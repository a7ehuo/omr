###############################################################################
# Copyright IBM Corp. and others 2015
#
# This program and the accompanying materials are made available under
# the terms of the Eclipse Public License 2.0 which accompanies this
# distribution and is available at https://www.eclipse.org/legal/epl-2.0/
# or the Apache License, Version 2.0 which accompanies this distribution and
# is available at https://www.apache.org/licenses/LICENSE-2.0.
#
# This Source Code may also be made available under the following
# Secondary Licenses when the conditions for such availability set
# forth in the Eclipse Public License, v. 2.0 are satisfied: GNU
# General Public License, version 2 with the GNU Classpath
# Exception [1] and GNU General Public License, version 2 with the
# OpenJDK Assembly Exception [2].
#
# [1] https://www.gnu.org/software/classpath/license.html
# [2] https://openjdk.org/legal/assembly-exception.html
#
# SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0-only WITH Classpath-exception-2.0 OR GPL-2.0-only WITH OpenJDK-assembly-exception-1.0
###############################################################################

# rules.aix.mk

define AR_COMMAND
$(AR) $(ARFLAGS) $(MODULE_ARFLAGS) $(GLOBAL_ARFLAGS) rcv $@ $(OBJECTS)
ranlib $@
endef

ifeq ($(OMR_ENV_DATA64),1)
  GLOBAL_ARFLAGS += -X64
  GLOBAL_ASFLAGS += -a64 -many
  GLOBAL_CPPFLAGS += -DPPC64

  ifeq (openxl,$(OMR_TOOLCHAIN))
    GLOBAL_CFLAGS += -s -m64
    GLOBAL_CXXFLAGS += -s -m64
  else
    GLOBAL_CFLAGS += -s -q64
    GLOBAL_CXXFLAGS += -s -q64
  endif
else
  GLOBAL_ARFLAGS += -X32
  GLOBAL_ASFLAGS += -a32 -mppc

  ifeq (openxl,$(OMR_TOOLCHAIN))
    GLOBAL_CXXFLAGS += -s -m32
    GLOBAL_CFLAGS += -s -m32
  else
    GLOBAL_CXXFLAGS += -s -q32
    GLOBAL_CFLAGS += -s -q32
  endif
endif

ifeq (openxl,$(OMR_TOOLCHAIN))
  GLOBAL_CFLAGS += -qarch=ppc -fno-strict-aliasing
  GLOBAL_CXXFLAGS+=-std=c++11 -qarch=ppc -fno-strict-aliasing
else
  GLOBAL_CFLAGS += -qarch=ppc -qalias=noansi -qxflag=LTOL:LTOL0 -qsuppress=1506-1108
  GLOBAL_CXXFLAGS+=-qlanglvl=extended0x -qarch=ppc -qalias=noansi -qxflag=LTOL:LTOL0 -qsuppress=1506-1108
endif
GLOBAL_CPPFLAGS+=-D_XOPEN_SOURCE_EXTENDED=1 -D_ALL_SOURCE -DRS6000 -DAIXPPC -D_LARGE_FILES

ifeq (openxl,$(OMR_TOOLCHAIN))
  # openxl options
  GLOBAL_CFLAGS+=-q mbcs -std=c89 -qinfo=pro
  GLOBAL_CFLAGS+=-std=c++11
else ifneq (,$(findstring xlclang,$(notdir $(CC))))
  # xlclang options
  GLOBAL_CFLAGS+=-qlanglvl=extended0x -qxlcompatmacros
else
  # xlc options
  GLOBAL_CFLAGS+=-q mbcs -qlanglvl=extended -qinfo=pro
endif

ifeq (openxl,$(OMR_TOOLCHAIN))
  # openxl options
  GLOBAL_CXXFLAGS+=-fno-exceptions
else ifneq (,$(findstring xlclang++,$(notdir $(CXX))))
  # xlclang++ options
  GLOBAL_CXXFLAGS+=-qxlcompatmacros -fno-exceptions
  ifeq (0,$(OMR_RTTI))
    GLOBAL_CXXFLAGS+=-fno-rtti
  endif
else
  # xlc++ options
  GLOBAL_CXXFLAGS+=-q mbcs -qinfo=pro
endif

ifdef I5_VERSION
  I5_FLAGS+=-g -qtbtable=full -qlist -qsource
  I5_DEFINES+=-DJ9OS_I5 -DJ9OS_$(I5_VERSION) -I$(top_srcdir)/../iseries -I$(top_srcdir)/../oti

  #Add IBM i specific compile options $(VMDEBUG)
  GLOBAL_CFLAGS+=$(I5_FLAGS) $(I5_DEFINES) $(VMDEBUG)
  GLOBAL_CXXFLAGS+=$(I5_FLAGS) $(I5_DEFINES) $(VMDEBUG)
  GLOBAL_CPPFLAGS+=$(I5_DEFINES) $(VMDEBUG)
endif

###
### Optimization
###

ifeq ($(OMR_OPTIMIZE),1)
  GLOBAL_CFLAGS+=-O3
  GLOBAL_CXXFLAGS+=-O3
else
  GLOBAL_CFLAGS+=-O0
  GLOBAL_CXXFLAGS+=-O0
endif

###
### Executable link flags
###
ifneq (,$(findstring executable,$(ARTIFACT_TYPE)))
  ifeq (1,$(OMR_ENV_DATA64))
    ifeq (openxl,$(OMR_TOOLCHAIN))
      GLOBAL_LDFLAGS+=-m64
    else
      GLOBAL_LDFLAGS+=-q64
    endif
  else
    GLOBAL_LDFLAGS+=-q32
  endif
  GLOBAL_LDFLAGS+=-brtl

  # If we are using ld directly to link, we must link in the c standard library.
  ifneq (,$(findstring cxx_,$(ARTIFACT_TYPE)))
    LINKTOOL:=$(CXXLINKEXE)
  else
    LINKTOOL:=$(CCLINKEXE)
  endif
  ifeq (ld,$(LINKTOOL))
    GLOBAL_LDFLAGS+=-lc_r -lC_r
  endif

  GLOBAL_LDFLAGS+=-lm -lpthread -liconv -ldl
endif

###
### Shared Library Flags
###
ifneq (,$(findstring shared,$(ARTIFACT_TYPE)))
  # Export file
  $(MODULE_NAME)_LINKER_EXPORT_SCRIPT := $(MODULE_NAME).exp

  define GENERATE_EXPORT_SCRIPT_COMMAND
    sh $(top_srcdir)/omrmakefiles/generate-exports.sh xlc $(MODULE_NAME) $(EXPORT_FUNCTIONS_FILE) $($(MODULE_NAME)_LINKER_EXPORT_SCRIPT)
  endef

  ifneq (,$(findstring cxx_,$(ARTIFACT_TYPE)))
    LINKTOOL:=$(CXXLINKSHARED)
  else
    LINKTOOL:=$(CCLINKSHARED)
  endif
  ifeq (ld,$(LINKTOOL))
    ifeq (1,$(OMR_ENV_DATA64))
      GLOBAL_LDFLAGS+=-b64
    else
      GLOBAL_LDFLAGS+=-b32
    endif
    GLOBAL_LDFLAGS+=-G -bnoentry -bernotok -bnolibpath
    GLOBAL_LDFLAGS+=-bmap:$(MODULE_NAME).map
    GLOBAL_LDFLAGS+=-bE:$($(MODULE_NAME)_LINKER_EXPORT_SCRIPT)
    GLOBAL_SHARED_LIBS+=c_r C_r m pthread
  else
    ifeq (1,$(OMR_ENV_DATA64))
      GLOBAL_LDFLAGS+=-X64
    else
      GLOBAL_LDFLAGS+=-X32
    endif
    GLOBAL_LDFLAGS+=-E $($(MODULE_NAME)_LINKER_EXPORT_SCRIPT)
    GLOBAL_LDFLAGS+=-p 0 -brtl -G -bernotok -bnoentry -Wl,-bnolibpath
    GLOBAL_SHARED_LIBS+=m
  endif

  # Add map files to clean target
  define CLEAN_COMMAND
    -$(RM) $(OBJECTS) $(MODULE_NAME).map
  endef

  # Shared library link command
  define LINK_C_SHARED_COMMAND
    -$(RM) $@
    $(CCLINKSHARED) -o $@ $(OBJECTS) $(LDFLAGS) $(MODULE_LDFLAGS) $(GLOBAL_LDFLAGS)
    cp -f $@ $(@:$(SOLIBEXT)=.debuginfo)
  endef

  define LINK_CXX_SHARED_COMMAND
    -$(RM) $@
    $(CXXLINKSHARED) -o $@ $(OBJECTS) $(LDFLAGS) $(MODULE_LDFLAGS) $(GLOBAL_LDFLAGS)
    cp -f $@ $(@:$(SOLIBEXT)=.debuginfo)
  endef
endif # ARTIFACT_TYPE contains "shared"

###
### Extra Flags
###

## Enhanced Warnings
ifeq ($(OMR_ENHANCED_WARNINGS),1)
endif

## Warnings as errors
ifeq ($(OMR_WARNINGS_AS_ERRORS),1)
  ifeq (openxl,$(OMR_TOOLCHAIN))
    GLOBAL_CFLAGS+=-Werror
    GLOBAL_CXXFLAGS+=-Werror
  else
    GLOBAL_CFLAGS+=-qhalt=w
    GLOBAL_CXXFLAGS+=-qhalt=w
  endif
endif

## Debug Information
ifeq (1,$(OMR_DEBUG))
  GLOBAL_CXXFLAGS+=-g
  GLOBAL_CFLAGS+=-g
endif
