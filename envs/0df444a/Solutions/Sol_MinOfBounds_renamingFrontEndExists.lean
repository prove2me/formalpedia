-- Prove2me | solution 1 for MinOfBounds.renamingFrontEndExists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:13:03.850011+00:00
-- url     : https://prove2.me/submissions/524700bc-603b-4df8-8ea9-c1fe14382c20

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Definitions.Def_VariableBound_Paper_Rename_Code
import Definitions.Def_WidthK_Decode
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.Dedup
import Definitions.Def_MinOfBounds_Rename
import Theorems.Thm_MinOfBounds_rencC_renames
import Theorems.Thm_VariableBound_Rename_rencC_polyT


set_option autoImplicit false
section
section
open MinOfBounds
open Groundwork Groundwork.Decode VariableBound.Rename MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution : RenamingFrontEndExists := ⟨rencC, rencC_polyT, rencC_renames⟩
end MinOfBounds
