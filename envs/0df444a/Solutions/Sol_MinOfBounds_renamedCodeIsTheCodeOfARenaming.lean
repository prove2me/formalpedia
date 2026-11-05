-- Prove2me | solution 1 for MinOfBounds.renamedCodeIsTheCodeOfARenaming
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:32.120208+00:00
-- url     : https://prove2.me/submissions/605a31e3-93c7-4efe-8559-a42fc4d77e24

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
import Theorems.Thm_MinOfBounds_renamedCode_eq
import Theorems.Thm_VariableBound_Rename_allOccur_ren
import Theorems.Thm_VariableBound_Rename_isKCNF_ren
import Theorems.Thm_VariableBound_Rename_length_ren
import Theorems.Thm_VariableBound_Rename_numSat_ren
import Theorems.Thm_VariableBound_Rename_toN_ren


set_option autoImplicit false
section
section
open MinOfBounds
open Groundwork Groundwork.Decode VariableBound.Rename MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution : RenamedCodeIsTheCodeOfARenaming := fun k _ φ =>
  ⟨ren φ, renamedCode_eq k φ, toN_ren φ, nodup_occL _, fun _ => ⟨exists_of_mem_occL φ, fun ⟨_, hi, ho⟩ => hi ▸ (val_mem_occL φ).2 ho⟩,
    length_ren φ, isKCNF_ren φ, allOccur_ren φ, numSat_ren φ⟩
end MinOfBounds
