-- Prove2me | solution 1 for MinOfBounds.numOcc_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:54:44.956952+00:00
-- url     : https://prove2.me/submissions/0b8871ac-d048-4cec-886c-b0ca8d48c806

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
import Theorems.Thm_MinOfBounds_length_literals_le
import Theorems.Thm_Groundwork_DecodeK_IsKCNF_length_le
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Sat3_Is3CNF_length_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open MinOfBounds
open Groundwork Groundwork.Decode VariableBound.Rename MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution {k V : ℕ} (φ : CNF V) (h : ∀ C ∈ φ, C.length ≤ k) : numOcc φ ≤ φ.length * k := by
  have h1 : ∀ C ∈ toN φ, C.length ≤ k := fun C hC => by
    obtain ⟨C', hC', rfl⟩ := List.mem_map.1 hC
    rw [List.length_map]
    exact h C' hC'
  have h2 : (toN φ).length = φ.length := List.length_map _
  rw [← length_occL, ← h2]
  exact (List.dedup_sublist _).length_le.trans (length_literals_le _ h1)
end MinOfBounds
