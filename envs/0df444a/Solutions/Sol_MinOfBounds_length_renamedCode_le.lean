-- Prove2me | solution 1 for MinOfBounds.length_renamedCode_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:08:40.497018+00:00
-- url     : https://prove2.me/submissions/3266fc64-7288-43bc-9e40-e653e5a59d1a

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
import Theorems.Thm_MinOfBounds_numOcc_le_mul
import Theorems.Thm_Groundwork_DecodeK_length_enc
import Theorems.Thm_Groundwork_Decode_length_enc
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_VariableBound_Rename_lengthEncC
import Theorems.Thm_VariableBound_Rename_length_ren
import Theorems.Thm_VariableBound_Rename_numOcc_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open MinOfBounds
open Groundwork Groundwork.Decode VariableBound.Rename MainTheoremForms
open Sat3 (CNF)
namespace MinOfBounds
theorem _root_.solution {k V : ℕ} (φ : CNF V) (h : ∀ C ∈ φ, C.length ≤ k) : (renamedCode k φ).length ≤ 2 * (encC k φ).length := by
  have h1 := numOcc_le_mul φ h
  have h2 : Nat.log2 (2 * numOcc φ) ≤ Nat.log2 (2 * V) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (Nat.mul_le_mul_left _ (numOcc_le φ))
  have h3 : φ.length * (k * (Nat.log2 (2 * numOcc φ) + 1)) ≤ φ.length * (k * (Nat.log2 (2 * V) + 1)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.succ_le_succ h2))
  have h4 : φ.length * k ≤ φ.length * (k * (Nat.log2 (2 * V) + 1)) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  rw [renamedCode_eq, lengthEncC, SatM.enc, List.length_append, List.length_replicate, List.length_cons, DecodeK.length_enc, length_ren]
  omega
end MinOfBounds
