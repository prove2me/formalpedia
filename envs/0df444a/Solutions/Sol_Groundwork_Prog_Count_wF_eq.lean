-- Prove2me | solution 1 for Groundwork.Prog.Count.wF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:24:59.163508+00:00
-- url     : https://prove2.me/submissions/82bf91b7-83e9-41bf-a9a0-e2e38f47672b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_locals_eq
import Theorems.Thm_Groundwork_Prog_Count_rows_eq
import Theorems.Thm_Groundwork_Prog_Count_loc_lt
import Theorems.Thm_Groundwork_Prog_Count_exists_loc
import Theorems.Thm_Groundwork_Prog_Count_idx_eq
import Theorems.Thm_Groundwork_Prog_Count_litAt_idx
import Theorems.Thm_Groundwork_Prog_Count_all_links_iff
import Theorems.Thm_Groundwork_Prog_Count_boole_congr
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
import Theorems.Thm_Groundwork_size_bool
import Theorems.Thm_Groundwork_size_inl
import Theorems.Thm_Groundwork_size_inr
import Theorems.Thm_Groundwork_size_int
import Theorems.Thm_Groundwork_size_list
import Theorems.Thm_Groundwork_size_nat
import Theorems.Thm_Groundwork_size_none
import Theorems.Thm_Groundwork_size_prod
import Theorems.Thm_Groundwork_size_some
import Theorems.Thm_Groundwork_size_unit
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words
attribute [local simp] Groundwork.size_bool
attribute [local simp] Groundwork.size_inl
attribute [local simp] Groundwork.size_inr
attribute [local simp] Groundwork.size_int
attribute [local simp] Groundwork.size_list
attribute [local simp] Groundwork.size_nat
attribute [local simp] Groundwork.size_none
attribute [local simp] Groundwork.size_prod
attribute [local simp] Groundwork.size_some
attribute [local simp] Groundwork.size_unit



set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}
namespace Groundwork.Prog.Count
theorem _root_.solution (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) (a : Fin g) (z : List Bool) :
    wF g k (φ, (a.val, z)) = weight φ a (bits (μ := mu g φ) (k := k) z) := by
  unfold wF weight
  refine boole_congr ?_
  simp only [Bool.and_eq_true, and_assoc]
  refine and_congr ?_ (and_congr ?_ ?_)
  · simp only [List.all_eq_true, locals_eq hg, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
    constructor
    · intro h s hs
      rcases h _ (loc_lt s) with h' | h'
      · rw [← idx_eq, litAt_idx, hs] at h'; simp at h'
      · exact h'
    · intro h r hr
      obtain ⟨s, rfl⟩ := exists_loc hr
      rw [← idx_eq, litAt_idx]
      cases hs : lit φ (a, s) with
      | none => right; exact h s hs
      | some l => left; rfl
  · simp only [List.all_eq_true, rows_eq hg, List.mem_range, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      List.any_eq_true, beq_iff_eq]
    constructor
    · intro h c hc
      rcases h _ c.2 with h' | ⟨j, hj, h'⟩
      · exact absurd hc h'
      · refine ⟨⟨j, hj⟩, ?_⟩
        rw [← litAt_idx]
        exact h'
    · intro h c hc
      by_cases hlt : a.val * mu g φ + c < φ.length
      · obtain ⟨j, hj⟩ := h ⟨c, hc⟩ hlt
        rw [← litAt_idx] at hj
        exact Or.inr ⟨j.val, j.2, hj⟩
      · exact Or.inl hlt
  · rw [all_links_iff hg hm a a fun r r' => z.getD r false == z.getD r' false]
    simp only [beq_iff_eq, bits]
end Groundwork.Prog.Count
