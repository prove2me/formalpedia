-- Prove2me | solution 1 for Groundwork.Prog.Count.linkB_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:22:00.540892+00:00
-- url     : https://prove2.me/submissions/9ee5a5e8-90d3-4375-9a82-683b9253ad41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Theorems.Thm_Groundwork_Prog_Count_slotsOf_eq
import Theorems.Thm_Groundwork_Prog_Count_varAt_idx
import Theorems.Thm_Groundwork_Prog_Count_varAt_eq_none
import Theorems.Thm_Groundwork_Prog_Count_exists_idx
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
theorem _root_.solution (hm : φ.length ≤ g * μ) (p q : Slot g μ k) : linkB k φ (idx p) (idx q) = true ↔ Link φ p q := by
  simp only [linkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, slotsOf_eq, List.mem_range, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_iff_eq, beq_eq_false_iff_ne, varAt_idx, Option.isSome_iff_ne_none]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, h3, fun r hr1 hr2 hr3 => ?_⟩
    by_cases ht : idx r < φ.length * k
    · rcases h4 _ ht with (h | h) | h
      · exact h hr1
      · exact h hr2
      · rw [varAt_idx] at h; exact h hr3
    · rw [← varAt_idx, varAt_eq_none (Nat.zero_lt_of_lt p.2.2.2) (not_lt.1 ht)] at hr3
      exact h2 hr3.symm
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, fun t ht => ?_⟩
    obtain ⟨r, rfl⟩ := exists_idx (g := g) (μ := μ) (lt_of_lt_of_le ht (Nat.mul_le_mul_right k hm))
    by_cases hr1 : idx p < idx r
    · by_cases hr2 : idx r < idx q
      · right; rw [varAt_idx]; exact h4 r hr1 hr2
      · left; right; exact hr2
    · left; left; exact hr1
end Groundwork.Prog.Count
