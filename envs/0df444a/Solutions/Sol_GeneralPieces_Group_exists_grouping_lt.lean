-- Prove2me | solution 1 for GeneralPieces.Group.exists_grouping_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:18:14.295348+00:00
-- url     : https://prove2.me/submissions/31650d58-b496-43fe-8525-9e152c8c2004

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Group_CaseI
import Definitions.Def_GeneralPieces_Group_CaseII
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_Col_CertG
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_GeneralPieces_Group_Lemma
import Theorems.Thm_GeneralPieces_caseI
import Theorems.Thm_GeneralPieces_stCaseII
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Group
open Finset Groundwork
namespace GeneralPieces.Group
theorem _root_.solution (K g : ℕ) (ζ : ℝ) (P : ℕ) (c : Fin g → Fin g → ℕ) (hK : 2 ≤ K) (hg : 2 ≤ g) (hζ0 : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hs : ∀ a b, c a b = c b a) (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) (h : AppRunningTime.Cases K g ζ P c) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → ∑ a with χ a = γ, ∑ b with χ b = γ', c a b ≤ AppRunningTime.Lof K g ζ P (∑ a, ∑ b ∈ univ.erase a, c a b) := by
  have key : ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' → (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) ≤
        ((∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + 2 * ζ * g * P) / (K : ℝ) ^ 2 := by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact caseI K g c P ζ hK h1 h2 hs fun a => by exact_mod_cast hP a
    · rcases Nat.eq_zero_or_pos P with rfl | hP1
      · have hc0 : ∀ a b, a ≠ b → c a b = 0 := fun a b hab =>
          Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 (hP a)) b (Finset.mem_erase.2 ⟨hab.symm, mem_univ b⟩)
        have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
        obtain ⟨χ, a1, -⟩ := stCaseII K g c 1 ζ hK hg h1 hζ0 hζ1 one_pos
          (fun a => by
            rw [Finset.sum_eq_zero fun b hb => by rw [hc0 a b (Finset.ne_of_mem_erase hb).symm, Nat.cast_zero]]
            exact zero_le_one)
          (fun a b hab => by rw [hc0 a b hab, Nat.cast_zero]; positivity) h3
        refine ⟨χ, fun γ => by rw [a1, Nat.mul_div_cancel' h1]; omega, fun γ γ' hne => ?_⟩
        rw [Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => by
          have hab : a ≠ b := fun e => hne (by rw [← (Finset.mem_filter.1 ha).2, ← (Finset.mem_filter.1 hb).2, e])
          rw [hc0 a b hab, Nat.cast_zero]]
        positivity
      · obtain ⟨χ, a1, a2⟩ := stCaseII K g c P ζ hK hg h1 hζ0 hζ1 (by exact_mod_cast hP1) (fun a => by exact_mod_cast hP a) h2 h3
        refine ⟨χ, fun γ => ?_, fun γ γ' hne => (a2 γ γ' hne).le⟩
        rw [a1, Nat.mul_div_cancel' h1]
        omega
  obtain ⟨χ, a1, a2⟩ := key
  refine ⟨χ, a1, fun γ γ' hne => ?_⟩
  have := (a2 γ γ' hne).trans (Nat.le_ceil _)
  unfold AppRunningTime.Lof
  push_cast
  exact_mod_cast this
end GeneralPieces.Group
