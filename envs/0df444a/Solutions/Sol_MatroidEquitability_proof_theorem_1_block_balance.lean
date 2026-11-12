-- Prove2me | solution 1 for MatroidEquitability.proof_theorem_1_block_balance
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:07:48.266114+00:00
-- url     : https://prove2.me/submissions/fb37fd70-a878-425d-a093-2800bf6906f0

import Mathlib
import Definitions.Def_MatroidEquitability_setWeight
import Definitions.Def_MatroidEquitability_IsBlock
import Theorems.Thm_MatroidEquitability_theorem_2

section
namespace MatroidEquitability.Dev.BlockBalance

lemma setWeight_add_diff {α : Type*} (M : Matroid α) [M.Finite] (w : α → ℝ) {B : Set α}
    (hB : B ⊆ M.E) :
    setWeight w B + setWeight w (M.E \ B) = setWeight w M.E := by
  unfold setWeight
  rw [← finsum_mem_union Set.disjoint_sdiff_right (M.ground_finite.subset hB)
    (M.ground_finite.sdiff), Set.union_sdiff_cancel hB]

end MatroidEquitability.Dev.BlockBalance

namespace MatroidEquitability

open Dev.BlockBalance in
theorem chk_proof_theorem_1_block_balance {α : Type*} (M : Matroid α) [M.Finite] (w : α → ℝ)
    (hw : ∀ e ∈ M.E, 0 ≤ w e ∧ w e ≤ 1) (hM : ∃ B, IsBlock M B) :
    ∃ B, IsBlock M B ∧ |setWeight w B - setWeight w (M.E \ B)| ≤ 1 := by
  obtain ⟨B0, hB0⟩ := hM
  set m := setWeight w M.E / 2 with hm
  have hsub : ∀ B, IsBlock M B → B ⊆ M.E := fun B hB => hB.1.subset_ground
  have hcompl : ∀ B, IsBlock M B → IsBlock M (M.E \ B) := by
    intro B hB
    refine ⟨hB.2, ?_⟩
    rw [Set.sdiff_sdiff_cancel_left (hsub B hB)]
    exact hB.1
  have hadd := fun B (hB : IsBlock M B) => setWeight_add_diff M w (hsub B hB)
  let S : Set (Set α) := {B | IsBlock M B ∧ m ≤ setWeight w B}
  have hSfin : S.Finite := M.ground_finite.finite_subsets.subset fun B hB => hsub B hB.1
  have hSne : S.Nonempty := by
    by_cases h : m ≤ setWeight w B0
    · exact ⟨B0, hB0, h⟩
    · refine ⟨M.E \ B0, hcompl B0 hB0, ?_⟩
      have := hadd B0 hB0
      rw [hm] at h ⊢
      linarith
  obtain ⟨D, ⟨hD, hmD⟩, hmin⟩ := Set.exists_min_image S (setWeight w) hSfin hSne
  have hDE := hadd D hD
  have hCblock := hcompl D hD
  refine ⟨D, hD, ?_⟩
  rcases eq_or_lt_of_le (show setWeight w (M.E \ D) ≤ setWeight w D by
      rw [hm] at hmD; linarith) with heq | hlt
  · rw [abs_le]; constructor <;> linarith
  · have h2 := theorem_2 M w hw (M.E \ D) D hCblock hD hlt (by
      rintro C hC ⟨h1, h2⟩
      by_cases hc : m ≤ setWeight w C
      · have := hmin C ⟨hC, hc⟩
        linarith
      · have hc' : m ≤ setWeight w (M.E \ C) := by
          have := hadd C hC
          rw [hm] at hc ⊢
          linarith
        have := hmin _ ⟨hcompl C hC, hc'⟩
        have := hadd C hC
        linarith)
    rw [abs_le]; constructor <;> linarith

end MatroidEquitability
end

theorem solution : type_of% @MatroidEquitability.chk_proof_theorem_1_block_balance := @MatroidEquitability.chk_proof_theorem_1_block_balance
