-- Prove2me | solution 1 for MinimaxSLP.ObjSDP.recourseSet_bounded
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:48:18.621409+00:00
-- url     : https://prove2.me/submissions/c8349a6c-3626-49a8-8d53-680873f7cb6f

import Mathlib
import Definitions.Def_MomentDRO_Conf_Setting
import Definitions.Def_MinimaxSLP_ObjSDP_Model

open MeasureTheory Matrix

open MinimaxSLP.ObjSDP in
theorem solution {n r d : ℕ}
    (W : Matrix (Fin r) (Fin d) ℝ) (T : Matrix (Fin r) (Fin n) ℝ) (h : Fin r → ℝ)
    (hA3 : ∀ q : Fin d → ℝ, ∃ π : Fin r → ℝ, Wᵀ *ᵥ π ≤ q) (x : Fin n → ℝ) :
    Bornology.IsBounded (recourseSet W T h x) ∧ Convex ℝ (recourseSet W T h x) := by
  constructor
  · obtain ⟨π, hπ⟩ := hA3 (-1)
    set C := -(π ⬝ᵥ (h - T *ᵥ x)) with hC
    have key : ∀ w ∈ recourseSet W T h x, ∀ i, w i ≤ C := by
      rintro w ⟨hw, hw0⟩ i
      have hsum : ∑ j, w j ≤ ∑ j, -(Wᵀ *ᵥ π) j * w j := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 : (Wᵀ *ᵥ π) j ≤ -1 := hπ j
        have h2 : 0 ≤ w j := hw0 j
        nlinarith
      have hid : ∑ j, -(Wᵀ *ᵥ π) j * w j = C := by
        rw [hC, ← hw]
        have : (Wᵀ *ᵥ π) ⬝ᵥ w = π ⬝ᵥ (W *ᵥ w) := by
          rw [mulVec_transpose, dotProduct_mulVec]
        rw [← this]
        simp [dotProduct, Finset.sum_neg_distrib]
      have hi : w i ≤ ∑ j, w j :=
        Finset.single_le_sum (f := w) (fun j _ => hw0 j) (Finset.mem_univ i)
      linarith
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨|C|, fun w hw => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (abs_nonneg C)).mpr fun i => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hw.2 i)]
    exact (key w hw i).trans (le_abs_self C)
  · rintro w1 ⟨hw1, hw10⟩ w2 ⟨hw2, hw20⟩ a b ha hb hab
    refine ⟨?_, ?_⟩
    · rw [mulVec_add, mulVec_smul, mulVec_smul, hw1, hw2, ← add_smul, hab, one_smul]
    · exact add_nonneg (smul_nonneg ha hw10) (smul_nonneg hb hw20)
