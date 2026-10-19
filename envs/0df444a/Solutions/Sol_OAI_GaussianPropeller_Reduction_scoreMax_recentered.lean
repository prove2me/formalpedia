-- Prove2me | solution 1 for OAI.GaussianPropeller.Reduction.scoreMax_recentered
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:11:46.506463+00:00
-- url     : https://prove2.me/submissions/38ef5171-d4cf-4d64-a23c-f48cbf4058af

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]


theorem solution (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) (x : Space d) :
    scoreMax (recentered z i).ofLp x = omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
  classical
  have hk1 : (1:ℝ) < k := by exact_mod_cast hk
  have hk0 : (0:ℝ) < (k:ℝ) - 1 := by linarith
  have hr : ∀ j, (recentered z i).ofLp j = if j = i then 0 else z j + ((k:ℝ)-1)⁻¹ • z i := fun j => rfl
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    rw [hr]
    by_cases hj : j = i
    · rw [if_pos hj, inner_zero_left]
      have hs : ∑ j ∈ Finset.univ.erase i, ⟪z j, x⟫ = - ⟪z i, x⟫ := by
        rw [← sum_inner]
        have : ∑ j ∈ Finset.univ.erase i, z j = - z i := by
          rw [eq_neg_iff_add_eq_zero, add_comm, Finset.add_sum_erase _ _ (Finset.mem_univ i), hz]
        rw [this, inner_neg_left]
      have hle := Finset.sum_le_card_nsmul (Finset.univ.erase i) (fun j => ⟪z j, x⟫)
        (omittedMax hk z i x) (fun j hj => Finset.le_sup' (fun j => ⟪z j,x⟫) hj)
      rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one] at hle
      rw [inner_smul_left]
      simp only [RCLike.conj_to_real]
      have : -(((k:ℝ)-1)⁻¹ * ⟪z i, x⟫) ≤ omittedMax hk z i x := by
        rw [← mul_neg, inv_mul_le_iff₀ hk0]; linarith
      linarith
    · rw [if_neg hj, inner_add_left]
      have := Finset.le_sup' (fun j => ⟪z j,x⟫) (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      change ⟪z j, x⟫ ≤ omittedMax hk z i x at this
      linarith
  · have : omittedMax hk z i x ≤ scoreMax (recentered z i).ofLp x - ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by
      apply Finset.sup'_le
      intro j hj
      have := Finset.le_sup' (fun j => ⟪(recentered z i).ofLp j, x⟫) (Finset.mem_univ j)
      change ⟪(recentered z i).ofLp j, x⟫ ≤ scoreMax (recentered z i).ofLp x at this
      rw [hr, if_neg (Finset.ne_of_mem_erase hj), inner_add_left] at this
      linarith
    linarith

