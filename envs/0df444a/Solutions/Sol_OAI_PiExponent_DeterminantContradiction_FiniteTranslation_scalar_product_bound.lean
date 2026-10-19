-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.scalar_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:30:12.990544+00:00
-- url     : https://prove2.me/submissions/58ebe4b6-1019-415d-ad93-1fa73668da8c

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_scalar_bound_each_row
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_sum_row_weights_eq_mean

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (f : Family d H) :
    ‖∏ r : Row d H, scalar d r (f r)‖ ≤
      Real.exp (-nu * ((∑ r : Row d H, weight d (f r).1) -
        (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) := by
  classical
  rw [norm_prod]
  calc
    (∏ r : Row d H, ‖scalar d r (f r)‖) ≤
        ∏ r : Row d H,
          Real.exp (-nu * (weight d (f r).1 -
            ∑ i : Fin d.m,
              MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) +
            H * d.translationError) := by
      apply Finset.prod_le_prod
      · intro r hr
        exact norm_nonneg _
      · intro r hr
        exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.scalar_bound_each_row
          d hnu (H := H) hH r (f r)
    _ = Real.exp (∑ r : Row d H,
          (-nu * (weight d (f r).1 -
            ∑ i : Fin d.m,
              MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) +
            H * d.translationError)) := by rw [← Real.exp_sum]
    _ = Real.exp (-nu * ((∑ r : Row d H, weight d (f r).1) -
          (actualRowCount d H : ℝ) * H * actualMean d H) +
          (actualRowCount d H : ℝ) * H * d.translationError) := by
      congr 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        OAI.PiExponent.DeterminantContradiction.FiniteTranslation.sum_row_weights_eq_mean d hH]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
      ring