-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_scalar_product
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T02:43:52.248988+00:00
-- url     : https://prove2.me/submissions/8bdeea0d-8b55-46d6-bc88-a97cdac4ab2a

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_factor_bounds_choiceScalar

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (f : ChoiceFamily d H) :
    ‖∏ r : Row d H, choiceScalar d r (f r)‖ ≤
      Real.exp (-nu * ((∑ r : Row d H, translatedIndexWeight d (f r).1) -
        (actualRowCount d H : ℝ) * H * actualMean d H) +
        (actualRowCount d H : ℝ) * H * d.translationError) := by
  classical
  have hrow :
      (∑ r : Row d H, ∑ i : Fin d.m,
        (r.2.1 i.succ : ℝ) * MatrixArithmetic.logWeights (finiteDenominators d) i) =
      (actualRowCount d H : ℝ) * H * actualMean d H := by
    change MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
        (finiteDenominators d) H =
      (actualRowCount d H : ℝ) * H *
        (MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
          (finiteDenominators d) H / ((actualRowCount d H : ℝ) * H))
    by_cases hc : actualRowCount d H = 0
    · haveI : IsEmpty (Row d H) := Fintype.card_eq_zero_iff.mp hc
      simp [MatrixArithmetic.rowWeightedSum, hc]
    · have hden : (actualRowCount d H : ℝ) * H ≠ 0 :=
        mul_ne_zero (by exact_mod_cast hc) hH.ne'
      exact (mul_div_cancel₀ _ hden).symm
  rw [norm_prod]
  calc
    (∏ r : Row d H, ‖choiceScalar d r (f r)‖) ≤
        ∏ r : Row d H,
          Real.exp (-nu * (translatedIndexWeight d (f r).1 -
            (∑ i : Fin d.m, (r.2.1 i.succ : ℝ) *
              MatrixArithmetic.logWeights (finiteDenominators d) i)) +
            H * d.translationError) := by
      apply Finset.prod_le_prod
      · intro r hr
        exact norm_nonneg _
      · intro r hr
        exact OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_choiceScalar
          d hnu hH r (f r)
    _ = Real.exp (∑ r : Row d H,
          (-nu * (translatedIndexWeight d (f r).1 -
            (∑ i : Fin d.m, (r.2.1 i.succ : ℝ) *
              MatrixArithmetic.logWeights (finiteDenominators d) i)) +
            H * d.translationError)) := by rw [← Real.exp_sum]
    _ = Real.exp (-nu * ((∑ r : Row d H, translatedIndexWeight d (f r).1) -
          (actualRowCount d H : ℝ) * H * actualMean d H) +
          (actualRowCount d H : ℝ) * H * d.translationError) := by
      congr 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hrow]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, actualRowCount]
      ring
