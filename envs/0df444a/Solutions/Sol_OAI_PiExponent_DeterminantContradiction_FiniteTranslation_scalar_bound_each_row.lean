-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.scalar_bound_each_row
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:13:28.146398+00:00
-- url     : https://prove2.me/submissions/98b2c4d8-dad9-466d-ae80-848194c58eca

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_center_product_estimate_of_tail_support
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_tail_support_and_prefactor_estimate
import Mathlib.Tactic.Ring

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖scalar d r t‖ ≤ Real.exp
      (-nu * (weight d t.1 -
        ∑ i : Fin d.m,
          MatrixArithmetic.logWeights (finiteDenominators d) i * (r.2.1 i.succ : ℝ)) +
        H * d.translationError) := by
  let P : ℂ :=
    ((∏ i : Fin d.m, (t.1.1 i).choose (r.2.1 i.succ) *
      (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ)
  let C : ℂ :=
    ∏ i : Fin d.m,
      (((r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d)
          (finiteDenominators d) i - 2 * (Real.pi : ℂ) * Complex.I)) ^
            (t.1.1 i - r.2.1 i.succ - t.2.1 i))
  let L : ℂ :=
    PowerSeries.coeff (t.2.2 : ℕ)
      (∏ i : Fin d.m,
        ((PowerSeries.trunc
          (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
          (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
            (t.2.1 i : ℕ))
  have hfac : scalar d r t = P * C * L := by rfl
  by_cases hL : L = 0
  · rw [hfac, hL, mul_zero, norm_zero]
    exact Real.exp_nonneg _
  have htail := translation_tail_support_and_prefactor_estimate d hnu hH r t hL
  have hcenter := center_product_estimate_of_tail_support d hnu hH r t htail.1
  have htailnorm := htail.2
  change ‖C‖ ≤ _ at hcenter
  change ‖P * L‖ ≤ _ at htailnorm
  rw [hfac]
  calc
    ‖P * C * L‖ = ‖P * L‖ * ‖C‖ := by
      rw [show P * C * L = (P * L) * C by ring, norm_mul]
    _ ≤ Real.exp (H * (Real.log 4 / d.wstar + Real.log 2 / (d.v0 : ℝ))) *
        Real.exp (-nu * (weight d t.1 -
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ)) +
          H * (nu / d.F0 + (Real.log (2 * (d.K : ℝ)) + nu) / d.wstar)) :=
        mul_le_mul htailnorm hcenter (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp
        (-nu * (weight d t.1 -
          ∑ i : Fin d.m,
            MatrixArithmetic.logWeights (finiteDenominators d) i *
              (r.2.1 i.succ : ℝ)) + H * d.translationError) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [AdmissibleParameters.translationError]
        ring
