-- Prove2me | solution 1 for MohriFoML.OnlineToBatch.hoeffding_lemma
-- status  : ACCEPTED   (prove)
-- author  : @ShouqiaoWang
-- created : 2026-10-30T12:42:44.468927+00:00
-- url     : https://prove2.me/submissions/2b8bc164-aa4c-44f9-968b-1e046b0657eb

import Mathlib.Probability.Moments.SubGaussian
open MeasureTheory
theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (a b : ℝ) (hX : Measurable X)
    (hmean : ∫ ω, X ω ∂μ = 0) (hab : a < b) (hXab : ∀ ω, a ≤ X ω ∧ X ω ≤ b) :
    ∀ t : ℝ, 0 < t →
      ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  intro t ht
  have h := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero
    hX.aemeasurable (Filter.Eventually.of_forall hXab) hmean ht
  refine h.trans_eq ?_
  congr 1
  rw [coe_nnnorm, Real.norm_of_nonneg (sub_nonneg.mpr hab.le)]
  ring
