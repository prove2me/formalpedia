-- Prove2me | solution 1 for Kyprianou.Ch01.brownianUpperStoppedExponentialPointwiseLimitPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:26:48.58788+00:00
-- url     : https://prove2.me/submissions/408de7b2-bf35-4526-af34-ea5b07d262aa

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Theorems.Thm_Kyprianou_Ch01_brownianAdjustmentRoot
import Theorems.Thm_Kyprianou_Ch01_passageLaplaceNormBoundNonnegativeDiscountPublic
import Theorems.Thm_Kyprianou_Ch01_brownianUpperPassageLaplaceAEStrongMeasurablePublic
import Theorems.Thm_Kyprianou_Ch01_continuousUpperPassageDiscountedExpLimitPublic
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Brownian a.s. continuous paths and the measurable bounded payoff imply the passage limit. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let theta : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    let F : ℕ → Ω → ℝ := fun N ω =>
      let T : ℝ≥0 := N
      let tauT : ℝ≥0 :=
        match firstUpperPassage X x ω with
        | none => T
        | some t => min t T
      Real.exp (theta * X tauT ω - q * (tauT : ℝ))
    Integrable (passageLaplace (firstUpperPassage X x) q) P ∧
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => F N ω) atTop
      (nhds (Real.exp (theta * x) *
        passageLaplace (firstUpperPassage X x) q ω)) := by
  intro theta F
  have htheta : 0 ≤ theta :=
    (brownianAdjustmentRoot sigma gamma q hsigma hq).1.le
  have hAES : AEStronglyMeasurable
      (passageLaplace (firstUpperPassage X x) q) P :=
    brownianUpperPassageLaplaceAEStrongMeasurablePublic
      P X sigma gamma q x hsigma hq hx hX hMeas
  have hInt : Integrable (passageLaplace (firstUpperPassage X x) q) P :=
    (integrable_const (1 : ℝ)).mono' hAES
      (Filter.Eventually.of_forall fun ω =>
        passageLaplaceNormBoundNonnegativeDiscountPublic
          (firstUpperPassage X x) q hq.le ω)
  refine ⟨hInt, ?_⟩
  have hZero (ω : Ω) : X 0 ω = 0 := congrFun hX.1.start_zero ω
  filter_upwards [hX.2.1] with ω hcont
  exact
    (continuousUpperPassageDiscountedExpLimitPublic
       X ω x theta q hx htheta hq hcont (hZero ω))
