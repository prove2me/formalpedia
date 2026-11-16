-- Prove2me | solution 1 for Kyprianou.Ch01.brownianRealExpMoment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T14:51:02.666349+00:00
-- url     : https://prove2.me/submissions/67b835d4-8cc6-4e62-b961-c1e15cd2b81a

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Gaussian marginal law derived from the Brownian characteristic exponent. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma theta : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t))
    (t : ℝ≥0) :
    Integrable (fun ω => Real.exp (theta * X t ω)) P ∧
      (∫ ω, Real.exp (theta * X t ω) ∂P) =
        Real.exp ((sigma ^ 2 * theta ^ 2 / 2 + gamma * theta) * (t : ℝ)) := by
  let v : ℝ≥0 :=
    ⟨sigma ^ 2 * (t : ℝ), mul_nonneg (sq_nonneg sigma) (NNReal.coe_nonneg t)⟩
  have hLaw : P.map (X t) = gaussianReal (gamma * (t : ℝ)) v := by
    apply Measure.ext_of_charFun
    funext ξ
    rw [hX.2.2 t ξ, charFun_gaussianReal]
    congr 1
    have hv : (v : ℂ) = ((sigma ^ 2 * (t : ℝ) : ℝ) : ℂ) := by rfl
    rw [hv]
    push_cast
    ring
  have hInt : Integrable (fun ω => Real.exp (theta * X t ω)) P := by
    have hi := integrable_exp_mul_gaussianReal
      (μ := gamma * (t : ℝ)) (v := v) theta
    rw [← hLaw] at hi
    simpa only [Function.comp_def] using
      hi.comp_measurable (hMeas t)
  refine ⟨hInt, ?_⟩
  change mgf (X t) P theta =
    Real.exp ((sigma ^ 2 * theta ^ 2 / 2 + gamma * theta) * (t : ℝ))
  rw [mgf_gaussianReal hLaw theta]
  congr 1
  have hv : (v : ℝ) = sigma ^ 2 * (t : ℝ) := by rfl
  rw [hv]
  ring
