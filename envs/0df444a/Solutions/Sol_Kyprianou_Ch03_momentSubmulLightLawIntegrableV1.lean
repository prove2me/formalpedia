-- Prove2me | solution 1 for Kyprianou.Ch03.momentSubmulLightLawIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:31:59.240828+00:00
-- url     : https://prove2.me/submissions/e9f01648-8b9a-4fa4-a15c-3525aa7e303a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_exercise33SubmultiplicativeExponentialEnvelope
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (nu : Measure Real) [IsProbabilityMeasure nu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g)
    (hg_bounded : ∀ R : Real, 0 ≤ R →
      ∃ M : Real, ∀ x : Real, |x| ≤ R → g x ≤ M)
    (hnu : ∀ b : Real, 0 < b → Integrable (fun x : Real => Real.exp (b * |x|)) nu) :
    Integrable g nu := by
  obtain ⟨a, b, ha, hb, hbound⟩ :=
    Kyprianou.Ch03.exercise33SubmultiplicativeExponentialEnvelope g hg hg_bounded
  have h := (hnu b hb).const_mul a
  apply h.mono hg_meas.aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hg.1 x),
    abs_of_nonneg (mul_nonneg ha.le (Real.exp_pos _).le)] using hbound x
