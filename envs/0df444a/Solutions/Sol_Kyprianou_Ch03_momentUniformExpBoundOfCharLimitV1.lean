-- Prove2me | solution 1 for Kyprianou.Ch03.momentUniformExpBoundOfCharLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T13:02:43.893877+00:00
-- url     : https://prove2.me/submissions/f8ee4e18-ab83-4266-88f2-a02adf100bb2

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_FamousTheorems_levy_continuity
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (q : ℕ → ProbabilityMeasure Real) (nu : ProbabilityMeasure Real)
    (hchar : ∀ xi : Real, Tendsto (fun n => charFun (q n : Measure Real) xi) atTop
      (𝓝 (charFun (nu : Measure Real) xi)))
    (b : Real) (C : ENNReal) (hC : C < ⊤)
    (hbound : ∀ n, (∫⁻ x, ENNReal.ofReal (Real.exp (b * x)) ∂(q n : Measure Real)) ≤ C) :
    Integrable (fun x : Real => Real.exp (b * x)) (nu : Measure Real) := by
  have hw : Tendsto q atTop (𝓝 nu) := FamousTheorems.levy_continuity.mpr hchar
  have hh := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (f := fun x : ℝ => Real.exp (b * x)) (μ := (nu : Measure ℝ))
    (μs := fun n => (q n : Measure ℝ)) (by fun_prop)
    (fun x => (Real.exp_pos _).le)
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hw hG)
  have hlim : Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (Real.exp (b * x)) ∂(q n : Measure ℝ)) atTop ≤ C :=
    Filter.liminf_le_of_frequently_le (Frequently.of_forall hbound)
  exact ⟨(by fun_prop), (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall (fun x : ℝ => (Real.exp_pos (b * x)).le))).mpr
      (lt_of_le_of_lt (hh.trans hlim) hC)⟩
