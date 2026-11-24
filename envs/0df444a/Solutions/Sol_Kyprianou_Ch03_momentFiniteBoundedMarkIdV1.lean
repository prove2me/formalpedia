-- Prove2me | solution 1 for Kyprianou.Ch03.momentFiniteBoundedMarkIdV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:45:27.02799+00:00
-- url     : https://prove2.me/submissions/4aa5bc5e-6d97-4c4a-bb5b-6dd846767c72

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (nu : Measure Real) [IsFiniteMeasure nu]
    (hnu : ∀ᵐ x ∂nu, |x| < 1) :
    Integrable (fun x : Real => x) nu := by
  apply (integrable_const (1 : ℝ)).mono (by fun_prop)
  filter_upwards [hnu] with x hx
  simpa [Real.norm_eq_abs] using hx.le
