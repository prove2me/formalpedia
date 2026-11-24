-- Prove2me | solution 1 for Kyprianou.Ch03.momentFourierCharacterIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:44:53.87366+00:00
-- url     : https://prove2.me/submissions/e1ab1c56-4141-424c-9c46-7f6c40eb55ef

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real) [IsFiniteMeasure mu] (xi : Real) :
    Integrable (fun x : Real => Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I)) mu := by
  apply (integrable_const (1 : ℝ)).mono (by fun_prop)
  filter_upwards [] with x
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
