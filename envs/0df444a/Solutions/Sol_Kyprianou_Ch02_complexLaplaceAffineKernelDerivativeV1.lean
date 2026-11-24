-- Prove2me | solution 1 for Kyprianou.Ch02.complexLaplaceAffineKernelDerivativeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:12:05.215942+00:00
-- url     : https://prove2.me/submissions/562fab71-a01b-4c0a-af5c-a4ad034aba40

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution
    (a b z : ℂ) (x : ℝ) :
    HasDerivAt (fun w : ℂ => a + b * Complex.exp (-w * (x : ℂ)))
      (b * (-(x : ℂ)) * Complex.exp (-z * (x : ℂ))) z := by
  have h := ((((hasDerivAt_id z).neg.mul_const (x : ℂ)).cexp).const_mul b).const_add a
  have he : b * (-(x : ℂ)) * Complex.exp (-z * (x : ℂ)) =
      b * (Complex.exp (-z * (x : ℂ)) * (-1 * (x : ℂ))) := by ring
  rw [he]
  exact h
