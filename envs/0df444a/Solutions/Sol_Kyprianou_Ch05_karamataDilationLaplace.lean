-- Prove2me | solution 1 for Kyprianou.Ch05.karamataDilationLaplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:44:42.240539+00:00
-- url     : https://prove2.me/submissions/3c3e2ea3-4f3f-4d10-b7f0-29a75daa7dc0

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Positive measure dilation gives the rescaled Laplace transform. -/
theorem solution
    (U : Measure Real) (x c t : Real) (hx : 0 < x) :
    positiveLaplace ((ENNReal.ofReal c) •
      (Measure.map (fun z : Real => z/x) U)) t =
      ENNReal.ofReal c * positiveLaplace U (t/x) := by
  unfold positiveLaplace
  rw [lintegral_smul_measure]
  rw [lintegral_map (f := fun z : Real => ENNReal.ofReal (Real.exp (-t*z))) (by fun_prop)
    (by fun_prop)]
  congr 1
  apply lintegral_congr
  intro z
  congr 2
  ring
