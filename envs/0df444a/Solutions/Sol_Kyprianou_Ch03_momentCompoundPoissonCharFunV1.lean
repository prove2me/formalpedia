-- Prove2me | solution 1 for Kyprianou.Ch03.momentCompoundPoissonCharFunV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:45:46.48879+00:00
-- url     : https://prove2.me/submissions/aa3e029f-4b6d-4e6d-ab62-9e7a590ee4b5

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
import Theorems.Thm_Kyprianou_Ch03_momentCPCharSeriesV1
import Theorems.Thm_Kyprianou_Ch03_momentCPCharSeriesEvalV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (mu : Measure Real) [IsFiniteMeasure mu] (xi : Real) :
    charFun (KSATSingleFlip.Connect.compoundPoisson mu) xi =
      Complex.exp (∫ x, (Complex.exp (Complex.I * (((xi * x : Real) : Complex))) - 1) ∂mu) := by
  rw [Kyprianou.Ch03.momentCPCharSeriesV1 mu xi]
  exact Kyprianou.Ch03.momentCPCharSeriesEvalV1 mu xi
