-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49OriginalCertificateFalseV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T16:11:40.347909+00:00
-- url     : https://prove2.me/submissions/9904d5b8-1bcd-47bb-b8fc-aa3df124110c

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise49AdmissibleUniformModelV5
import Theorems.Thm_Kyprianou_Ch04_exercise49CounterexampleFromAdmissibleModelV3
import Definitions.Def_Kyprianou_Ch04_Exercise4_9Certification
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
import Definitions.Def_levy_foundations_exponent
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    : ¬ Kyprianou.Ch04.certificate_ex4_9_iii := by
  obtain ⟨P,X,T,b,hP,hX,hLaw,hBV,hDrift,hb,hNotSub,hInfinity⟩ := exercise49AdmissibleUniformModelV5
  letI : IsProbabilityMeasure P := hP
  exact exercise49CounterexampleFromAdmissibleModelV3 P X hX T hLaw hBV b hDrift hb hNotSub hInfinity
