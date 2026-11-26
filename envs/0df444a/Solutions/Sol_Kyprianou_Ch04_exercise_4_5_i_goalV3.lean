-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_5_i_goalV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T09:15:22.10454+00:00
-- url     : https://prove2.me/submissions/8b08b1c1-c01d-4e84-98b9-1af0729bf2f8

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise45FiniteCutoffMartingaleV1
import Theorems.Thm_Kyprianou_Ch04_exercise45FiniteCutoffPathIdentityV1
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Assemble the exact common physical martingale and pathwise witnesses. -/
theorem solution : Kyprianou.Ch04.certificate_ex4_5_iV3 := by
  unfold Kyprianou.Ch04.certificate_ex4_5_iV3
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation e he he1
  have hm := Kyprianou.Ch04.exercise45FiniteCutoffMartingaleV1 P F X hLevy
    triplet hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
    Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation e he he1
  obtain ⟨I,hGrid,hIto⟩ := Kyprianou.Ch04.exercise45FiniteCutoffPathIdentityV1 P F X hLevy
    triplet hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
    hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
    Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation e he he1
  exact ⟨_,I,fun _ _ => rfl,hm.1,hm.2.1,hm.2.2,hGrid,hIto⟩
