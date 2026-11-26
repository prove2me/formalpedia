-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_5_iii_goalV3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:26:36.01842+00:00
-- url     : https://prove2.me/submissions/86d4a590-a70e-4894-8f08-d7f1a3f537f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise45PureJumpLimitWitnessV1
import Theorems.Thm_Kyprianou_Ch04_martingaleTerminalL1LimitV1
import Theorems.Thm_Kyprianou_Ch04_exercise45FiniteCutoffMartingaleV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false
/-- Recover the limiting martingale from the original cutoff witnesses. -/
theorem solution : Kyprianou.Ch04.certificate_ex4_5_iiiV3 := by
  unfold Kyprianou.Ch04.certificate_ex4_5_iiiV3
  intro Ω m P hP F X hLevy triplet hSigma hNoGaussian hTriplet hFiltration N
    Xleft hLeft hNLaw f fTime fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime
    hSmoothSpace hJoint K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft
    hX2Representation hXepsRepresentation Mε hMRepresentation hConv
  obtain ⟨M,I,e,he,hA,hI,hL1,hSq,hRight,hUCP,hL2,hGrid,hIto⟩ :=
    Kyprianou.Ch04.exercise45PureJumpLimitWitnessV1 P F X hLevy triplet
      hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime fSpace fSpace2
      hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint K hK hBound
      Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation hXepsRepresentation
      Mε hMRepresentation hConv
  have hm (n : ℕ) : Martingale (Mε (e n)) F P := by
    have h := (Kyprianou.Ch04.exercise45FiniteCutoffMartingaleV1 P F X hLevy
      triplet hNoGaussian hTriplet hFiltration N Xleft hLeft hNLaw f fTime
      fSpace fSpace2 hTime hSpace hSpace2 hSmoothTime hSmoothSpace hJoint
      K hK hBound Xeps XepsLeft X2 hXepsInitial hXepsLeft hX2Representation
      hXepsRepresentation (e n) (he n).1 (he n).2).1
    convert h using 1
    funext t w
    exact hMRepresentation (e n) (he n).1 (he n).2 t w
  exact ⟨M,I,Kyprianou.Ch04.martingaleTerminalL1LimitV1 P F
    (fun n => Mε (e n)) M hm hA hI hL1,hSq,hRight,hUCP,hL2,hGrid,hIto⟩
