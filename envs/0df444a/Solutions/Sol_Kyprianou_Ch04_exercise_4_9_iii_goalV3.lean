-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_9_iii_goalV3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:38:18.114376+00:00
-- url     : https://prove2.me/submissions/dc27f2d6-97ca-4ca4-b739-dcf9527ead1a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
import Theorems.Thm_Kyprianou_Ch04_exercise49FiniteClockVersionV3
import Theorems.Thm_Kyprianou_Ch04_exercise49RhoPositiveV3
import Theorems.Thm_Kyprianou_Ch04_exercise49RhoLtOneV3
import Theorems.Thm_Kyprianou_Ch04_exercise49DefectiveLadderRenewalV3
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch04
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Reduce the original survival identity to the clock, probability bounds and renewal law. -/
theorem solution : certificate_ex4_9_iii_v3 := by
  unfold certificate_ex4_9_iii_v3
  intro Ω mΩ P hP X hLevy triplet hTriplet hBV drift hDrift hd hNot hInf
  obtain ⟨f, hf, he⟩ := exercise49FiniteClockVersionV3 P X hLevy 0 le_rfl
  have h0 := exercise49RhoPositiveV3
    P X hLevy triplet hTriplet hBV drift hDrift hd hNot hInf
  have h1 := exercise49RhoLtOneV3
    P X hLevy triplet hTriplet hBV drift hDrift hd hNot hInf
  have hLaw := exercise49DefectiveLadderRenewalV3
    P X hLevy triplet hTriplet hBV drift hDrift hd hNot hInf h0 h1 f hf he
  exact ⟨h0, h1, f, hf, he, hLaw⟩
