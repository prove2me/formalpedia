-- Prove2me | solution 1 for Kyprianou.Ch04.exercise_4_6_i_goalV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:22:00.404827+00:00
-- url     : https://prove2.me/submissions/eafadde3-8b4e-4c46-8e44-4f70c68bd5f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_6Certification
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_exercise46QueueLaplaceExponentV1
import Theorems.Thm_Kyprianou_Ch04_totalIdleTrafficMaximalRootV1
import Theorems.Thm_Kyprianou_Ch03_upwardFirstPassageLaplaceTransform
import Theorems.Thm_Kyprianou_Ch04_exercise46RandomWeakPassageTransformV1
import Theorems.Thm_Kyprianou_Ch04_exercise46DefectiveClockCDFTransformV1
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Busy-period transform from strict passage, random weak passage and Tonelli. -/
theorem solution : Kyprianou.Ch04.certificate_ex4_6_i := by
  intro Omega mOmega P G L hBV hd lambda hlambda service hservice hpos hInput
    J hLaw hJ hInd B beta hb
  letI : IsProbabilityMeasure P := L.isProbability
  obtain ⟨phi, hp, hr, hm, hs⟩ := Kyprianou.Ch03.upwardFirstPassageLaplaceTransform
    P G L (Kyprianou.Ch04.totalIdleTrafficMaximalRootV1 P G L hBV
      (by simpa [hd] using zero_lt_one)).1 beta hb
  have he := Kyprianou.Ch04.exercise46QueueLaplaceExponentV1 P G L hBV hd
    lambda hlambda service hInput
  obtain ⟨hB, hI⟩ := Kyprianou.Ch04.exercise46RandomWeakPassageTransformV1
    P G L service J hLaw hJ hInd beta phi hb hp
    (fun x hx => hs x hx (fun w => (Kyprianou.Ch03.firstHittingTime L.X (Ioi x) w).untopD 0)
      (by intro w h; exact (WithTop.coe_untop₀_of_ne_top (by simpa using h)).symm))
  exact ⟨phi, hp, (he phi hp).symm.trans hr,
    fun theta ht htheta => hm theta ht ((he theta ht).trans htheta),
    (Kyprianou.Ch04.exercise46DefectiveClockCDFTransformV1 P _ hB beta hb).trans hI⟩
