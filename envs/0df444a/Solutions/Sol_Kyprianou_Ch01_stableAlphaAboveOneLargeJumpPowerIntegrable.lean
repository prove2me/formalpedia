-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneLargeJumpPowerIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:29:16.650191+00:00
-- url     : https://prove2.me/submissions/55cf997f-1e13-49e9-9ebc-637304c0d873

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open Real Set MeasureTheory Kyprianou.Ch01
set_option autoImplicit false

theorem solution
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn (fun r : ℝ => r ^ (-alpha))
      (Set.Ioi (1 : ℝ)) := by
  exact integrableOn_Ioi_rpow_of_lt (by linarith : -alpha < -1)
    (by norm_num : (0 : ℝ) < 1)
