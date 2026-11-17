-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicJumpWeightsHasSumOne
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:53:04.259415+00:00
-- url     : https://prove2.me/submissions/1ac43b4a-b00e-45f9-88a1-30dc59c42459

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_Kyprianou_Ch01_realLogSeriesMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

theorem solution (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun n : ℕ =>
        (q ^ (n + 1) / ((n : ℝ) + 1)) /
          (-Real.log (1 - q))) 1 := by
  have hpos : 0 < -Real.log (1 - q) := by
    have h1 : 0 < 1 - q := sub_pos.mpr hq1
    have hlt : 1 - q < 1 := sub_lt_self 1 hq0
    exact neg_pos.mpr (Real.log_neg h1 hlt)
  have hbase :=
    Kyprianou.Ch01.realLogSeriesMass q (le_of_lt hq0) hq1
  have hn := hbase.div_const (-Real.log (1 - q))
  simpa only [div_self (ne_of_gt hpos)] using hn
