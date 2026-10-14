-- Prove2me | solution 2 for IntMul.HvdH.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-13T21:38:05.372979+00:00
-- url     : https://prove2.me/submissions/8305415f-f705-451e-8a3a-4cd1554ec4e2

import Definitions.Def_IntMul_MultitapeModel
import Theorems.Thm_NLogN_FIN_theorem_1_1_nlogn

set_option maxHeartbeats 1000000

open IntMul IntMul.HvdH

theorem solution : MulTimeBound fun n => (n : ℝ) * Real.log n :=
  NLogN.FIN.theorem_1_1_nlogn
