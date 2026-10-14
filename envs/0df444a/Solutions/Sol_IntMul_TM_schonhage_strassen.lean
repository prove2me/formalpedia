-- Prove2me | solution 1 for IntMul.TM.schonhage_strassen
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-12T07:57:58.666029+00:00
-- url     : https://prove2.me/submissions/8f9e87a1-9e95-4157-a319-11673d2616c4

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Theorems.Thm_NLogN_ss_mulTimeBound

open IntMul in
theorem solution :
    MulTimeBound fun n => (n : ℝ) * Real.log n * Real.log (Real.log n) :=
  NLogN.ss_mulTimeBound
