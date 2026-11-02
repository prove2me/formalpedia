-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_19_19_s50
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T10:44:44.95602+00:00
-- url     : https://prove2.me/submissions/c2c9f1d8-9417-4366-bca3-87f0cced12b5

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI.Laughlin.Certificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem solution : Y 21 19 19 = (0 : ℚ) :=
  by

  simp only [OAI.Laughlin.Certificate.Y, OAI.Laughlin.Certificate.rows,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yRow,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yEntry, OAI.Laughlin.Certificate.V]
  norm_num
