-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_19_15_15_s50
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T11:14:58.701059+00:00
-- url     : https://prove2.me/submissions/df4b2665-5cdb-4403-8e31-a933763c6761

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI.Laughlin.Certificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem solution : Y 19 15 15 = (-68818433127534301774563/1638400000000 : ℚ) :=
  by
  have hU0 : U 1 4 0 0 = 0 := by decide
  have hU1 : U 1 4 1 0 = 0 := by decide
  have hU2 : U 1 4 1 1 = 0 := by decide
  have hU3 : U 1 4 2 1 = 0 := by decide
  have hU4 : U 1 4 2 2 = 0 := by decide
  have hU5 : U 1 4 3 2 = 0 := by decide
  have hU6 : U 1 4 3 3 = 0 := by decide
  have hU7 : U 1 4 4 3 = -4 := by decide
  have hU8 : U 1 4 4 4 = 1 := by decide
  have hU9 : U 1 4 5 4 = -3 := by decide
  have hU10 : U 1 4 5 5 = 1 := by decide
  have hU11 : U 1 4 6 5 = -2 := by decide
  have hU12 : U 1 4 6 6 = 1 := by decide
  have hU13 : U 1 4 8 7 = 0 := by decide
  have hU14 : U 1 15 15 7 = 6435 := by decide
  have hU15 : U 1 15 15 8 = -6435 := by decide
  have hU16 : U 1 15 16 8 = 0 := by decide
  simp only [OAI.Laughlin.Certificate.Y, OAI.Laughlin.Certificate.rows,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yRow,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yEntry, OAI.Laughlin.Certificate.V]
  simp only [hU0, hU1, hU2, hU3, hU4, hU5, hU6, hU7, hU8, hU9, hU10, hU11, hU12, hU13, hU14, hU15, hU16]
  norm_num
