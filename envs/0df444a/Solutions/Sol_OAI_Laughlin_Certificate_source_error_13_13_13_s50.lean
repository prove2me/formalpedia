-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_13_13_13_s50
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T12:20:05.781313+00:00
-- url     : https://prove2.me/submissions/461a6ac8-1c1e-45b0-ac69-db583b973998

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI.Laughlin.Certificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem solution : Y 13 13 13 = (-17580701774552693245136811/13107200000000000 : ℚ) :=
  by
  have hU0 : U 1 0 0 0 = 1 := by decide
  have hU1 : U 1 0 1 0 = 1 := by decide
  have hU2 : U 1 0 1 1 = 1 := by decide
  have hU3 : U 1 0 2 0 = 1 := by decide
  have hU4 : U 1 0 2 1 = 2 := by decide
  have hU5 : U 1 0 2 2 = 1 := by decide
  have hU6 : U 1 0 3 0 = 1 := by decide
  have hU7 : U 1 0 3 1 = 3 := by decide
  have hU8 : U 1 0 3 2 = 3 := by decide
  have hU9 : U 1 0 3 3 = 1 := by decide
  have hU10 : U 1 0 4 1 = 4 := by decide
  have hU11 : U 1 0 4 2 = 6 := by decide
  have hU12 : U 1 0 4 3 = 4 := by decide
  have hU13 : U 1 0 4 4 = 1 := by decide
  have hU14 : U 1 0 5 2 = 10 := by decide
  have hU15 : U 1 0 5 3 = 10 := by decide
  have hU16 : U 1 0 5 4 = 5 := by decide
  have hU17 : U 1 0 5 5 = 1 := by decide
  have hU18 : U 1 0 6 3 = 20 := by decide
  have hU19 : U 1 0 6 4 = 15 := by decide
  have hU20 : U 1 0 6 5 = 6 := by decide
  have hU21 : U 1 0 6 6 = 1 := by decide
  have hU22 : U 1 0 7 4 = 35 := by decide
  have hU23 : U 1 0 7 5 = 21 := by decide
  have hU24 : U 1 0 7 6 = 7 := by decide
  have hU25 : U 1 0 7 7 = 1 := by decide
  have hU26 : U 1 0 8 5 = 56 := by decide
  have hU27 : U 1 0 8 6 = 28 := by decide
  have hU28 : U 1 0 8 7 = 8 := by decide
  have hU29 : U 1 0 10 7 = 120 := by decide
  have hU30 : U 1 13 13 5 = 1287 := by decide
  have hU31 : U 1 13 13 6 = -1716 := by decide
  have hU32 : U 1 13 13 7 = 1716 := by decide
  have hU33 : U 1 13 13 8 = -1287 := by decide
  have hU34 : U 1 13 14 6 = -429 := by decide
  have hU35 : U 1 13 14 7 = 0 := by decide
  have hU36 : U 1 13 14 8 = 429 := by decide
  have hU37 : U 1 13 15 7 = -429 := by decide
  have hU38 : U 1 13 15 8 = 429 := by decide
  have hU39 : U 1 13 16 8 = 0 := by decide
  simp only [OAI.Laughlin.Certificate.Y, OAI.Laughlin.Certificate.rows,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yRow,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yEntry, OAI.Laughlin.Certificate.V]
  simp only [hU0, hU1, hU2, hU3, hU4, hU5, hU6, hU7, hU8, hU9, hU10, hU11, hU12, hU13, hU14, hU15, hU16, hU17, hU18, hU19, hU20, hU21, hU22, hU23, hU24, hU25, hU26, hU27, hU28, hU29, hU30, hU31, hU32, hU33, hU34, hU35, hU36, hU37, hU38, hU39]
  norm_num
