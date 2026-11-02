-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_17_13_15_s50
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T11:41:38.381634+00:00
-- url     : https://prove2.me/submissions/b4e78c15-aab9-4d61-8f76-b37805afaca0

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI.Laughlin.Certificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem solution : Y 17 13 15 = (797255391734832796032267/819200000000000 : ℚ) :=
  by
  have hU0 : U 1 2 0 0 = 0 := by decide
  have hU1 : U 1 2 1 0 = 0 := by decide
  have hU2 : U 1 2 1 1 = 0 := by decide
  have hU3 : U 1 2 2 1 = -2 := by decide
  have hU4 : U 1 2 2 2 = 1 := by decide
  have hU5 : U 1 2 3 2 = -1 := by decide
  have hU6 : U 1 2 3 3 = 1 := by decide
  have hU7 : U 1 2 4 3 = 0 := by decide
  have hU8 : U 1 2 4 4 = 1 := by decide
  have hU9 : U 1 2 5 4 = 1 := by decide
  have hU10 : U 1 2 5 5 = 1 := by decide
  have hU11 : U 1 2 6 5 = 2 := by decide
  have hU12 : U 1 2 6 6 = 1 := by decide
  have hU13 : U 1 2 8 7 = 4 := by decide
  have hU14 : U 1 4 0 0 = 0 := by decide
  have hU15 : U 1 4 1 0 = 0 := by decide
  have hU16 : U 1 4 1 1 = 0 := by decide
  have hU17 : U 1 4 2 0 = 0 := by decide
  have hU18 : U 1 4 2 1 = 0 := by decide
  have hU19 : U 1 4 2 2 = 0 := by decide
  have hU20 : U 1 4 3 0 = 0 := by decide
  have hU21 : U 1 4 3 1 = 0 := by decide
  have hU22 : U 1 4 3 2 = 0 := by decide
  have hU23 : U 1 4 3 3 = 0 := by decide
  have hU24 : U 1 4 4 1 = -4 := by decide
  have hU25 : U 1 4 4 2 = 6 := by decide
  have hU26 : U 1 4 4 3 = -4 := by decide
  have hU27 : U 1 4 4 4 = 1 := by decide
  have hU28 : U 1 4 5 2 = 2 := by decide
  have hU29 : U 1 4 5 3 = 2 := by decide
  have hU30 : U 1 4 5 4 = -3 := by decide
  have hU31 : U 1 4 5 5 = 1 := by decide
  have hU32 : U 1 4 6 3 = 4 := by decide
  have hU33 : U 1 4 6 4 = -1 := by decide
  have hU34 : U 1 4 6 5 = -2 := by decide
  have hU35 : U 1 4 6 6 = 1 := by decide
  have hU36 : U 1 4 7 4 = 3 := by decide
  have hU37 : U 1 4 7 5 = -3 := by decide
  have hU38 : U 1 4 7 6 = -1 := by decide
  have hU39 : U 1 4 7 7 = 1 := by decide
  have hU40 : U 1 4 8 5 = 0 := by decide
  have hU41 : U 1 4 8 6 = -4 := by decide
  have hU42 : U 1 4 8 7 = 0 := by decide
  have hU43 : U 1 4 10 7 = -8 := by decide
  have hU44 : U 1 13 13 5 = 1287 := by decide
  have hU45 : U 1 13 13 6 = -1716 := by decide
  have hU46 : U 1 13 13 7 = 1716 := by decide
  have hU47 : U 1 13 13 8 = -1287 := by decide
  have hU48 : U 1 13 14 6 = -429 := by decide
  have hU49 : U 1 13 14 7 = 0 := by decide
  have hU50 : U 1 13 14 8 = 429 := by decide
  have hU51 : U 1 13 15 7 = -429 := by decide
  have hU52 : U 1 13 15 8 = 429 := by decide
  have hU53 : U 1 13 16 8 = 0 := by decide
  have hU54 : U 1 15 15 7 = 6435 := by decide
  have hU55 : U 1 15 15 8 = -6435 := by decide
  have hU56 : U 1 15 16 8 = 0 := by decide
  simp only [OAI.Laughlin.Certificate.Y, OAI.Laughlin.Certificate.rows,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yRow,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yEntry, OAI.Laughlin.Certificate.V]
  simp only [hU0, hU1, hU2, hU3, hU4, hU5, hU6, hU7, hU8, hU9, hU10, hU11, hU12, hU13, hU14, hU15, hU16, hU17, hU18, hU19, hU20, hU21, hU22, hU23, hU24, hU25, hU26, hU27, hU28, hU29, hU30, hU31, hU32, hU33, hU34, hU35, hU36, hU37, hU38, hU39, hU40, hU41, hU42, hU43, hU44, hU45, hU46, hU47, hU48, hU49, hU50, hU51, hU52, hU53, hU54, hU55, hU56]
  norm_num
