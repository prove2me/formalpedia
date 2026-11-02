-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_23_9_19_s50
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T07:40:34.165512+00:00
-- url     : https://prove2.me/submissions/fa268cc7-97fd-41d0-859f-ac1f346238df

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI.Laughlin.Certificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem solution : Y 23 9 19 = (0 : ℚ) :=
  by
  have hU0 : U 1 9 9 1 = 9 := by decide
  have hU1 : U 1 9 9 2 = -36 := by decide
  have hU2 : U 1 9 9 3 = 84 := by decide
  have hU3 : U 1 9 9 4 = -126 := by decide
  have hU4 : U 1 9 9 5 = 126 := by decide
  have hU5 : U 1 9 9 6 = -84 := by decide
  have hU6 : U 1 9 9 7 = 36 := by decide
  have hU7 : U 1 9 9 8 = -9 := by decide
  have hU8 : U 1 9 10 2 = -27 := by decide
  have hU9 : U 1 9 10 3 = 48 := by decide
  have hU10 : U 1 9 10 4 = -42 := by decide
  have hU11 : U 1 9 10 5 = 0 := by decide
  have hU12 : U 1 9 10 6 = 42 := by decide
  have hU13 : U 1 9 10 7 = -48 := by decide
  have hU14 : U 1 9 10 8 = 27 := by decide
  have hU15 : U 1 9 11 3 = 21 := by decide
  have hU16 : U 1 9 11 4 = 6 := by decide
  have hU17 : U 1 9 11 5 = -42 := by decide
  have hU18 : U 1 9 11 6 = 42 := by decide
  have hU19 : U 1 9 11 7 = -6 := by decide
  have hU20 : U 1 9 11 8 = -21 := by decide
  have hU21 : U 1 9 12 4 = 27 := by decide
  have hU22 : U 1 9 12 5 = -36 := by decide
  have hU23 : U 1 9 12 6 = 0 := by decide
  have hU24 : U 1 9 12 7 = 36 := by decide
  have hU25 : U 1 9 12 8 = -27 := by decide
  have hU26 : U 1 9 13 5 = -9 := by decide
  have hU27 : U 1 9 13 6 = -36 := by decide
  have hU28 : U 1 9 13 7 = 36 := by decide
  have hU29 : U 1 9 13 8 = 9 := by decide
  have hU30 : U 1 9 14 6 = -45 := by decide
  have hU31 : U 1 9 14 7 = 0 := by decide
  have hU32 : U 1 9 14 8 = 45 := by decide
  have hU33 : U 1 9 15 7 = -45 := by decide
  have hU34 : U 1 9 15 8 = 45 := by decide
  have hU35 : U 1 9 16 8 = 0 := by decide
  have hU36 : U 1 14 0 0 = 0 := by decide
  have hU37 : U 1 14 1 0 = 0 := by decide
  have hU38 : U 1 14 1 1 = 0 := by decide
  have hU39 : U 1 14 2 0 = 0 := by decide
  have hU40 : U 1 14 2 1 = 0 := by decide
  have hU41 : U 1 14 2 2 = 0 := by decide
  have hU42 : U 1 14 3 0 = 0 := by decide
  have hU43 : U 1 14 3 1 = 0 := by decide
  have hU44 : U 1 14 3 2 = 0 := by decide
  have hU45 : U 1 14 3 3 = 0 := by decide
  have hU46 : U 1 14 4 0 = 0 := by decide
  have hU47 : U 1 14 4 1 = 0 := by decide
  have hU48 : U 1 14 4 2 = 0 := by decide
  have hU49 : U 1 14 4 3 = 0 := by decide
  have hU50 : U 1 14 4 4 = 0 := by decide
  have hU51 : U 1 14 5 0 = 0 := by decide
  have hU52 : U 1 14 5 1 = 0 := by decide
  have hU53 : U 1 14 5 2 = 0 := by decide
  have hU54 : U 1 14 5 3 = 0 := by decide
  have hU55 : U 1 14 5 4 = 0 := by decide
  have hU56 : U 1 14 5 5 = 0 := by decide
  have hU57 : U 1 14 6 0 = 0 := by decide
  have hU58 : U 1 14 6 1 = 0 := by decide
  have hU59 : U 1 14 6 2 = 0 := by decide
  have hU60 : U 1 14 6 3 = 0 := by decide
  have hU61 : U 1 14 6 4 = 0 := by decide
  have hU62 : U 1 14 6 5 = 0 := by decide
  have hU63 : U 1 14 6 6 = 0 := by decide
  have hU64 : U 1 14 7 0 = 0 := by decide
  have hU65 : U 1 14 7 1 = 0 := by decide
  have hU66 : U 1 14 7 2 = 0 := by decide
  have hU67 : U 1 14 7 3 = 0 := by decide
  have hU68 : U 1 14 7 4 = 0 := by decide
  have hU69 : U 1 14 7 5 = 0 := by decide
  have hU70 : U 1 14 7 6 = 0 := by decide
  have hU71 : U 1 14 7 7 = 0 := by decide
  have hU72 : U 1 14 8 1 = 0 := by decide
  have hU73 : U 1 14 8 2 = 0 := by decide
  have hU74 : U 1 14 8 3 = 0 := by decide
  have hU75 : U 1 14 8 4 = 0 := by decide
  have hU76 : U 1 14 8 5 = 0 := by decide
  have hU77 : U 1 14 8 6 = 0 := by decide
  have hU78 : U 1 14 8 7 = 0 := by decide
  have hU79 : U 1 14 9 2 = 0 := by decide
  have hU80 : U 1 14 9 3 = 0 := by decide
  have hU81 : U 1 14 9 4 = 0 := by decide
  have hU82 : U 1 14 9 5 = 0 := by decide
  have hU83 : U 1 14 9 6 = 0 := by decide
  have hU84 : U 1 14 9 7 = 0 := by decide
  have hU85 : U 1 14 10 3 = 0 := by decide
  have hU86 : U 1 14 10 4 = 0 := by decide
  have hU87 : U 1 14 10 5 = 0 := by decide
  have hU88 : U 1 14 10 6 = 0 := by decide
  have hU89 : U 1 14 10 7 = 0 := by decide
  have hU90 : U 1 14 11 4 = 0 := by decide
  have hU91 : U 1 14 11 5 = 0 := by decide
  have hU92 : U 1 14 11 6 = 0 := by decide
  have hU93 : U 1 14 11 7 = 0 := by decide
  have hU94 : U 1 14 12 5 = 0 := by decide
  have hU95 : U 1 14 12 6 = 0 := by decide
  have hU96 : U 1 14 12 7 = 0 := by decide
  have hU97 : U 1 14 14 7 = -3432 := by decide
  simp only [OAI.Laughlin.Certificate.Y, OAI.Laughlin.Certificate.rows,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yRow,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yEntry, OAI.Laughlin.Certificate.V]
  simp only [hU0, hU1, hU2, hU3, hU4, hU5, hU6, hU7, hU8, hU9, hU10, hU11, hU12, hU13, hU14, hU15, hU16, hU17, hU18, hU19, hU20, hU21, hU22, hU23, hU24, hU25, hU26, hU27, hU28, hU29, hU30, hU31, hU32, hU33, hU34, hU35, hU36, hU37, hU38, hU39, hU40, hU41, hU42, hU43, hU44, hU45, hU46, hU47, hU48, hU49, hU50, hU51, hU52, hU53, hU54, hU55, hU56, hU57, hU58, hU59, hU60, hU61, hU62, hU63, hU64, hU65, hU66, hU67, hU68, hU69, hU70, hU71, hU72, hU73, hU74, hU75, hU76, hU77, hU78, hU79, hU80, hU81, hU82, hU83, hU84, hU85, hU86, hU87, hU88, hU89, hU90, hU91, hU92, hU93, hU94, hU95, hU96, hU97]
  norm_num
