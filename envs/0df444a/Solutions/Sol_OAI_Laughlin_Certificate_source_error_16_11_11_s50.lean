-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_16_11_11_s50
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T11:51:49.741614+00:00
-- url     : https://prove2.me/submissions/38b1e2ad-9e12-4e30-baa0-177de81b1f8d

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI.Laughlin.Certificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem solution : Y 16 11 11 = (-47586420975452552673183/1638400000000000 : ℚ) :=
  by
  have hU0 : U 1 5 0 0 = 0 := by decide
  have hU1 : U 1 5 1 0 = 0 := by decide
  have hU2 : U 1 5 1 1 = 0 := by decide
  have hU3 : U 1 5 2 0 = 0 := by decide
  have hU4 : U 1 5 2 1 = 0 := by decide
  have hU5 : U 1 5 2 2 = 0 := by decide
  have hU6 : U 1 5 3 0 = 0 := by decide
  have hU7 : U 1 5 3 1 = 0 := by decide
  have hU8 : U 1 5 3 2 = 0 := by decide
  have hU9 : U 1 5 3 3 = 0 := by decide
  have hU10 : U 1 5 4 0 = 0 := by decide
  have hU11 : U 1 5 4 1 = 0 := by decide
  have hU12 : U 1 5 4 2 = 0 := by decide
  have hU13 : U 1 5 4 3 = 0 := by decide
  have hU14 : U 1 5 4 4 = 0 := by decide
  have hU15 : U 1 5 5 0 = -1 := by decide
  have hU16 : U 1 5 5 1 = 5 := by decide
  have hU17 : U 1 5 5 2 = -10 := by decide
  have hU18 : U 1 5 5 3 = 10 := by decide
  have hU19 : U 1 5 5 4 = -5 := by decide
  have hU20 : U 1 5 5 5 = 1 := by decide
  have hU21 : U 1 5 6 1 = 4 := by decide
  have hU22 : U 1 5 6 2 = -5 := by decide
  have hU23 : U 1 5 6 3 = 0 := by decide
  have hU24 : U 1 5 6 4 = 5 := by decide
  have hU25 : U 1 5 6 5 = -4 := by decide
  have hU26 : U 1 5 6 6 = 1 := by decide
  have hU27 : U 1 5 7 2 = -1 := by decide
  have hU28 : U 1 5 7 3 = -5 := by decide
  have hU29 : U 1 5 7 4 = 5 := by decide
  have hU30 : U 1 5 7 5 = 1 := by decide
  have hU31 : U 1 5 7 6 = -3 := by decide
  have hU32 : U 1 5 7 7 = 1 := by decide
  have hU33 : U 1 5 8 3 = -6 := by decide
  have hU34 : U 1 5 8 4 = 0 := by decide
  have hU35 : U 1 5 8 5 = 6 := by decide
  have hU36 : U 1 5 8 6 = -2 := by decide
  have hU37 : U 1 5 8 7 = -2 := by decide
  have hU38 : U 1 5 9 4 = -6 := by decide
  have hU39 : U 1 5 9 5 = 6 := by decide
  have hU40 : U 1 5 9 6 = 4 := by decide
  have hU41 : U 1 5 9 7 = -4 := by decide
  have hU42 : U 1 5 10 5 = 0 := by decide
  have hU43 : U 1 5 10 6 = 10 := by decide
  have hU44 : U 1 5 10 7 = 0 := by decide
  have hU45 : U 1 5 12 7 = 20 := by decide
  have hU46 : U 1 11 11 3 = 165 := by decide
  have hU47 : U 1 11 11 4 = -330 := by decide
  have hU48 : U 1 11 11 5 = 462 := by decide
  have hU49 : U 1 11 11 6 = -462 := by decide
  have hU50 : U 1 11 11 7 = 330 := by decide
  have hU51 : U 1 11 11 8 = -165 := by decide
  have hU52 : U 1 11 12 4 = -165 := by decide
  have hU53 : U 1 11 12 5 = 132 := by decide
  have hU54 : U 1 11 12 6 = 0 := by decide
  have hU55 : U 1 11 12 7 = -132 := by decide
  have hU56 : U 1 11 12 8 = 165 := by decide
  have hU57 : U 1 11 13 5 = -33 := by decide
  have hU58 : U 1 11 13 6 = 132 := by decide
  have hU59 : U 1 11 13 7 = -132 := by decide
  have hU60 : U 1 11 13 8 = 33 := by decide
  have hU61 : U 1 11 14 6 = 99 := by decide
  have hU62 : U 1 11 14 7 = 0 := by decide
  have hU63 : U 1 11 14 8 = -99 := by decide
  have hU64 : U 1 11 15 7 = 99 := by decide
  have hU65 : U 1 11 15 8 = -99 := by decide
  have hU66 : U 1 11 16 8 = 0 := by decide
  simp only [OAI.Laughlin.Certificate.Y, OAI.Laughlin.Certificate.rows,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yRow,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yEntry, OAI.Laughlin.Certificate.V]
  simp only [hU0, hU1, hU2, hU3, hU4, hU5, hU6, hU7, hU8, hU9, hU10, hU11, hU12, hU13, hU14, hU15, hU16, hU17, hU18, hU19, hU20, hU21, hU22, hU23, hU24, hU25, hU26, hU27, hU28, hU29, hU30, hU31, hU32, hU33, hU34, hU35, hU36, hU37, hU38, hU39, hU40, hU41, hU42, hU43, hU44, hU45, hU46, hU47, hU48, hU49, hU50, hU51, hU52, hU53, hU54, hU55, hU56, hU57, hU58, hU59, hU60, hU61, hU62, hU63, hU64, hU65, hU66]
  norm_num
