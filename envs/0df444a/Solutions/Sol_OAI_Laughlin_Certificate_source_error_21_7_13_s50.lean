-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_7_13_s50
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T07:57:52.642021+00:00
-- url     : https://prove2.me/submissions/67f5b506-4348-4af3-b612-fb69d88b5442

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI.Laughlin.Certificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem solution : Y 21 7 13 = (81562090823302666065489/5120000000000 : ℚ) :=
  by
  have hU0 : U 1 7 7 1 = 7 := by decide
  have hU1 : U 1 7 7 2 = -21 := by decide
  have hU2 : U 1 7 7 3 = 35 := by decide
  have hU3 : U 1 7 7 4 = -35 := by decide
  have hU4 : U 1 7 7 5 = 21 := by decide
  have hU5 : U 1 7 7 6 = -7 := by decide
  have hU6 : U 1 7 7 7 = 1 := by decide
  have hU7 : U 1 7 8 1 = 6 := by decide
  have hU8 : U 1 7 8 2 = -14 := by decide
  have hU9 : U 1 7 8 3 = 14 := by decide
  have hU10 : U 1 7 8 4 = 0 := by decide
  have hU11 : U 1 7 8 5 = -14 := by decide
  have hU12 : U 1 7 8 6 = 14 := by decide
  have hU13 : U 1 7 8 7 = -6 := by decide
  have hU14 : U 1 7 8 8 = 1 := by decide
  have hU15 : U 1 7 9 1 = 5 := by decide
  have hU16 : U 1 7 9 2 = -8 := by decide
  have hU17 : U 1 7 9 3 = 0 := by decide
  have hU18 : U 1 7 9 4 = 14 := by decide
  have hU19 : U 1 7 9 5 = -14 := by decide
  have hU20 : U 1 7 9 6 = 0 := by decide
  have hU21 : U 1 7 9 7 = 8 := by decide
  have hU22 : U 1 7 9 8 = -5 := by decide
  have hU23 : U 1 7 10 2 = -3 := by decide
  have hU24 : U 1 7 10 3 = -8 := by decide
  have hU25 : U 1 7 10 4 = 14 := by decide
  have hU26 : U 1 7 10 5 = 0 := by decide
  have hU27 : U 1 7 10 6 = -14 := by decide
  have hU28 : U 1 7 10 7 = 8 := by decide
  have hU29 : U 1 7 10 8 = 3 := by decide
  have hU30 : U 1 7 11 3 = -11 := by decide
  have hU31 : U 1 7 11 4 = 6 := by decide
  have hU32 : U 1 7 11 5 = 14 := by decide
  have hU33 : U 1 7 11 6 = -14 := by decide
  have hU34 : U 1 7 11 7 = -6 := by decide
  have hU35 : U 1 7 11 8 = 11 := by decide
  have hU36 : U 1 7 12 4 = -5 := by decide
  have hU37 : U 1 7 12 5 = 20 := by decide
  have hU38 : U 1 7 12 6 = 0 := by decide
  have hU39 : U 1 7 12 7 = -20 := by decide
  have hU40 : U 1 7 12 8 = 5 := by decide
  have hU41 : U 1 7 13 5 = 15 := by decide
  have hU42 : U 1 7 13 6 = 20 := by decide
  have hU43 : U 1 7 13 7 = -20 := by decide
  have hU44 : U 1 7 13 8 = -15 := by decide
  have hU45 : U 1 7 14 6 = 35 := by decide
  have hU46 : U 1 7 14 7 = 0 := by decide
  have hU47 : U 1 7 14 8 = -35 := by decide
  have hU48 : U 1 7 15 7 = 35 := by decide
  have hU49 : U 1 7 15 8 = -35 := by decide
  have hU50 : U 1 7 16 8 = 0 := by decide
  have hU51 : U 1 8 0 0 = 0 := by decide
  have hU52 : U 1 8 1 0 = 0 := by decide
  have hU53 : U 1 8 1 1 = 0 := by decide
  have hU54 : U 1 8 2 0 = 0 := by decide
  have hU55 : U 1 8 2 1 = 0 := by decide
  have hU56 : U 1 8 2 2 = 0 := by decide
  have hU57 : U 1 8 3 0 = 0 := by decide
  have hU58 : U 1 8 3 1 = 0 := by decide
  have hU59 : U 1 8 3 2 = 0 := by decide
  have hU60 : U 1 8 3 3 = 0 := by decide
  have hU61 : U 1 8 4 1 = 0 := by decide
  have hU62 : U 1 8 4 2 = 0 := by decide
  have hU63 : U 1 8 4 3 = 0 := by decide
  have hU64 : U 1 8 4 4 = 0 := by decide
  have hU65 : U 1 8 5 2 = 0 := by decide
  have hU66 : U 1 8 5 3 = 0 := by decide
  have hU67 : U 1 8 5 4 = 0 := by decide
  have hU68 : U 1 8 5 5 = 0 := by decide
  have hU69 : U 1 8 6 3 = 0 := by decide
  have hU70 : U 1 8 6 4 = 0 := by decide
  have hU71 : U 1 8 6 5 = 0 := by decide
  have hU72 : U 1 8 6 6 = 0 := by decide
  have hU73 : U 1 8 7 4 = 0 := by decide
  have hU74 : U 1 8 7 5 = 0 := by decide
  have hU75 : U 1 8 7 6 = 0 := by decide
  have hU76 : U 1 8 7 7 = 0 := by decide
  have hU77 : U 1 8 8 5 = -56 := by decide
  have hU78 : U 1 8 8 6 = 28 := by decide
  have hU79 : U 1 8 8 7 = -8 := by decide
  have hU80 : U 1 8 10 7 = -8 := by decide
  have hU81 : U 1 13 13 5 = 1287 := by decide
  have hU82 : U 1 13 13 6 = -1716 := by decide
  have hU83 : U 1 13 13 7 = 1716 := by decide
  have hU84 : U 1 13 13 8 = -1287 := by decide
  have hU85 : U 1 13 14 6 = -429 := by decide
  have hU86 : U 1 13 14 7 = 0 := by decide
  have hU87 : U 1 13 14 8 = 429 := by decide
  have hU88 : U 1 13 15 7 = -429 := by decide
  have hU89 : U 1 13 15 8 = 429 := by decide
  have hU90 : U 1 13 16 8 = 0 := by decide
  have hU91 : U 1 14 0 0 = 0 := by decide
  have hU92 : U 1 14 1 0 = 0 := by decide
  have hU93 : U 1 14 1 1 = 0 := by decide
  have hU94 : U 1 14 2 0 = 0 := by decide
  have hU95 : U 1 14 2 1 = 0 := by decide
  have hU96 : U 1 14 3 0 = 0 := by decide
  have hU97 : U 1 14 3 1 = 0 := by decide
  have hU98 : U 1 14 3 2 = 0 := by decide
  have hU99 : U 1 14 3 3 = 0 := by decide
  have hU100 : U 1 14 4 0 = 0 := by decide
  have hU101 : U 1 14 4 1 = 0 := by decide
  have hU102 : U 1 14 4 2 = 0 := by decide
  have hU103 : U 1 14 4 3 = 0 := by decide
  have hU104 : U 1 14 4 4 = 0 := by decide
  have hU105 : U 1 14 5 0 = 0 := by decide
  have hU106 : U 1 14 5 1 = 0 := by decide
  have hU107 : U 1 14 5 2 = 0 := by decide
  have hU108 : U 1 14 5 3 = 0 := by decide
  have hU109 : U 1 14 5 4 = 0 := by decide
  have hU110 : U 1 14 5 5 = 0 := by decide
  have hU111 : U 1 14 6 0 = 0 := by decide
  have hU112 : U 1 14 6 1 = 0 := by decide
  have hU113 : U 1 14 6 2 = 0 := by decide
  have hU114 : U 1 14 6 3 = 0 := by decide
  have hU115 : U 1 14 6 4 = 0 := by decide
  have hU116 : U 1 14 6 5 = 0 := by decide
  have hU117 : U 1 14 6 6 = 0 := by decide
  have hU118 : U 1 14 7 0 = 0 := by decide
  have hU119 : U 1 14 7 1 = 0 := by decide
  have hU120 : U 1 14 7 2 = 0 := by decide
  have hU121 : U 1 14 7 3 = 0 := by decide
  have hU122 : U 1 14 7 4 = 0 := by decide
  have hU123 : U 1 14 7 5 = 0 := by decide
  have hU124 : U 1 14 7 6 = 0 := by decide
  have hU125 : U 1 14 7 7 = 0 := by decide
  have hU126 : U 1 14 8 0 = 0 := by decide
  have hU127 : U 1 14 8 1 = 0 := by decide
  have hU128 : U 1 14 8 2 = 0 := by decide
  have hU129 : U 1 14 8 3 = 0 := by decide
  have hU130 : U 1 14 8 4 = 0 := by decide
  have hU131 : U 1 14 8 5 = 0 := by decide
  have hU132 : U 1 14 8 6 = 0 := by decide
  have hU133 : U 1 14 8 7 = 0 := by decide
  have hU134 : U 1 14 9 0 = 0 := by decide
  have hU135 : U 1 14 9 1 = 0 := by decide
  have hU136 : U 1 14 9 2 = 0 := by decide
  have hU137 : U 1 14 9 3 = 0 := by decide
  have hU138 : U 1 14 9 4 = 0 := by decide
  have hU139 : U 1 14 9 5 = 0 := by decide
  have hU140 : U 1 14 9 6 = 0 := by decide
  have hU141 : U 1 14 9 7 = 0 := by decide
  have hU142 : U 1 14 10 1 = 0 := by decide
  have hU143 : U 1 14 10 2 = 0 := by decide
  have hU144 : U 1 14 10 3 = 0 := by decide
  have hU145 : U 1 14 10 4 = 0 := by decide
  have hU146 : U 1 14 10 5 = 0 := by decide
  have hU147 : U 1 14 10 6 = 0 := by decide
  have hU148 : U 1 14 10 7 = 0 := by decide
  have hU149 : U 1 14 11 2 = 0 := by decide
  have hU150 : U 1 14 11 3 = 0 := by decide
  have hU151 : U 1 14 11 4 = 0 := by decide
  have hU152 : U 1 14 11 5 = 0 := by decide
  have hU153 : U 1 14 11 6 = 0 := by decide
  have hU154 : U 1 14 11 7 = 0 := by decide
  have hU155 : U 1 14 12 3 = 0 := by decide
  have hU156 : U 1 14 12 4 = 0 := by decide
  have hU157 : U 1 14 12 5 = 0 := by decide
  have hU158 : U 1 14 12 6 = 0 := by decide
  have hU159 : U 1 14 12 7 = 0 := by decide
  have hU160 : U 1 14 13 4 = 0 := by decide
  have hU161 : U 1 14 13 5 = 0 := by decide
  have hU162 : U 1 14 13 6 = 0 := by decide
  have hU163 : U 1 14 13 7 = 0 := by decide
  have hU164 : U 1 14 14 5 = -2002 := by decide
  have hU165 : U 1 14 14 6 = 3003 := by decide
  have hU166 : U 1 14 14 7 = -3432 := by decide
  have hU167 : U 1 14 16 7 = 572 := by decide
  simp only [OAI.Laughlin.Certificate.Y, OAI.Laughlin.Certificate.rows,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yRow,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yEntry, OAI.Laughlin.Certificate.V]
  simp only [hU0, hU1, hU2, hU3, hU4, hU5, hU6, hU7, hU8, hU9, hU10, hU11, hU12, hU13, hU14, hU15, hU16, hU17, hU18, hU19, hU20, hU21, hU22, hU23, hU24, hU25, hU26, hU27, hU28, hU29, hU30, hU31, hU32, hU33, hU34, hU35, hU36, hU37, hU38, hU39, hU40, hU41, hU42, hU43, hU44, hU45, hU46, hU47, hU48, hU49, hU50, hU51, hU52, hU53, hU54, hU55, hU56, hU57, hU58, hU59, hU60, hU61, hU62, hU63, hU64, hU65, hU66, hU67, hU68, hU69, hU70, hU71, hU72, hU73, hU74, hU75, hU76, hU77, hU78, hU79, hU80, hU81, hU82, hU83, hU84, hU85, hU86, hU87, hU88, hU89, hU90, hU91, hU92, hU93, hU94, hU95, hU96, hU97, hU98, hU99, hU100, hU101, hU102, hU103, hU104, hU105, hU106, hU107, hU108, hU109, hU110, hU111, hU112, hU113, hU114, hU115, hU116, hU117, hU118, hU119, hU120, hU121, hU122, hU123, hU124, hU125, hU126, hU127, hU128, hU129, hU130, hU131, hU132, hU133, hU134, hU135, hU136, hU137, hU138, hU139, hU140, hU141, hU142, hU143, hU144, hU145, hU146, hU147, hU148, hU149, hU150, hU151, hU152, hU153, hU154, hU155, hU156, hU157, hU158, hU159, hU160, hU161, hU162, hU163, hU164, hU165, hU166, hU167]
  norm_num
