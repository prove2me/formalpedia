-- Prove2me | solution 1 for OAI.Laughlin.Certificate.source_error_21_1_15_s50
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-01T08:03:19.960446+00:00
-- url     : https://prove2.me/submissions/6ca19635-7c2f-4b2e-866d-fab2940536ee

import Mathlib
import Definitions.Def_OAIQ050L010

open OAI.Laughlin.Certificate

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem solution : Y 21 1 15 = (-135618250205634004439631/409600000000 : ℚ) :=
  by
  have hU0 : U 1 1 1 1 = 1 := by decide
  have hU1 : U 1 1 2 1 = 0 := by decide
  have hU2 : U 1 1 2 2 = 1 := by decide
  have hU3 : U 1 1 3 1 = -1 := by decide
  have hU4 : U 1 1 3 2 = 1 := by decide
  have hU5 : U 1 1 3 3 = 1 := by decide
  have hU6 : U 1 1 4 1 = -2 := by decide
  have hU7 : U 1 1 4 2 = 0 := by decide
  have hU8 : U 1 1 4 3 = 2 := by decide
  have hU9 : U 1 1 4 4 = 1 := by decide
  have hU10 : U 1 1 5 1 = -3 := by decide
  have hU11 : U 1 1 5 2 = -2 := by decide
  have hU12 : U 1 1 5 3 = 2 := by decide
  have hU13 : U 1 1 5 4 = 3 := by decide
  have hU14 : U 1 1 5 5 = 1 := by decide
  have hU15 : U 1 1 6 1 = -4 := by decide
  have hU16 : U 1 1 6 2 = -5 := by decide
  have hU17 : U 1 1 6 3 = 0 := by decide
  have hU18 : U 1 1 6 4 = 5 := by decide
  have hU19 : U 1 1 6 5 = 4 := by decide
  have hU20 : U 1 1 6 6 = 1 := by decide
  have hU21 : U 1 1 7 1 = -5 := by decide
  have hU22 : U 1 1 7 2 = -9 := by decide
  have hU23 : U 1 1 7 3 = -5 := by decide
  have hU24 : U 1 1 7 4 = 5 := by decide
  have hU25 : U 1 1 7 5 = 9 := by decide
  have hU26 : U 1 1 7 6 = 5 := by decide
  have hU27 : U 1 1 7 7 = 1 := by decide
  have hU28 : U 1 1 8 1 = -6 := by decide
  have hU29 : U 1 1 8 2 = -14 := by decide
  have hU30 : U 1 1 8 3 = -14 := by decide
  have hU31 : U 1 1 8 4 = 0 := by decide
  have hU32 : U 1 1 8 5 = 14 := by decide
  have hU33 : U 1 1 8 6 = 14 := by decide
  have hU34 : U 1 1 8 7 = 6 := by decide
  have hU35 : U 1 1 8 8 = 1 := by decide
  have hU36 : U 1 1 9 1 = -7 := by decide
  have hU37 : U 1 1 9 2 = -20 := by decide
  have hU38 : U 1 1 9 3 = -28 := by decide
  have hU39 : U 1 1 9 4 = -14 := by decide
  have hU40 : U 1 1 9 5 = 14 := by decide
  have hU41 : U 1 1 9 6 = 28 := by decide
  have hU42 : U 1 1 9 7 = 20 := by decide
  have hU43 : U 1 1 9 8 = 7 := by decide
  have hU44 : U 1 1 10 2 = -27 := by decide
  have hU45 : U 1 1 10 3 = -48 := by decide
  have hU46 : U 1 1 10 4 = -42 := by decide
  have hU47 : U 1 1 10 5 = 0 := by decide
  have hU48 : U 1 1 10 6 = 42 := by decide
  have hU49 : U 1 1 10 7 = 48 := by decide
  have hU50 : U 1 1 10 8 = 27 := by decide
  have hU51 : U 1 1 11 3 = -75 := by decide
  have hU52 : U 1 1 11 4 = -90 := by decide
  have hU53 : U 1 1 11 5 = -42 := by decide
  have hU54 : U 1 1 11 6 = 42 := by decide
  have hU55 : U 1 1 11 7 = 90 := by decide
  have hU56 : U 1 1 11 8 = 75 := by decide
  have hU57 : U 1 1 12 4 = -165 := by decide
  have hU58 : U 1 1 12 5 = -132 := by decide
  have hU59 : U 1 1 12 6 = 0 := by decide
  have hU60 : U 1 1 12 7 = 132 := by decide
  have hU61 : U 1 1 12 8 = 165 := by decide
  have hU62 : U 1 1 13 5 = -297 := by decide
  have hU63 : U 1 1 13 6 = -132 := by decide
  have hU64 : U 1 1 13 7 = 132 := by decide
  have hU65 : U 1 1 13 8 = 297 := by decide
  have hU66 : U 1 1 14 6 = -429 := by decide
  have hU67 : U 1 1 14 7 = 0 := by decide
  have hU68 : U 1 1 14 8 = 429 := by decide
  have hU69 : U 1 1 15 7 = -429 := by decide
  have hU70 : U 1 1 15 8 = 429 := by decide
  have hU71 : U 1 1 16 8 = 0 := by decide
  have hU72 : U 1 6 0 0 = 0 := by decide
  have hU73 : U 1 6 1 0 = 0 := by decide
  have hU74 : U 1 6 1 1 = 0 := by decide
  have hU75 : U 1 6 2 1 = 0 := by decide
  have hU76 : U 1 6 2 2 = 0 := by decide
  have hU77 : U 1 6 3 2 = 0 := by decide
  have hU78 : U 1 6 3 3 = 0 := by decide
  have hU79 : U 1 6 4 3 = 0 := by decide
  have hU80 : U 1 6 4 4 = 0 := by decide
  have hU81 : U 1 6 5 4 = 0 := by decide
  have hU82 : U 1 6 5 5 = 0 := by decide
  have hU83 : U 1 6 6 5 = -6 := by decide
  have hU84 : U 1 6 6 6 = 1 := by decide
  have hU85 : U 1 6 8 7 = -4 := by decide
  have hU86 : U 1 15 15 7 = 6435 := by decide
  have hU87 : U 1 15 15 8 = -6435 := by decide
  have hU88 : U 1 15 16 8 = 0 := by decide
  have hU89 : U 1 20 4 0 = 0 := by decide
  have hU90 : U 1 20 4 1 = 0 := by decide
  have hU91 : U 1 20 4 3 = 0 := by decide
  have hU92 : U 1 20 5 0 = 0 := by decide
  have hU93 : U 1 20 5 1 = 0 := by decide
  have hU94 : U 1 20 5 3 = 0 := by decide
  have hU95 : U 1 20 5 4 = 0 := by decide
  have hU96 : U 1 20 6 0 = 0 := by decide
  have hU97 : U 1 20 6 1 = 0 := by decide
  have hU98 : U 1 20 6 3 = 0 := by decide
  have hU99 : U 1 20 6 4 = 0 := by decide
  have hU100 : U 1 20 6 6 = 0 := by decide
  have hU101 : U 1 20 7 0 = 0 := by decide
  have hU102 : U 1 20 7 1 = 0 := by decide
  have hU103 : U 1 20 7 3 = 0 := by decide
  have hU104 : U 1 20 7 4 = 0 := by decide
  have hU105 : U 1 20 7 5 = 0 := by decide
  have hU106 : U 1 20 7 6 = 0 := by decide
  have hU107 : U 1 20 7 7 = 0 := by decide
  have hU108 : U 1 20 8 0 = 0 := by decide
  have hU109 : U 1 20 8 1 = 0 := by decide
  have hU110 : U 1 20 8 3 = 0 := by decide
  have hU111 : U 1 20 8 4 = 0 := by decide
  have hU112 : U 1 20 8 5 = 0 := by decide
  have hU113 : U 1 20 8 6 = 0 := by decide
  have hU114 : U 1 20 8 7 = 0 := by decide
  have hU115 : U 1 20 9 0 = 0 := by decide
  have hU116 : U 1 20 9 1 = 0 := by decide
  have hU117 : U 1 20 9 2 = 0 := by decide
  have hU118 : U 1 20 9 3 = 0 := by decide
  have hU119 : U 1 20 9 4 = 0 := by decide
  have hU120 : U 1 20 9 5 = 0 := by decide
  have hU121 : U 1 20 9 6 = 0 := by decide
  have hU122 : U 1 20 9 7 = 0 := by decide
  have hU123 : U 1 20 10 0 = 0 := by decide
  have hU124 : U 1 20 10 1 = 0 := by decide
  have hU125 : U 1 20 10 2 = 0 := by decide
  have hU126 : U 1 20 10 3 = 0 := by decide
  have hU127 : U 1 20 10 4 = 0 := by decide
  have hU128 : U 1 20 10 5 = 0 := by decide
  have hU129 : U 1 20 10 6 = 0 := by decide
  have hU130 : U 1 20 10 7 = 0 := by decide
  have hU131 : U 1 20 11 0 = 0 := by decide
  have hU132 : U 1 20 11 1 = 0 := by decide
  have hU133 : U 1 20 11 2 = 0 := by decide
  have hU134 : U 1 20 11 3 = 0 := by decide
  have hU135 : U 1 20 11 4 = 0 := by decide
  have hU136 : U 1 20 11 5 = 0 := by decide
  have hU137 : U 1 20 11 6 = 0 := by decide
  have hU138 : U 1 20 11 7 = 0 := by decide
  have hU139 : U 1 20 12 0 = 0 := by decide
  have hU140 : U 1 20 12 1 = 0 := by decide
  have hU141 : U 1 20 12 2 = 0 := by decide
  have hU142 : U 1 20 12 3 = 0 := by decide
  have hU143 : U 1 20 12 4 = 0 := by decide
  have hU144 : U 1 20 12 5 = 0 := by decide
  have hU145 : U 1 20 12 6 = 0 := by decide
  have hU146 : U 1 20 12 7 = 0 := by decide
  have hU147 : U 1 20 13 0 = 0 := by decide
  have hU148 : U 1 20 13 1 = 0 := by decide
  have hU149 : U 1 20 13 2 = 0 := by decide
  have hU150 : U 1 20 13 3 = 0 := by decide
  have hU151 : U 1 20 13 4 = 0 := by decide
  have hU152 : U 1 20 13 5 = 0 := by decide
  have hU153 : U 1 20 13 6 = 0 := by decide
  have hU154 : U 1 20 13 7 = 0 := by decide
  have hU155 : U 1 20 14 0 = 0 := by decide
  have hU156 : U 1 20 14 1 = 0 := by decide
  have hU157 : U 1 20 14 2 = 0 := by decide
  have hU158 : U 1 20 14 3 = 0 := by decide
  have hU159 : U 1 20 14 4 = 0 := by decide
  have hU160 : U 1 20 14 5 = 0 := by decide
  have hU161 : U 1 20 14 6 = 0 := by decide
  have hU162 : U 1 20 14 7 = 0 := by decide
  have hU163 : U 1 20 15 0 = 0 := by decide
  have hU164 : U 1 20 15 1 = 0 := by decide
  have hU165 : U 1 20 15 2 = 0 := by decide
  have hU166 : U 1 20 15 3 = 0 := by decide
  have hU167 : U 1 20 15 4 = 0 := by decide
  have hU168 : U 1 20 15 5 = 0 := by decide
  have hU169 : U 1 20 15 6 = 0 := by decide
  have hU170 : U 1 20 15 7 = 0 := by decide
  have hU171 : U 1 20 16 1 = 0 := by decide
  have hU172 : U 1 20 16 2 = 0 := by decide
  have hU173 : U 1 20 16 3 = 0 := by decide
  have hU174 : U 1 20 16 4 = 0 := by decide
  have hU175 : U 1 20 16 5 = 0 := by decide
  have hU176 : U 1 20 16 6 = 0 := by decide
  have hU177 : U 1 20 16 7 = 0 := by decide
  have hU178 : U 1 20 17 2 = 0 := by decide
  have hU179 : U 1 20 17 3 = 0 := by decide
  have hU180 : U 1 20 17 4 = 0 := by decide
  have hU181 : U 1 20 17 5 = 0 := by decide
  have hU182 : U 1 20 17 6 = 0 := by decide
  have hU183 : U 1 20 17 7 = 0 := by decide
  have hU184 : U 1 20 18 3 = 0 := by decide
  have hU185 : U 1 20 18 4 = 0 := by decide
  have hU186 : U 1 20 18 5 = 0 := by decide
  have hU187 : U 1 20 18 6 = 0 := by decide
  have hU188 : U 1 20 18 7 = 0 := by decide
  have hU189 : U 1 20 19 4 = 0 := by decide
  have hU190 : U 1 20 19 5 = 0 := by decide
  have hU191 : U 1 20 19 6 = 0 := by decide
  have hU192 : U 1 20 19 7 = 0 := by decide
  have hU193 : U 1 20 20 5 = -15504 := by decide
  have hU194 : U 1 20 20 6 = 38760 := by decide
  have hU195 : U 1 20 20 7 = -77520 := by decide
  have hU196 : U 1 20 22 7 = -15504 := by decide
  simp only [OAI.Laughlin.Certificate.Y, OAI.Laughlin.Certificate.rows,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yRow,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  simp only [OAI.Laughlin.Certificate.yEntry, OAI.Laughlin.Certificate.V]
  simp only [hU0, hU1, hU2, hU3, hU4, hU5, hU6, hU7, hU8, hU9, hU10, hU11, hU12, hU13, hU14, hU15, hU16, hU17, hU18, hU19, hU20, hU21, hU22, hU23, hU24, hU25, hU26, hU27, hU28, hU29, hU30, hU31, hU32, hU33, hU34, hU35, hU36, hU37, hU38, hU39, hU40, hU41, hU42, hU43, hU44, hU45, hU46, hU47, hU48, hU49, hU50, hU51, hU52, hU53, hU54, hU55, hU56, hU57, hU58, hU59, hU60, hU61, hU62, hU63, hU64, hU65, hU66, hU67, hU68, hU69, hU70, hU71, hU72, hU73, hU74, hU75, hU76, hU77, hU78, hU79, hU80, hU81, hU82, hU83, hU84, hU85, hU86, hU87, hU88, hU89, hU90, hU91, hU92, hU93, hU94, hU95, hU96, hU97, hU98, hU99, hU100, hU101, hU102, hU103, hU104, hU105, hU106, hU107, hU108, hU109, hU110, hU111, hU112, hU113, hU114, hU115, hU116, hU117, hU118, hU119, hU120, hU121, hU122, hU123, hU124, hU125, hU126, hU127, hU128, hU129, hU130, hU131, hU132, hU133, hU134, hU135, hU136, hU137, hU138, hU139, hU140, hU141, hU142, hU143, hU144, hU145, hU146, hU147, hU148, hU149, hU150, hU151, hU152, hU153, hU154, hU155, hU156, hU157, hU158, hU159, hU160, hU161, hU162, hU163, hU164, hU165, hU166, hU167, hU168, hU169, hU170, hU171, hU172, hU173, hU174, hU175, hU176, hU177, hU178, hU179, hU180, hU181, hU182, hU183, hU184, hU185, hU186, hU187, hU188, hU189, hU190, hU191, hU192, hU193, hU194, hU195, hU196]
  norm_num
