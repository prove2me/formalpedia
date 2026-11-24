-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.chapterEightMain_v4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T13:06:40.680936+00:00
-- url     : https://prove2.me/submissions/fcf775da-203d-44c8-a79c-589bf24975f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_Corrected89_Cumulative_v4
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_1_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_3_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_4_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_5_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_v3
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_7_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_8_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_9_v3
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_10_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_11_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_12_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_1_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_2_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_3_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_4_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_5_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_6_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_7_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_8_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_9_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_10_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_11_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_exercise8_12_v2

set_option autoImplicit false
open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_chapterEightMain_v4 := by
  exact ⟨source_result8_1_v2,
    source_result8_2_v2,
    source_result8_3_v2,
    source_result8_4_v2,
    source_result8_5_v2,
    source_result8_6_v3,
    source_result8_7_v2,
    source_result8_8_v2,
    source_result8_9_v3,
    source_result8_10_v2,
    source_result8_11_v2,
    source_result8_12_v2,
    source_exercise8_1_v2,
    source_exercise8_2_v2,
    source_exercise8_3_v2,
    source_exercise8_4_v2,
    source_exercise8_5_v2,
    source_exercise8_6_v2,
    source_exercise8_7_v2,
    source_exercise8_8_v2,
    source_exercise8_9_v2,
    source_exercise8_10_v2,
    source_exercise8_11_v2,
    source_exercise8_12_v2⟩
