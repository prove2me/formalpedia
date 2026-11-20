-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.chapterEightMain_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:40:26.064171+00:00
-- url     : https://prove2.me/submissions/1f76c2b6-4bae-4c13-8ae4-446b7cea63fd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_1_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_3_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_4_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_5_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_7_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_8_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_9_v2
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

theorem solution :
  sourceCertificate_result8_1 ∧
    sourceCertificate_result8_2 ∧
    sourceCertificate_result8_3 ∧
    sourceCertificate_result8_4 ∧
    sourceCertificate_result8_5 ∧
    sourceCertificate_result8_6 ∧
    sourceCertificate_result8_7 ∧
    sourceCertificate_result8_8 ∧
    sourceCertificate_result8_9 ∧
    sourceCertificate_result8_10 ∧
    sourceCertificate_result8_11 ∧
    sourceCertificate_result8_12 ∧
    sourceCertificate_exercise8_1 ∧
    sourceCertificate_exercise8_2 ∧
    sourceCertificate_exercise8_3 ∧
    sourceCertificate_exercise8_4 ∧
    sourceCertificate_exercise8_5 ∧
    sourceCertificate_exercise8_6 ∧
    sourceCertificate_exercise8_7 ∧
    sourceCertificate_exercise8_8 ∧
    sourceCertificate_exercise8_9 ∧
    sourceCertificate_exercise8_10 ∧
    sourceCertificate_exercise8_11 ∧
    sourceCertificate_exercise8_12 := by
  exact ⟨
    source_result8_1_v2,
    source_result8_2_v2,
    source_result8_3_v2,
    source_result8_4_v2,
    source_result8_5_v2,
    source_result8_6_v2,
    source_result8_7_v2,
    source_result8_8_v2,
    source_result8_9_v2,
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
    source_exercise8_12_v2
  ⟩
