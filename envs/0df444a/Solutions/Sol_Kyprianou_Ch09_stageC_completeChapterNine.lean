-- Prove2me | solution 1 for Kyprianou.Ch09.stageC_completeChapterNine
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:48:25.411857+00:00
-- url     : https://prove2.me/submissions/272f5533-0866-4f18-90c4-fb494f515d84
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch09_SourceCertificates
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_1
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_2
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_3
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_4
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_6
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_7
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_8
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_9
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_10
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_11
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_12
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_13
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_14
import Theorems.Thm_Kyprianou_Ch09_stageC_result_9_15
import Theorems.Thm_Kyprianou_Ch09_stageC_exercise_9_1
import Theorems.Thm_Kyprianou_Ch09_stageC_exercise_9_2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch09
universe v

theorem solution :
  certificate_result_9_1 ∧
    certificate_result_9_2 ∧
    certificate_result_9_3 ∧
    certificate_result_9_4 ∧
    certificate_result_9_6 ∧
    certificate_result_9_7 ∧
    certificate_result_9_8.{v} ∧
    certificate_result_9_9 ∧
    certificate_result_9_10 ∧
    certificate_result_9_11 ∧
    certificate_result_9_12 ∧
    certificate_result_9_13 ∧
    certificate_result_9_14 ∧
    certificate_result_9_15 ∧
    certificate_exercise_9_1 ∧
    certificate_exercise_9_2 := by
  exact ⟨
    Kyprianou.Ch09.stageC_result_9_1,
    Kyprianou.Ch09.stageC_result_9_2,
    Kyprianou.Ch09.stageC_result_9_3,
    Kyprianou.Ch09.stageC_result_9_4,
    Kyprianou.Ch09.stageC_result_9_6,
    Kyprianou.Ch09.stageC_result_9_7,
    Kyprianou.Ch09.stageC_result_9_8,
    Kyprianou.Ch09.stageC_result_9_9,
    Kyprianou.Ch09.stageC_result_9_10,
    Kyprianou.Ch09.stageC_result_9_11,
    Kyprianou.Ch09.stageC_result_9_12,
    Kyprianou.Ch09.stageC_result_9_13,
    Kyprianou.Ch09.stageC_result_9_14,
    Kyprianou.Ch09.stageC_result_9_15,
    Kyprianou.Ch09.stageC_exercise_9_1,
    Kyprianou.Ch09.stageC_exercise_9_2
  ⟩
