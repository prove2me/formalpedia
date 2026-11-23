-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.chapterEightMain_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T21:06:26.975466+00:00
-- url     : https://prove2.me/submissions/49eb5cf5-7aa1-4dd6-9463-4676971f35b4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_OriginDriftSign_v3
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_1_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_3_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_4_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_5_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_v3
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

/-- Assemble all mandatory source-certified results for the corrected root. -/
theorem solution :
    sourceCertificate_result8_1 ∧
  sourceCertificate_result8_2 ∧
  sourceCertificate_result8_3 ∧
  sourceCertificate_result8_4 ∧
  sourceCertificate_result8_5 ∧
  sourceCertificate_result8_6_v3 ∧
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
  exact ⟨source_result8_1_v2,
    source_result8_2_v2,
    source_result8_3_v2,
    source_result8_4_v2,
    source_result8_5_v2,
    source_result8_6_v3,
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
    source_exercise8_12_v2⟩
