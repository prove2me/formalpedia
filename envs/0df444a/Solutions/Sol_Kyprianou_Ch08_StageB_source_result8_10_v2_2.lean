-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_result8_10_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:43:11.586434+00:00
-- url     : https://prove2.me/submissions/1b4fc923-fe42-4e25-a180-5bcaec295c5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_result8_10_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_result8_10_ii_v2
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_result8_10 := by
  exact ⟨part_result8_10_i_v2, part_result8_10_ii_v2⟩
