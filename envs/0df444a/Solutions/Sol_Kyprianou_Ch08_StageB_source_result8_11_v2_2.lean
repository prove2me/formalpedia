-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_result8_11_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:43:23.627195+00:00
-- url     : https://prove2.me/submissions/69faaa87-bfb1-4f94-a4d3-52a2322a59ee
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_result8_11_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_result8_11_ii_v2
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_result8_11 := by
  exact ⟨part_result8_11_i_v2, part_result8_11_ii_v2⟩
