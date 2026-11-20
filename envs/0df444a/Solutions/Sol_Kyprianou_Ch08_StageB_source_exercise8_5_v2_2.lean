-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_exercise8_5_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:39:43.825752+00:00
-- url     : https://prove2.me/submissions/b43270b8-e6b3-4d4b-96b9-2d5e2b44c126
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_5_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_5_ii_v2
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_exercise8_5 := by
  exact ⟨part_exercise8_5_i_v2, part_exercise8_5_ii_v2⟩


