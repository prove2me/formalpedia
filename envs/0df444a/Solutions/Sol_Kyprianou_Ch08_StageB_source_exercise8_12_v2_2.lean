-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_exercise8_12_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:42:56.191563+00:00
-- url     : https://prove2.me/submissions/7c231377-e38b-4eb2-a5f6-2dd7fb4caf7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_12_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_12_ii_v2
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_exercise8_12 := by
  exact ⟨part_exercise8_12_i_v2, part_exercise8_12_ii_v2⟩


