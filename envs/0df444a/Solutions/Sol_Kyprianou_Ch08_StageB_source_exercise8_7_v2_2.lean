-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_exercise8_7_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:41:17.400174+00:00
-- url     : https://prove2.me/submissions/910a9c42-c4ab-4777-8cfc-8067d79bf21a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_7_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_7_ii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_7_iii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_7_iv_v2
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_exercise8_7 := by
  exact ⟨part_exercise8_7_i_v2, part_exercise8_7_ii_v2, part_exercise8_7_iii_v2, part_exercise8_7_iv_v2⟩


