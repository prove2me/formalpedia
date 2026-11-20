-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_exercise8_10_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:42:27.089081+00:00
-- url     : https://prove2.me/submissions/cd37c9cd-2b73-4877-b5f7-148b4c784c30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_10_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_10_ii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_10_iii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_10_iv_v2
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_exercise8_10 := by
  exact ⟨part_exercise8_10_i_v2, part_exercise8_10_ii_v2, part_exercise8_10_iii_v2, part_exercise8_10_iv_v2⟩


