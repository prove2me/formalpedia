-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_exercise8_2_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:38:46.50423+00:00
-- url     : https://prove2.me/submissions/d9a0fb80-e20a-4ea5-af56-9ee837ad2fd6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_2_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_2_ii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_2_iii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_2_iv_v2
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_exercise8_2 := by
  exact ⟨part_exercise8_2_i_v2, part_exercise8_2_ii_v2, part_exercise8_2_iii_v2, part_exercise8_2_iv_v2⟩


