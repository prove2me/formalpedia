-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_exercise8_9_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:21:58.767246+00:00
-- url     : https://prove2.me/submissions/aebf81e8-61b9-4429-afb3-28e41c72418e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_9_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_9_ii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_9_iii_v2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_exercise8_9 := by
  exact ⟨
    Kyprianou.Ch08.StageB.part_exercise8_9_i_v2,
    Kyprianou.Ch08.StageB.part_exercise8_9_ii_v2,
    Kyprianou.Ch08.StageB.part_exercise8_9_iii_v2
  ⟩
