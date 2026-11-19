-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_exercise8_4_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:20:35.502413+00:00
-- url     : https://prove2.me/submissions/466b82d1-dd1b-418e-ab07-3892d0b0c37b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_4_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_4_ii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_4_iii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_4_iv_v2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_exercise8_4 := by
  exact ⟨
    Kyprianou.Ch08.StageB.part_exercise8_4_i_v2,
    Kyprianou.Ch08.StageB.part_exercise8_4_ii_v2,
    Kyprianou.Ch08.StageB.part_exercise8_4_iii_v2,
    Kyprianou.Ch08.StageB.part_exercise8_4_iv_v2
  ⟩
