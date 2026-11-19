-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_exercise8_7_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:21:30.655719+00:00
-- url     : https://prove2.me/submissions/26e6b5ba-81a5-4064-8ebf-3525deb0acd6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_7_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_7_ii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_7_iii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_7_iv_v2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_exercise8_7 := by
  exact ⟨
    Kyprianou.Ch08.StageB.part_exercise8_7_i_v2,
    Kyprianou.Ch08.StageB.part_exercise8_7_ii_v2,
    Kyprianou.Ch08.StageB.part_exercise8_7_iii_v2,
    Kyprianou.Ch08.StageB.part_exercise8_7_iv_v2
  ⟩
