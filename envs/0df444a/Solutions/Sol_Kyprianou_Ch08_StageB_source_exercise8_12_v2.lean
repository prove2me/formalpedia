-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_exercise8_12_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:22:50.928925+00:00
-- url     : https://prove2.me/submissions/388859ec-7b14-418d-9cdb-cc6485827ee1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_12_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_12_ii_v2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_exercise8_12 := by
  exact ⟨
    Kyprianou.Ch08.StageB.part_exercise8_12_i_v2,
    Kyprianou.Ch08.StageB.part_exercise8_12_ii_v2
  ⟩
