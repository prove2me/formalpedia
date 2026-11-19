-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_10_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:19:13.342537+00:00
-- url     : https://prove2.me/submissions/0a169078-d2a4-4407-82bc-de8908197804
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_result8_10_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_part_result8_10_ii_v2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_result8_10 := by
  exact ⟨
    Kyprianou.Ch08.StageB.part_result8_10_i_v2,
    Kyprianou.Ch08.StageB.part_result8_10_ii_v2
  ⟩
