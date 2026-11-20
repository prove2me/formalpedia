-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:06:15.512021+00:00
-- url     : https://prove2.me/submissions/b143d804-db1e-4c12-b596-1ff8d1d253cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_unbounded
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_bounded
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_result8_6 := by
  intro Ω mΩ P hP D ψ W hψ hW q hq
  exact ⟨
    source_result8_6_unbounded Ω P D ψ W hψ hW q hq,
    source_result8_6_bounded Ω P D ψ W hψ hW q hq
  ⟩
