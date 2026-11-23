-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_6_v3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T17:31:03.132882+00:00
-- url     : https://prove2.me/submissions/d5438de8-229f-4d36-bc81-1895ef237335
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_OriginDriftSign_v3
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount_v3
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_origin_discount_invariant
set_option autoImplicit false
open Kyprianou.Ch08.StageB

/-- Lift the source-corrected origin identity from q=0 to q>=0. -/
theorem solution : sourceCertificate_result8_6_v3 := by
  intro Ω mΩ P hP D ψ W hψ hW q hq
  have hzero :=
    source_result8_6_zero_discount_v3 Ω P D ψ W hψ hW
  have hdiscount := source_scale_origin_discount_invariant ψ W hW q hq
  simpa only [hdiscount] using hzero
