-- Prove2me | solution 2 for Kyprianou.Ch08.StageB.source_result8_6_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:13:35.903043+00:00
-- url     : https://prove2.me/submissions/d0f7d4b3-9843-4220-b56c-7d58c3fe3b9a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_origin_discount_invariant
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_6_zero_discount
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08.StageB

theorem solution : sourceCertificate_result8_6 := by
  intro Ω mΩ P hP D ψ W hψ hW q hq
  obtain ⟨hz, hbv⟩ := source_result8_6_zero_discount Ω P D ψ W hψ hW
  have heq := source_scale_origin_discount_invariant ψ W hW q hq
  constructor
  · simpa only [heq] using hz
  · intro hBV
    obtain ⟨hd, hW0⟩ := hbv hBV
    exact ⟨hd, heq.trans hW0⟩
