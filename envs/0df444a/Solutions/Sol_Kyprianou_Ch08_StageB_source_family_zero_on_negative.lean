-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_family_zero_on_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:03:33.923183+00:00
-- url     : https://prove2.me/submissions/edc27013-a23c-441f-8065-ac2ca9300311

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q x : ℝ) (hq : 0 ≤ q) (hx : x < 0) :
    W q x = 0 := by
  exact (hW q hq).2.1 x hx
