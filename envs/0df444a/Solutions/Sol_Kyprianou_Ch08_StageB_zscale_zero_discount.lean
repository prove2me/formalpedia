-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.zscale_zero_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:48:38.500729+00:00
-- url     : https://prove2.me/submissions/04e3580e-3982-45ac-95dc-948af5087c9b

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_A
set_option autoImplicit false

open Kyprianou.Ch08

theorem solution (W : ℝ → ℝ) (x : ℝ) : Zscale 0 W x = 1 := by
  simp [Zscale]
