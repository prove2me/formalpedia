-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_product_grid_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:29:21.614594+00:00
-- url     : https://prove2.me/submissions/ad18e046-52a7-4b46-8421-3c0e5a523666

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
open Filter Topology
set_option autoImplicit false

/-- A convergent right-point correction determines the predictable grid limit. -/
theorem solution (Q C : Nat → Complex) (Za Zb limit : Complex)
    (hGrid : ∀ n, Q n + C n = Zb - Za)
    (hLim : Tendsto C atTop (nhds limit)) :
    Tendsto Q atTop (nhds (Zb-Za-limit)) := by
  have heq : Q = fun n => Zb-Za-C n := by
    funext n
    linear_combination hGrid n
  rw [heq]
  exact tendsto_const_nhds.sub hLim
