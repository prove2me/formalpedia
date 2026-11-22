-- Prove2me | solution 1 for IteratedFDerivShiftTwoPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:10:17.487441+00:00
-- url     : https://prove2.me/submissions/7153cbb0-c1e2-4aae-837b-538500d8b3b6

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_IteratedFDerivShiftTwoPoint

set_option autoImplicit false

theorem _root_.solution (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (f : Plane → Z) (n : ℕ) (x y : Plane) :
    ‖iteratedFDeriv ℝ (n + 1) f x - iteratedFDeriv ℝ (n + 1) f y‖
      = ‖iteratedFDeriv ℝ n (fderiv ℝ f) x - iteratedFDeriv ℝ n (fderiv ℝ f) y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    Function.comp_apply, ← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
