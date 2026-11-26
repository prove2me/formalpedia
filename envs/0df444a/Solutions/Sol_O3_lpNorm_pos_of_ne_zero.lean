-- Prove2me | solution 1 for O3.lpNorm_pos_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:03.746267+00:00
-- url     : https://prove2.me/submissions/d5c4f5ea-257f-45a8-929f-c373419b6043

import Mathlib
import Definitions.Def_O3_Geometry
import Theorems.Thm_O3_lpPower_pos_of_ne_zero

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p : ℝ} {d : ℕ} {x : Point d}
    (hx : x ≠ 0) : 0 < lpNorm p x := by
  exact Real.rpow_pos_of_pos (lpPower_pos_of_ne_zero hx) (1 / p)
end O3
