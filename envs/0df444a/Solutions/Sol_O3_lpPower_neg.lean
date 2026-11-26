-- Prove2me | solution 1 for O3.lpPower_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:53:50.610792+00:00
-- url     : https://prove2.me/submissions/8797d274-9a49-4a4d-bdbd-f2a1e0ed1092

import Mathlib
import Definitions.Def_O3_Geometry
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_lpNorm_zero
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.lpNorm_zero

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution (p : ℝ) {d : ℕ} (x : Point d) :
    lpPower p (-x) = lpPower p x := by
  simp [lpPower]
end O3
