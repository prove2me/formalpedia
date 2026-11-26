-- Prove2me | solution 1 for O3.lpPower_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:15.332213+00:00
-- url     : https://prove2.me/submissions/6cd622cd-ef3f-49b3-894b-d2a02ff4fb21

import Mathlib
import Definitions.Def_O3_Geometry

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p : ℝ} (hp : p ≠ 0) {d : ℕ} :
    lpPower p (0 : Point d) = 0 := by
  simp [lpPower, hp]
end O3
