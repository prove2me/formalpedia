-- Prove2me | solution 1 for O3.lpNorm_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:52:13.246072+00:00
-- url     : https://prove2.me/submissions/9736e3f6-09e9-4945-9cf1-d4a084d83958

import Mathlib
import Definitions.Def_O3_Geometry
import Theorems.Thm_O3_lpPower_zero
attribute [local simp] O3.lpPower_zero

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution {p : ℝ} (hp : 0 < p) {d : ℕ} :
    lpNorm p (0 : Point d) = 0 := by
  simp [lpNorm, hp.ne']
end O3
