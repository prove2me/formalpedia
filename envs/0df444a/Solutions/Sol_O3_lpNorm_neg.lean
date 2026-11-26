-- Prove2me | solution 1 for O3.lpNorm_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:55:00.766933+00:00
-- url     : https://prove2.me/submissions/b2c3aa3d-1375-4faa-bf02-0a6ea1b2c4d8

import Mathlib
import Definitions.Def_O3_Geometry
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution (p : ℝ) {d : ℕ} (x : Point d) :
    lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]
end O3
