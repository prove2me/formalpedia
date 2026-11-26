-- Prove2me | solution 1 for O3.lpNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:51:52.083818+00:00
-- url     : https://prove2.me/submissions/0341c671-2047-4b3a-afa1-bd27b7ebe351

import Mathlib
import Definitions.Def_O3_Geometry
import Theorems.Thm_O3_lpPower_nonneg

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution (p : ℝ) {d : ℕ} (x : Point d) : 0 ≤ lpNorm p x := by
  exact Real.rpow_nonneg (lpPower_nonneg p x) (1 / p)
end O3
