-- Prove2me | solution 1 for O3.lpPower_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:50:33.587233+00:00
-- url     : https://prove2.me/submissions/1644da22-0bff-4642-b626-89ae0127c189

import Mathlib
import Definitions.Def_O3_Geometry

set_option autoImplicit true
open scoped BigOperators
open O3
namespace O3
theorem _root_.solution (p : ℝ) {d : ℕ} (x : Point d) : 0 ≤ lpPower p x := by
  exact Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (x i)) p
end O3
