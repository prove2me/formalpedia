-- Prove2me | solution 1 for O3.Stage2RouteA.lineGradientFormula_deriv_le_above_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:55.847253+00:00
-- url     : https://prove2.me/submissions/3fd582ad-2654-4b9b-a32e-0e6d45f235f5

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteD_weightedHolder_upper_power
import Theorems.Thm_O3_lpPower_nonneg


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {q : ℝ} (hq : 2 < q) {d : ℕ}
    (x h : Point d) (t : ℝ) (hzvec : x + t • h ≠ 0) :
    (2 - q) * linePower q x h t ^ (2 / q - 2) *
          linePowerPair q x h t ^ (2 : ℕ) +
        (q - 1) * linePower q x h t ^ (2 / q - 1) *
          weightedSquareSum q x h t ≤
      (q - 1) * (lpNorm q h) ^ (2 : ℕ) := by
  have hfirst :
      (2 - q) * linePower q x h t ^ (2 / q - 2) *
        linePowerPair q x h t ^ (2 : ℕ) ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith : 2 - q ≤ 0)
        (Real.rpow_nonneg (lpPower_nonneg q (x + t • h)) _))
      (sq_nonneg _)
  have hw := O3.Stage2RouteD.weightedHolder_upper_power hq
    (x + t • h) h hzvec
  change linePower q x h t ^ (2 / q - 1) *
      weightedSquareSum q x h t ≤ (lpNorm q h) ^ (2 : ℕ) at hw
  have hmul := mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ q - 1)
  linarith
end O3.Stage2RouteA
