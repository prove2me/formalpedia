-- Prove2me | solution 1 for O3.Stage2RouteA.weightedTerm_le_hessianFormula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:33:28.276519+00:00
-- url     : https://prove2.me/submissions/9f72c64c-894b-4fa6-9f50-9507683bf181

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_lpPower_nonneg


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {p : ℝ} (hp2 : p ≤ 2) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    (p - 1) * linePower p x h t ^ (2 / p - 1) *
        weightedSquareSum p x h t ≤
      (2 - p) * linePower p x h t ^ (2 / p - 2) *
          linePowerPair p x h t ^ (2 : ℕ) +
        (p - 1) * linePower p x h t ^ (2 / p - 1) *
          weightedSquareSum p x h t := by
  have hfirst : 0 ≤
      (2 - p) * linePower p x h t ^ (2 / p - 2) *
        linePowerPair p x h t ^ (2 : ℕ) := by
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr hp2)
        (Real.rpow_nonneg (lpPower_nonneg p (x + t • h)) (2 / p - 2)))
      (sq_nonneg (linePowerPair p x h t))
  linarith
end O3.Stage2RouteA
