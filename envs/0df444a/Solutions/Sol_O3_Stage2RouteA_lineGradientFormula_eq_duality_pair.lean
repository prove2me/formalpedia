-- Prove2me | solution 1 for O3.Stage2RouteA.lineGradientFormula_eq_duality_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:41.118865+00:00
-- url     : https://prove2.me/submissions/7c426c76-1634-4fc2-a724-cdbd2899cef1

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_lpPower_rpow_two_div_sub_one_eq
import Theorems.Thm_O3_lpNorm_pos_of_ne_zero


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {p : ℝ} (hp : p ≠ 0) {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : x + t • h ≠ 0) :
    lineGradientFormula p x h t = pairing (dualityMap p (x + t • h)) h := by
  have hnorm : lpNorm p (x + t • h) ≠ 0 :=
    (lpNorm_pos_of_ne_zero hz).ne'
  rw [lineGradientFormula, dualityMap, if_neg hnorm,
    linePower, lpPower_rpow_two_div_sub_one_eq hp hz, linePowerPair]
  unfold pairing powerDualityMap
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end O3.Stage2RouteA
