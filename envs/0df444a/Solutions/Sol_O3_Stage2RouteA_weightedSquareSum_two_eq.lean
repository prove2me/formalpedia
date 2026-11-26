-- Prove2me | solution 1 for O3.Stage2RouteA.weightedSquareSum_two_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:33:36.521337+00:00
-- url     : https://prove2.me/submissions/eac42946-9c38-46ee-93d2-e10579362fc8

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_lpNorm_sq_eq_lpPower_rpow

set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {d : ℕ} (x h : Point d) (t : ℝ) :
    weightedSquareSum 2 x h t = (lpNorm 2 h) ^ (2 : ℕ) := by
  rw [lpNorm_sq_eq_lpPower_rpow (by norm_num : (2 : ℝ) ≠ 0)]
  have hexp : (2 : ℝ) / 2 = 1 := by norm_num
  rw [hexp, Real.rpow_one]
  unfold weightedSquareSum lpPower
  apply Finset.sum_congr rfl
  intro i _
  norm_num
end O3.Stage2RouteA
