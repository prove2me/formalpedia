-- Prove2me | solution 1 for O3.Stage2RouteB.lpNorm_rpow_eq_lpPower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:35.299287+00:00
-- url     : https://prove2.me/submissions/73d2e9ef-ec0e-4c05-bf8d-960de698e159

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_lpPower_nonneg


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : p ≠ 0) {d : ℕ} (x : Point d) :
    (lpNorm p x) ^ p = lpPower p x := by
  unfold lpNorm
  rw [one_div]
  exact Real.rpow_inv_rpow (lpPower_nonneg p x) hp
end O3.Stage2RouteB
