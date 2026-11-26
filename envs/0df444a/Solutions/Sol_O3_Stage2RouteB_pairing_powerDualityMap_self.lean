-- Prove2me | solution 1 for O3.Stage2RouteB.pairing_powerDualityMap_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:58.220262+00:00
-- url     : https://prove2.me/submissions/f334f64f-b190-4fdb-91a6-3356783c7a9d

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_coordinate_power_identity
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ} (x : Point d) :
    pairing (powerDualityMap p x) x = lpPower p x := by
  simp only [pairing, powerDualityMap, lpPower]
  apply Finset.sum_congr rfl
  intro i _
  exact coordinate_power_identity hp
end O3.Stage2RouteB
