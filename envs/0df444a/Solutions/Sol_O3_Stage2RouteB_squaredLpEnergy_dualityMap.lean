-- Prove2me | solution 1 for O3.Stage2RouteB.squaredLpEnergy_dualityMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:44.645126+00:00
-- url     : https://prove2.me/submissions/8e0273ba-6a6c-4581-b935-affc2458490d

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_squaredLpEnergy_eq_quadraticRegularizer
import Theorems.Thm_O3_Stage2RouteB_lpNorm_dualityMap
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_one_lt_conjugateExponent
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
    squaredLpEnergy (conjugateExponent p) (dualityMap p x) = squaredLpEnergy p x := by
  rw [squaredLpEnergy_eq_quadraticRegularizer
    (lt_trans zero_lt_one (one_lt_conjugateExponent hp))]
  rw [squaredLpEnergy_eq_quadraticRegularizer (by linarith : 0 < p)]
  simp only [quadraticRegularizer, sub_zero]
  rw [lpNorm_dualityMap hp]
end O3.Stage2RouteB
