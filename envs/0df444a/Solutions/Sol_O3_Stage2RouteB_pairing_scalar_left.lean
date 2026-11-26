-- Prove2me | solution 1 for O3.Stage2RouteB.pairing_scalar_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:19.039415+00:00
-- url     : https://prove2.me/submissions/cde6121f-cc3e-4153-970d-ff14193f2d9b

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
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
theorem _root_.solution {d : ℕ} (r : ℝ) (a b : Point d) :
    pairing (fun i ↦ r * a i) b = r * pairing a b := by
  simp only [pairing, Finset.mul_sum, mul_assoc]
end O3.Stage2RouteB
