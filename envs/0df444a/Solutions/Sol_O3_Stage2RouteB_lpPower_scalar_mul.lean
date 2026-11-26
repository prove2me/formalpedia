-- Prove2me | solution 1 for O3.Stage2RouteB.lpPower_scalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:52.418747+00:00
-- url     : https://prove2.me/submissions/36e8a959-4270-43c8-881b-a6948e7e2282

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
theorem _root_.solution {p a : ℝ} {d : ℕ} (h : Point d) :
    lpPower p (fun i ↦ a * h i) = |a| ^ p * lpPower p h := by
  simp only [lpPower, abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg _),
    Finset.mul_sum]
end O3.Stage2RouteB
