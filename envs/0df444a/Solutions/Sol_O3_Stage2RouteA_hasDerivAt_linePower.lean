-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_linePower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:33:53.005214+00:00
-- url     : https://prove2.me/submissions/2073511f-883d-4b82-960d-a0b823257072

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_abs_affine_rpow
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.Stage2RouteD.dualityMap_zero
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteA
namespace O3.Stage2RouteA
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    HasDerivAt (linePower p x h) (linePowerDerivative p x h t) t := by
  classical
  have hsum : HasDerivAt
      (fun s : ℝ ↦ ∑ i : Fin d, |x i + s * h i| ^ p)
      (∑ i : Fin d, p * |x i + t * h i| ^ (p - 2) * (x i + t * h i) * h i) t := by
    exact HasDerivAt.fun_sum (fun i _ ↦ hasDerivAt_abs_affine_rpow hp)
  convert hsum using 1 <;>
    first
    | rfl
    | simp only [linePowerDerivative, pairing, powerDualityMap,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
end O3.Stage2RouteA
