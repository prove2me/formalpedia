-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_linePowerPair_of_coordinates_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:34:33.968596+00:00
-- url     : https://prove2.me/submissions/328accce-f724-402f-9477-19d4899bd830

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_scalarJ_affine
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
theorem _root_.solution {p : ℝ} {d : ℕ}
    (x h : Point d) (t : ℝ) (hz : ∀ i : Fin d, (x + t • h) i ≠ 0) :
    HasDerivAt (linePowerPair p x h)
      ((p - 1) * weightedSquareSum p x h t) t := by
  classical
  have hsum : HasDerivAt
      (fun s : ℝ ↦ ∑ i : Fin d,
        O3.Experimental.scalarJ p (x i + s * h i) * h i)
      (∑ i : Fin d, ((p - 1) * |x i + t * h i| ^ (p - 2) * h i) * h i) t := by
    exact HasDerivAt.fun_sum fun i _ ↦
      (hasDerivAt_scalarJ_affine (p := p) (a := x i) (b := h i) (t := t)
        (by simpa using hz i)).mul_const (h i)
  have hderiv : (∑ i : Fin d,
      ((p - 1) * |x i + t * h i| ^ (p - 2) * h i) * h i) =
      (p - 1) * weightedSquareSum p x h t := by
    rw [weightedSquareSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_two]
    ring
  rw [← hderiv]
  change HasDerivAt
    (fun s : ℝ ↦ ∑ i : Fin d,
      O3.Experimental.scalarJ p (x i + s * h i) * h i)
    (∑ i : Fin d, ((p - 1) * |x i + t * h i| ^ (p - 2) * h i) * h i) t
  exact hsum
end O3.Stage2RouteA
