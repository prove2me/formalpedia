-- Prove2me | solution 1 for O3.Stage2RouteA.hasDerivAt_linePowerPair_above_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:35:35.364832+00:00
-- url     : https://prove2.me/submissions/55a54601-1981-4368-b5a5-771702fc9c6e

import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage2RouteA
import Theorems.Thm_O3_Stage2RouteA_hasDerivAt_scalarJ_above_two
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
theorem _root_.solution {q : ℝ} (hq : 2 < q) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    HasDerivAt (linePowerPair q x h)
      ((q - 1) * weightedSquareSum q x h t) t := by
  classical
  have hsum : HasDerivAt
      (fun s : ℝ ↦ ∑ i : Fin d,
        O3.Experimental.scalarJ q (x i + s * h i) * h i)
      (∑ i : Fin d, ((q - 1) * |x i + t * h i| ^ (q - 2) * h i) * h i) t := by
    apply HasDerivAt.fun_sum
    intro i _
    have haff : HasDerivAt (fun s : ℝ ↦ x i + s * h i) (h i) t := by
      convert ((hasDerivAt_id t).mul_const (h i)).const_add (x i) using 1 <;>
        first | rfl | ring
    have hc := (hasDerivAt_scalarJ_above_two (q := q)
      (u := x i + t * h i) hq).comp t haff
    exact hc.mul_const (h i)
  have hderiv : (∑ i : Fin d,
      ((q - 1) * |x i + t * h i| ^ (q - 2) * h i) * h i) =
      (q - 1) * weightedSquareSum q x h t := by
    rw [weightedSquareSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_two]
    ring
  rw [← hderiv]
  change HasDerivAt
    (fun s : ℝ ↦ ∑ i : Fin d,
      O3.Experimental.scalarJ q (x i + s * h i) * h i)
    (∑ i : Fin d, ((q - 1) * |x i + t * h i| ^ (q - 2) * h i) * h i) t
  exact hsum
end O3.Stage2RouteA
