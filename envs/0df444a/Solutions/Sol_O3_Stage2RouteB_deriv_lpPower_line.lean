-- Prove2me | solution 1 for O3.Stage2RouteB.deriv_lpPower_line
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:27:52.888187+00:00
-- url     : https://prove2.me/submissions/83d30130-0110-4067-bee0-5492711716c5

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
theorem _root_.solution {p : ℝ} (hp : 1 < p) {d : ℕ}
    (x h : Point d) (t : ℝ) :
    deriv (fun s : ℝ ↦ lpPower p (fun i ↦ x i + s * h i)) t =
      p * pairing (powerDualityMap p (fun i ↦ x i + t * h i)) h := by
  simp only [lpPower, pairing, powerDualityMap]
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset (Fin d))) (fun i _ ↦
    ((hasDerivAt_abs_rpow (x i + t * h i) hp).comp t
      ((hasDerivAt_const t (x i)).add ((hasDerivAt_id t).mul_const (h i)))))
  have hd := hsum.deriv
  have hfun : (fun s : ℝ ↦ ∑ i, |x i + s * h i| ^ p) =
      ∑ i, (fun r : ℝ ↦ |r| ^ p) ∘
        ((fun _ : ℝ ↦ x i) + fun s : ℝ ↦ id s * h i) := by
    funext s
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Function.comp_apply, Pi.add_apply, id_eq]
  rw [hfun]
  simpa only [zero_add, one_mul, Finset.mul_sum, mul_assoc] using hd
end O3.Stage2RouteB
