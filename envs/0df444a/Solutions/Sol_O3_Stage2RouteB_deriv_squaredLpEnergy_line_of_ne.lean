-- Prove2me | solution 1 for O3.Stage2RouteB.deriv_squaredLpEnergy_line_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:24:52.134374+00:00
-- url     : https://prove2.me/submissions/899fd2bc-4789-46ab-805d-e6238c697bb9

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_pairing_dualityMap_eq_powerSum_factor
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_pos_of_ne_zero
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
    (x h : Point d) (t : ℝ) (hxt : (fun i ↦ x i + t * h i) ≠ 0) :
    deriv (fun s : ℝ ↦ squaredLpEnergy p (fun i ↦ x i + s * h i)) t =
      pairing (dualityMap p (fun i ↦ x i + t * h i)) h := by
  let z : Point d := fun i ↦ x i + t * h i
  have hS : 0 < lpPower p z := lpPower_pos_of_ne_zero hxt
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset (Fin d))) (fun i _ ↦
    ((hasDerivAt_abs_rpow (x i + t * h i) hp).comp t
      ((hasDerivAt_const t (x i)).add ((hasDerivAt_id t).mul_const (h i)))))
  have hsumAt : (∑ i, ((fun r : ℝ ↦ |r| ^ p) ∘
      ((fun _ : ℝ ↦ x i) + fun s : ℝ ↦ id s * h i)) t) = lpPower p z := by
    simp only [Function.comp_apply, Pi.add_apply, id_eq, lpPower, z]
  have hrawpos : 0 < (∑ i, (fun r : ℝ ↦ |r| ^ p) ∘
      ((fun _ : ℝ ↦ x i) + fun s : ℝ ↦ id s * h i)) t := by
    rw [Finset.sum_apply, hsumAt]
    exact hS
  have hpow := hsum.rpow_const (p := 2 / p) (Or.inl hrawpos.ne')
  have hscaled := hpow.const_mul (1 / 2 : ℝ)
  have hd := hscaled.deriv
  have hfun : (fun s : ℝ ↦ squaredLpEnergy p (fun i ↦ x i + s * h i)) =
      fun s : ℝ ↦ (1 / 2 : ℝ) *
        ((∑ i, ((fun r : ℝ ↦ |r| ^ p) ∘
          ((fun _ : ℝ ↦ x i) + fun u : ℝ ↦ id u * h i)) s) ^ (2 / p)) := by
    funext s
    simp only [squaredLpEnergy, lpPower, Function.comp_apply, Pi.add_apply, id_eq]
  rw [hfun]
  rw [pairing_dualityMap_eq_powerSum_factor (by linarith : 0 < p) hxt h]
  rw [← hsumAt]
  convert hd using 1
  · congr 1
    funext s
    congr 2
    rw [Finset.sum_apply]
  · simp only [pairing, powerDualityMap, zero_add, one_mul]
    rw [show (∑ i, p * |x i + t * h i| ^ (p - 2) * (x i + t * h i) * h i) =
        p * (∑ i, |x i + t * h i| ^ (p - 2) * (x i + t * h i) * h i) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    field_simp
    rw [Finset.sum_apply]
    simp only [Function.comp_apply, Pi.add_apply, id_eq]
    rw [show (∑ i, |x i + t * h i| ^ p) = (∑ i, |t * h i + x i| ^ p) by
      apply Finset.sum_congr rfl
      intro i _
      congr 2
      ring]
    ring_nf
end O3.Stage2RouteB
