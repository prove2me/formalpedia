-- Prove2me | solution 1 for O3.Experimental.scalarJ_strongMonotone_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:59:04.385805+00:00
-- url     : https://prove2.me/submissions/1d0c7c0d-2aa9-4dcb-856b-d8a8aed252cd

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
import Theorems.Thm_O3_Experimental_scalarJ_nonneg
import Theorems.Thm_O3_Experimental_scalarJ_nonpos
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
open O3 O3.Experimental
namespace O3.Experimental
theorem _root_.solution {p u v : ℝ} (hp : 2 < p) (huv : v ≤ u) :
    (2 : ℝ) ^ (2 - p) * |u - v| ^ p ≤ (scalarJ p u - scalarJ p v) * (u - v) := by
  have hr : 1 ≤ p - 1 := by linarith
  have hc1 : (2 : ℝ) ^ (2 - p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  rcases le_total 0 v with hv | hv
  · have hu : 0 ≤ u := hv.trans huv
    rw [scalarJ_nonneg hp hu, scalarJ_nonneg hp hv, abs_of_nonneg (sub_nonneg.mpr huv)]
    have hpow := Real.add_rpow_le_rpow_add hv (sub_nonneg.mpr huv) hr
    have huvsum : v + (u - v) = u := by ring
    rw [huvsum] at hpow
    have hdiff : (u - v) ^ (p - 1) ≤ u ^ (p - 1) - v ^ (p - 1) := by linarith
    have hd0 : 0 ≤ u - v := sub_nonneg.mpr huv
    have hmul := mul_le_mul_of_nonneg_right hdiff hd0
    have hrpow : (u - v) ^ (p - 1) * (u - v) = (u - v) ^ p := by
      rw [← Real.rpow_add_one' hd0 (by linarith : p - 1 + 1 ≠ 0)]
      congr 1
      ring
    rw [hrpow] at hmul
    have hcpow := mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg hd0 p)
    calc
      2 ^ (2 - p) * (u - v) ^ p ≤ 1 * (u - v) ^ p := hcpow
      _ = (u - v) ^ p := one_mul _
      _ ≤ (u ^ (p - 1) - v ^ (p - 1)) * (u - v) := hmul
  · rcases le_total u 0 with hu | hu
    · have hnv : 0 ≤ -u := neg_nonneg.mpr hu
      have hv0 : v ≤ 0 := huv.trans hu
      rw [scalarJ_nonpos hp hu, scalarJ_nonpos hp hv0,
        abs_of_nonneg (sub_nonneg.mpr huv)]
      ring_nf
      have hpow := Real.add_rpow_le_rpow_add hnv (sub_nonneg.mpr huv) hr
      have hsum : -u + (u - v) = -v := by ring
      rw [hsum] at hpow
      have hdiff : (u - v) ^ (p - 1) ≤ (-v) ^ (p - 1) - (-u) ^ (p - 1) := by linarith
      have hd0 : 0 ≤ u - v := sub_nonneg.mpr huv
      have hmul := mul_le_mul_of_nonneg_right hdiff hd0
      have hrpow : (u - v) ^ (p - 1) * (u - v) = (u - v) ^ p := by
        rw [← Real.rpow_add_one' hd0 (by linarith : p - 1 + 1 ≠ 0)]
        congr 1
        ring
      rw [hrpow] at hmul
      ring_nf at hmul
      have hcpow := mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg hd0 p)
      have hcpow' : 2 ^ (2 - p) * (u - v) ^ p ≤ (u - v) ^ p := by
        simpa only [one_mul] using hcpow
      have hfinal := hcpow'.trans hmul
      ring_nf at hfinal
      linarith [hfinal]
    · have hu0 : 0 ≤ u := hu
      have hv0 : v ≤ 0 := hv
      rw [scalarJ_nonneg hp hu0, scalarJ_nonpos hp hv0,
        abs_of_nonneg (sub_nonneg.mpr huv)]
      let a : NNReal := ⟨u, hu0⟩
      let b : NNReal := ⟨-v, neg_nonneg.mpr hv0⟩
      have hnn := NNReal.rpow_add_le_mul_rpow_add_rpow a b (p := p - 1) hr
      have hcast : (↑((a + b) ^ (p - 1)) : ℝ) ≤
          ↑((2 : NNReal) ^ (p - 1 - 1) * (a ^ (p - 1) + b ^ (p - 1))) := by
        exact_mod_cast hnn
      simp only [NNReal.coe_rpow, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat] at hcast
      have hreal' : ((a : ℝ) + (b : ℝ)) ^ (p - 1) ≤
          (2 : ℝ) ^ (p - 2) * ((a : ℝ) ^ (p - 1) + (b : ℝ) ^ (p - 1)) := by
        convert hcast using 1
        ring_nf
      change (u + (-v)) ^ (p - 1) ≤
        (2 : ℝ) ^ (p - 2) * (u ^ (p - 1) + (-v) ^ (p - 1)) at hreal'
      have hreal : (u + (-v)) ^ (p - 1) ≤
          (2 : ℝ) ^ (p - 2) * (u ^ (p - 1) + (-v) ^ (p - 1)) := by
        exact hreal'
      have hd : u - v = u + (-v) := by ring
      rw [hd]
      have hd0 : 0 ≤ u + -v := add_nonneg hu0 (neg_nonneg.mpr hv0)
      have hcpos : 0 < (2 : ℝ) ^ (p - 2) := Real.rpow_pos_of_pos (by norm_num) _
      have hcancel :
          (2 : ℝ) ^ (2 - p) * (u + -v) ^ (p - 1) ≤
            u ^ (p - 1) + (-v) ^ (p - 1) := by
        have hinv : (2 : ℝ) ^ (2 - p) = ((2 : ℝ) ^ (p - 2))⁻¹ := by
          rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          congr 2
          ring
        rw [hinv, inv_mul_le_iff₀ hcpos]
        simpa [mul_comm] using hreal
      have hmul := mul_le_mul_of_nonneg_right hcancel hd0
      have hrpow : (u + -v) ^ (p - 1) * (u + -v) = (u + -v) ^ p := by
        rw [← Real.rpow_add_one' hd0 (by linarith : p - 1 + 1 ≠ 0)]
        congr 1
        ring
      rw [mul_assoc, hrpow] at hmul
      nlinarith
end O3.Experimental
