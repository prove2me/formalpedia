-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.det_B_eq_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:51:21.533336+00:00
-- url     : https://prove2.me/submissions/24c16071-bcd0-41dc-a172-764e7f868bc0

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_R_sub_bI_isUnit
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_Construction_B_R__form_nat_e28fa09a307e
import Theorems.Thm_GroupTheoreticShannonCapacity_Construction_det_ratio_eq_p_real
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_det_xR__add_yI_9d0b1d30422b

section
namespace GroupTheoreticShannonCapacity.Construction
open Matrix
private lemma det_B_eq_p_nat (n k b r s : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (hd : (r : ℤ) + (k : ℤ) * (b : ℤ) ^ n ≠ 0) :
    (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).det = p n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) := by
  -- Use B_Rα_form_nat to get the factorization
  have hB_form := B_Rα_form_nat n k b r s hn hk hb hd
  set R := MAlpha.Rα n ((r : ℝ) / (k : ℝ))
  -- Step 1: RingHom.map_det: f(M.det) = (f.mapMatrix M).det
  have hmap_det : (algebraMap ℚ ℝ) (matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).det =
      ((matrixB n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ)).map (↑· : ℚ → ℝ)).det := by
    rw [RingHom.map_det (algebraMap ℚ ℝ) _]; rfl
  -- Now use hB_form: B.map = (s•R - a•I) * (R - b•I)⁻¹
  rw [hB_form] at hmap_det
  -- Step 2: Compute det(A * B⁻¹) = det(A) * det(B⁻¹)
  have hR_unit := R_sub_bI_isUnit n k b r hn hk hd
  rw [Matrix.det_mul] at hmap_det
  -- det(B⁻¹) = Ring.inverse(det B) = (det B)⁻¹
  have h_unit_det := (Matrix.isUnit_iff_isUnit_det _).mp hR_unit
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at hmap_det
  -- Step 3: Use det_xRα_add_yI for numerator
  have hdet_num : ((s : ℝ) • R - (a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ) • 1).det =
      (-(s : ℝ))^n * ((r : ℝ) / (k : ℝ)) + (-(a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ))^n := by
    have h :=
      MAlpha.det_xRα_add_yI n hn (s : ℝ) (-(a n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) : ℝ)) ((r : ℝ) / (k : ℝ))
    convert h using 1; rw [sub_eq_add_neg, neg_smul]
  -- Step 4: Use det_xRα_add_yI for denominator
  have hdet_denom : (R - (b : ℝ) • 1).det =
      (-1 : ℝ)^n * ((r : ℝ) / (k : ℝ)) + (-(b : ℝ))^n := by
    have h := MAlpha.det_xRα_add_yI n hn 1 (-(b : ℝ)) ((r : ℝ) / (k : ℝ))
    convert h using 1; rw [sub_eq_add_neg, neg_smul, one_smul]
  rw [hdet_num, hdet_denom] at hmap_det
  -- Step 5: Apply det_ratio_eq_p_real
  have hk_ne : (k : ℤ) ≠ 0 := by omega
  have hratio := det_ratio_eq_p_real n (k:ℤ) (b:ℤ) (r:ℤ) (s:ℤ) hd hk_ne
  simp only at hratio; rw [div_eq_mul_inv] at hratio
  -- Match the forms using convert
  rw [← (algebraMap ℚ ℝ).injective.eq_iff]
  convert hratio using 1
  · simpa only [Int.cast_natCast] using hmap_det
  · rfl
section Tests
example : a 2 1 2 1 0 = 5 := by decide
example : p 2 1 2 1 0 = 5 := by
  simp only [p, a]
  norm_num
example : q 2 1 2 1 0 = 2 := by
  simp only [q, a]
  norm_num
example : p 2 1 2 1 0 = q 2 1 2 1 0 * 0 + 1 * (a 2 1 2 1 0)^(2-1) := by
  simp only [p, q, a]
  norm_num
example : p 2 1 2 1 0 * 2 = q 2 1 2 1 0 * (a 2 1 2 1 0) - 1 * 0^(2-1) := by
  simp only [p, q, a]
  norm_num
end Tests
end GroupTheoreticShannonCapacity.Construction
end

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
theorem _root_.solution (n : ℕ) (k b r s : ℤ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hb : 1 ≤ b) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (matrixB n k b r s).det = p n k b r s := by
  -- With k ≥ 1, b ≥ 1, r ≥ 0, the denominator r + k * b^n is always positive
  have hd : r + k * b ^ n ≠ 0 := by
    have hpos : 0 < k * b ^ n := by positivity
    omega
  -- Reduce to natural numbers
  have hk_nat : 1 ≤ k.natAbs := by omega
  have hb_nat : 1 ≤ b.natAbs := by omega
  have hk_eq : (k.natAbs : ℤ) = k := Int.natAbs_of_nonneg (by omega)
  have hb_eq : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg (by omega)
  have hr_eq : (r.natAbs : ℤ) = r := Int.natAbs_of_nonneg hr
  have hs_eq : (s.natAbs : ℤ) = s := Int.natAbs_of_nonneg hs
  have hd' : (r.natAbs : ℤ) + (k.natAbs : ℤ) * (b.natAbs : ℤ) ^ n ≠ 0 := by
    rw [hr_eq, hk_eq, hb_eq]; exact hd
  -- Apply det_B_eq_p_nat
  calc (matrixB n k b r s).det
      = (matrixB n (k.natAbs : ℤ) (b.natAbs : ℤ) (r.natAbs : ℤ) (s.natAbs : ℤ)).det := by
          simp only [hk_eq, hb_eq, hr_eq, hs_eq]
    _ = p n (k.natAbs : ℤ) (b.natAbs : ℤ) (r.natAbs : ℤ) (s.natAbs : ℤ) :=
          det_B_eq_p_nat n k.natAbs b.natAbs r.natAbs s.natAbs hn hk_nat hb_nat hd'
    _ = p n k b r s := by simp only [hk_eq, hb_eq, hr_eq, hs_eq]
end GroupTheoreticShannonCapacity.Construction
