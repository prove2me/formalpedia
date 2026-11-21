-- Prove2me | solution 1 for MasulloRH.prime_tail_reserve_to_four_mul
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:21:31.655176+00:00
-- url     : https://prove2.me/submissions/4be042be-bfe6-409f-b895-42a0c14d9ba6

import Mathlib
open ArithmeticFunction Finset
-- The interval decomposition and pointwise weighting follow marozols's
-- explicit verification-height proof. The sharper interval and constants are new.
private theorem log_bound {x : ℝ} (hx : 196 ≤ x) : Real.log x ≤ (2/5)*Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hy : 14 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).mpr (by linarith)
  have h := Real.log_le_sub_one_of_pos (div_pos (Real.sqrt_pos.mpr hx0) (by norm_num : (0:ℝ)<16))
  rw [Real.log_div (Real.sqrt_pos.mpr hx0).ne' (by norm_num), Real.log_sqrt hx0.le,
    show (16:ℝ)=2^4 by norm_num,Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [Real.log_two_lt_d9]

private theorem interval_mangoldt_mass (X : ℕ) (hX : 196 ≤ X) :
    (2/5:ℝ)*X ≤ ∑ j ∈ Ioc X (4*X), vonMangoldt j := by
  have hx : (196:ℝ) ≤ X := by exact_mod_cast hX
  have h0 : 0 < (X:ℝ) := by linarith
  have hy : 14 ≤ Real.sqrt X := (Real.le_sqrt (by norm_num) h0.le).mpr (by linarith)
  have hs := Real.sq_sqrt h0.le
  have hu := Chebyshev.psi_le (show 1 ≤ (X:ℝ) by linarith)
  rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hu
  have hlog2 := mul_le_mul_of_nonneg_right (show Real.log 2 ≤ 7/10 by linarith [Real.log_two_lt_d9]) h0.le
  have hlog2' := mul_le_mul_of_nonneg_right (show (69/100:ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]) h0.le
  have hupper : Chebyshev.psi X ≤ (11/5:ℝ)*X := by
    nlinarith [mul_le_mul_of_nonneg_left (log_bound hx) (Real.sqrt_nonneg (X:ℝ))]
  have hl := Real.log_le_log (by positivity : 0<4*(X:ℝ)+1)
    (show 4*(X:ℝ)+1 ≤ 5*X by linarith)
  rw [Real.log_mul (by norm_num) h0.ne'] at hl
  have hsmall : Real.log (4*(X:ℝ)+1) ≤ (X:ℝ)/10 := by
    nlinarith [log_bound hx, Real.log_five_lt_d9,
      mul_nonneg (Real.sqrt_nonneg (X:ℝ)) (sub_nonneg.mpr hy)]
  have hd := Chebyshev.psi_ge (4*X)
  have he : Chebyshev.psi X + ∑ j ∈ Ioc X (4*X), vonMangoldt j = Chebyshev.psi (4*X:ℕ) := by
    simp only [Chebyshev.psi,Nat.floor_natCast]
    rw [←sum_union (Ioc_disjoint_Ioc_of_le (le_refl X)), Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le X) (by omega)]
  push_cast at he hd
  linarith
theorem solution (X : ℕ) (hX : 196 ≤ X) :
    1/(128*(X:ℝ)^(3/2:ℝ)) ≤ ∑ j ∈ Ioc X (4*X),
      (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ)) := by
  have hXR : (196:ℝ) ≤ X := by exact_mod_cast hX
  have hx0 : 0 < (X:ℝ) := by linarith
  have h16 : (4:ℝ)^(5/2:ℝ) = 32 := by
    rw [show (5/2:ℝ)=2+1/2 by norm_num,Real.rpow_add (by norm_num),
      ←Real.sqrt_eq_rpow, Real.rpow_ofNat]
    norm_num
  have ha : (4*(X:ℝ))^(5/2:ℝ) = 32*((X:ℝ)^(3/2:ℝ))*(X:ℝ) := by
    rw [Real.mul_rpow (by norm_num) hx0.le,h16,
      show (5/2:ℝ)=3/2+1 by norm_num,Real.rpow_add_one hx0.ne']; ring
  have he : 1/(128*(X:ℝ)^(3/2:ℝ)) = ((2/5:ℝ)*X)/((8/5)*(4*(X:ℝ))^(5/2:ℝ)) := by
    rw [ha]; field_simp [hx0.ne',(Real.rpow_pos_of_pos hx0 (3/2:ℝ)).ne']; ring
  rw [he]
  apply (div_le_div_of_nonneg_right (interval_mangoldt_mass X hX) (by positivity)).trans
  rw [sum_div]
  apply sum_le_sum
  intro j hj
  obtain ⟨hjlo,hjhi⟩ := mem_Ioc.mp hj
  have hj0 : 0 < (j:ℝ) := by exact_mod_cast (show 0<j by omega)
  have hjr : (j:ℝ) ≤ 4*(X:ℝ) := by exact_mod_cast hjhi
  have hs : (4:ℝ) ≤ Real.sqrt j := (Real.le_sqrt (by norm_num) hj0.le).mpr
    (by exact_mod_cast (show 4^2≤j by omega))
  have hp := Real.rpow_le_rpow hj0.le hjr (by norm_num : 0 ≤ (5/2:ℝ))
  have hm : (j:ℝ)^(5/2:ℝ) * Real.sqrt j = (j:ℝ)^3 := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hj0,show (5/2:ℝ)+1/2=3 by norm_num,Real.rpow_ofNat]
  apply (div_le_div_of_nonneg_left (vonMangoldt_nonneg (n:=j)) (by positivity) (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤8/5))).trans
  rw [Real.rpow_ofNat,←hm]
  field_simp [(Real.rpow_pos_of_pos hj0 (5/2:ℝ)).ne',(Real.sqrt_pos.mpr hj0).ne']
  nlinarith [vonMangoldt_nonneg (n:=j), mul_nonneg (vonMangoldt_nonneg (n:=j)) (sub_nonneg.mpr hs)]
