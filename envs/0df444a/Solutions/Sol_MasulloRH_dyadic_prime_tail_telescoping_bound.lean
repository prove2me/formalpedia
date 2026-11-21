-- Prove2me | solution 1 for MasulloRH.dyadic_prime_tail_telescoping_bound
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:39:05.873155+00:00
-- url     : https://prove2.me/submissions/657ddb31-3fcd-494d-b164-5e551c1f8ab4

-- Dyadic upper bound for the prime series using the elementary Chebyshev estimate.
import Mathlib
open ArithmeticFunction Finset
private theorem log_bound {x : ℝ} (hx : 196 ≤ x) : Real.log x ≤ (2/5)*Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hy : 14 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0.le).mpr (by linarith)
  have h := Real.log_le_sub_one_of_pos (div_pos (Real.sqrt_pos.mpr hx0) (by norm_num : (0:ℝ)<16))
  rw [Real.log_div (Real.sqrt_pos.mpr hx0).ne' (by norm_num), Real.log_sqrt hx0.le,
    show (16:ℝ)=2^4 by norm_num,Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [Real.log_two_lt_d9]


private theorem psi_upper (X : ℕ) (hX : 196 ≤ X) : Chebyshev.psi X ≤ (11/5:ℝ)*X := by
  have hx : (196:ℝ) ≤ X := by exact_mod_cast hX
  have h0 : 0 < (X:ℝ) := by linarith
  have hs := Real.sq_sqrt h0.le
  have hu := Chebyshev.psi_le (show 1 ≤ (X:ℝ) by linarith)
  rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hu
  have hlog2 := mul_le_mul_of_nonneg_right (show Real.log 2 ≤ 7/10 by linarith [Real.log_two_lt_d9]) h0.le
  have hlog2' := mul_le_mul_of_nonneg_right (show (69/100:ℝ) ≤ Real.log 2 by linarith [Real.log_two_gt_d9]) h0.le
  nlinarith [mul_le_mul_of_nonneg_left (log_bound hx) (Real.sqrt_nonneg (X:ℝ))]

theorem solution (X : ℕ) (hX : 196 ≤ X) :
    (∑ j ∈ Ioc X (2*X), (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
      7/(X:ℝ)^(3/2:ℝ) - 7/(2*(X:ℝ))^(3/2:ℝ) := by
  have hpos : 0 < (X:ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hd : (0:ℝ) < (X:ℝ)^(5/2:ℝ) := Real.rpow_pos_of_pos hpos _
  have hm : (∑ j ∈ Ioc X (2*X),vonMangoldt j) ≤ 22/5*(X:ℝ) := by
    have H := psi_upper (2*X) (by omega)
    have hsum : (∑ j ∈ Ioc X (2*X),vonMangoldt j) ≤ Chebyshev.psi (2*X:ℕ) := by
      simp only [Chebyshev.psi,Nat.floor_natCast]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc (Nat.zero_le X) le_rfl) (fun _ _ _ => vonMangoldt_nonneg)
    push_cast at H hsum
    linarith only [H,hsum]
  have hg : (∑ j ∈ Ioc X (2*X), (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))) ≤
      (22/5*(X:ℝ))/(X:ℝ)^(5/2:ℝ) := by
    apply le_trans _ (div_le_div_of_nonneg_right hm hd.le)
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro j hj
    have hxj : (X:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Ioc.mp hj).1.le
    exact (sub_le_self _ (by positivity)).trans (div_le_div_of_nonneg_left vonMangoldt_nonneg hd
      (Real.rpow_le_rpow hpos.le hxj (by norm_num)))
  apply hg.trans
  rw [show (5/2:ℝ)=3/2+1 by norm_num,Real.rpow_add_one hpos.ne',Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hpos.le]
  have h2 : (14/5:ℝ) ≤ (2:ℝ)^(3/2:ℝ) := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_one,←Real.sqrt_eq_rpow]
    have := (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 7/5) (by norm_num : (0:ℝ) ≤ 2)).mpr (by norm_num)
    linarith
  have hp := Real.rpow_pos_of_pos hpos (3/2:ℝ)
  have ht := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (3/2:ℝ)
  field_simp
  nlinarith only [mul_pos hp hpos,mul_le_mul_of_nonneg_right h2 (mul_pos hp hpos).le]
