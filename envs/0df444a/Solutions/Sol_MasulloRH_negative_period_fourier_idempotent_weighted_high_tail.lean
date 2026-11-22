-- Prove2me | solution 1 for MasulloRH.negative_period_fourier_idempotent_weighted_high_tail
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T14:45:27.26721+00:00
-- url     : https://prove2.me/submissions/f0adba98-f588-48b1-ae71-0d85c434425c

import Mathlib
open MeasureTheory Set Real
open scoped Interval

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (L A C D : ℝ) (hL : 0 < L) (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (r : ℕ) (V : ℝ → E) (m : ℝ → ℂ)
    (hV : ∀ t ∈ Icc (-L) 0, ‖V t‖ ≤ C*(1+|t|)^2)
    (hm : ∀ u, ‖m u‖ ≤ D/(1+|u|)^(r+2)) :
    let δ := 2*Real.pi/L
    let P := fun u : ℝ => (L⁻¹ : ℂ) • (∫ t in (-L)..0, Complex.exp (((-u*t : ℝ):ℂ)*Complex.I) • V t)
    let u := fun k : ℕ => A + k*δ
    let z := fun k : ℕ => ‖m (u k) • P (u k)‖ + ‖m (-(u k)) • P (-(u k))‖
    (∀ x t : ℝ, t ≤ 0 → exp (t+|x+t|-|x|)*(1+(x+t)^2)^2 ≤ (1+|t|)^4*(1+x^2)^2) ∧
    (∀ v, ‖P v‖ ≤ C*(1+L)^2) ∧ Summable z ∧
    (∑' k, z k) ≤ 2*D*C*(1+L)^2 * (1+δ)/(δ*(1+A)^(r+1)) := by
  intro δ P u z
  have hd : 0 < δ := by dsimp [δ]; positivity
  have physical (x t : ℝ) (ht : t ≤ 0) :
      exp (t+|x+t|-|x|)*(1+(x+t)^2)^2 ≤ (1+|t|)^4*(1+x^2)^2 := by
    have ht' := abs_add_le x t
    rw [abs_of_nonpos ht] at ht'
    have hex : exp (t+|x+t|-|x|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hp : 1+(x+t)^2 ≤ (1+|t|)^2*(1+x^2) := by
      rw [abs_of_nonpos ht]
      have h1 := mul_nonneg (neg_nonneg.mpr ht) (sq_nonneg (x+1))
      have h2 := sq_nonneg (t*x)
      nlinarith
    calc
      _ ≤ 1*(1+(x+t)^2)^2 := mul_le_mul_of_nonneg_right hex (sq_nonneg _)
      _ ≤ ((1+|t|)^2*(1+x^2))^2 := by rw [one_mul]; exact pow_le_pow_left₀ (by positivity) hp _
      _ = _ := by ring
  have proj (v : ℝ) : ‖P v‖ ≤ C*(1+L)^2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -L) (b := (0:ℝ)) (f := fun t : ℝ => Complex.exp (((-v*t : ℝ):ℂ)*Complex.I) • V t)
      (C := C*(1+L)^2) (by
        intro t ht
        rw [Set.uIoc_of_le (by linarith : -L ≤ 0)] at ht
        have ht' : t ∈ Icc (-L) 0 := ⟨ht.1.le,ht.2⟩
        have ab : |t| ≤ L := abs_le.mpr ⟨ht.1.le,ht.2.trans hL.le⟩
        rw [norm_smul,Complex.norm_exp_ofReal_mul_I,one_mul]
        exact (hV t ht').trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith : 1+|t| ≤ 1+L) 2) hC))
    rw [zero_sub,neg_neg,abs_of_pos hL] at hb
    simp only [P,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_of_pos hL]
    calc
      _ ≤ L⁻¹*(C*(1+L)^2*L) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hL.le)
      _ = _ := by field_simp
  let X := fun k : ℕ => 1+u k
  let H := 2*D*C*(1+L)^2
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have ux (k : ℕ) : A ≤ u k := by dsimp [u]; exact le_add_of_nonneg_right (by positivity)
  have hx (k : ℕ) : 0 < X k := by dsimp [X]; linarith [ux k]
  have adj (k : ℕ) : X (k+1) = X k+δ := by dsimp [X,u]; push_cast; ring
  have point (v : ℝ) : ‖m v • P v‖ ≤ (D/(1+|v|)^(r+2))*(C*(1+L)^2) := by
    rw [norm_smul]
    exact mul_le_mul (hm v) (proj v) (norm_nonneg _) (by positivity)
  have zbound (k : ℕ) : z k ≤ H/(X k)^(r+2) := by
    have h1 := point (u k)
    have h2 := point (-(u k))
    rw [abs_neg] at h2
    rw [abs_of_nonneg (hA.trans (ux k))] at h1 h2
    dsimp [z,H,X]
    apply (add_le_add h1 h2).trans_eq
    ring
  let Y := fun k : ℕ => H*(1+δ)/(δ*(1+A)^r) / X k
  have ystep (k : ℕ) : z k ≤ Y k - Y (k+1) := by
    apply (zbound k).trans
    have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1+A) (show 1+A ≤ X k by dsimp [X]; linarith [ux k]) r
    have x2 := sq_pos_of_pos (hx k)
    have hxa : (1+A)^r*(X k)^2 ≤ (X k)^(r+2) := by
      rw [pow_add]
      exact mul_le_mul_of_nonneg_right hpow x2.le
    have lop : H/(X k)^(r+2) ≤ H/((1+A)^r*(X k)^2) :=
      div_le_div_of_nonneg_left hH (by positivity) hxa
    apply lop.trans
    dsimp [Y]; rw [adj]
    have hpos : 0 < 1+A := by linarith
    have xx := hx k
    have dx : 0 < X k+δ := by positivity
    have ratio := mul_nonneg (sub_nonneg.mpr (show 1 ≤ X k by dsimp [X]; linarith [ux k])) hd.le
    have core : 1/(X k)^2 ≤ (1+δ)/δ * (1/X k - 1/(X k+δ)) := by
      field_simp [xx.ne',dx.ne',hd.ne']
      nlinarith [mul_nonneg xx.le ratio]
    have hh := mul_le_mul_of_nonneg_left core (show 0 ≤ H/(1+A)^r by positivity)
    convert hh using 1 <;> ring
  have partBound (N : ℕ) : (∑ k ∈ Finset.range N, z k) ≤ Y 0-Y N := by
    induction N with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; linarith [ystep n]
  have bound (N : ℕ) : (∑ k ∈ Finset.range N, z k) ≤ 2*D*C*(1+L)^2*(1+δ)/(δ*(1+A)^(r+1)) := by
    have non : 0 ≤ Y N := by dsimp [Y]; have := hx N; positivity
    have init : Y 0 = 2*D*C*(1+L)^2*(1+δ)/(δ*(1+A)^(r+1)) := by
      simp only [Y,H,X,u,Nat.cast_zero,zero_mul,add_zero,pow_succ,div_div,mul_assoc]
    linarith [partBound N]
  have hz (n : ℕ) : 0 ≤ z n := by dsimp [z]; positivity
  exact ⟨physical,proj,summable_of_sum_range_le hz bound,Real.tsum_le_of_sum_range_le hz bound⟩
