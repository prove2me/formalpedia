-- Prove2me | solution 1 for LanglandsTunnell.integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/87a2c2b9-adab-5007-9cf6-21dadaed6141

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.MellinTransform
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Complex

noncomputable section

namespace HermiteC1

open Real Set MeasureTheory

theorem integrableOn_Iic_of_comp_neg' {E : Type*} [NormedAddCommGroup E] (F : ℝ → E)
    (hF : IntegrableOn (fun t => F (-t)) (Ioi 0)) : IntegrableOn F (Iic 0) := by
  have h' : IntegrableOn F (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_zero] using hF
  exact h'.congr_set_ae Iio_ae_eq_Iic.symm

theorem integrable_of_Ioi_of_comp_neg {E : Type*} [NormedAddCommGroup E] (F : ℝ → E)
    (h1 : IntegrableOn F (Ioi 0)) (h2 : IntegrableOn (fun t => F (-t)) (Ioi 0)) : Integrable F := by
  have h := (integrableOn_Iic_of_comp_neg' F h2).union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at h

def J (k : ℕ) : ℝ := ∫ u : ℝ, u ^ k * rexp (-(Real.pi * u ^ 2))

theorem integrable_pow_gauss (k : ℕ) : Integrable (fun u : ℝ => u ^ k * rexp (-(Real.pi * u ^ 2))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos
    (show (-1 : ℝ) < (k : ℝ) by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Real.rpow_natCast, neg_mul]

theorem J_odd (r : ℕ) : J (2 * r + 1) = 0 := by
  unfold J
  have h := Measure.integral_comp_mul_left (fun u : ℝ => u ^ (2 * r + 1) * rexp (-(Real.pi * u ^ 2))) (-1)
  simp only [inv_neg, inv_one, abs_neg, abs_one, one_smul] at h
  have h2 : (fun x : ℝ => (-1 * x) ^ (2 * r + 1) * rexp (-(Real.pi * (-1 * x) ^ 2))) =
      fun x => -(x ^ (2 * r + 1) * rexp (-(Real.pi * x ^ 2))) := by
    funext x
    rw [neg_one_mul, neg_pow, neg_sq, Odd.neg_one_pow ⟨r, rfl⟩]
    ring
  rw [h2, integral_neg] at h
  linarith

theorem factorial_two_mul (r : ℕ) :
    ((2 * r).factorial : ℝ) = 2 ^ r * (r.factorial : ℝ) * ((2 * r - 1).doubleFactorial : ℝ) := by
  rcases r with _ | k
  · simp
  · have h1 : (2 * (k + 1)).factorial = (2 * (k + 1)).doubleFactorial * (2 * k + 1).doubleFactorial := by
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by ring]
      exact Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega, h1, Nat.doubleFactorial_two_mul]
    push_cast
    ring

theorem J_even (r : ℕ) : J (2 * r) = ((2 * r).factorial : ℝ) / ((r.factorial : ℝ) * (4 * Real.pi) ^ r) := by
  unfold J
  have h1 : (fun u : ℝ => u ^ (2 * r) * rexp (-(Real.pi * u ^ 2))) =
      fun u => (fun x : ℝ => x ^ (2 * r) * rexp (-(Real.pi * x ^ 2))) |u| := by
    funext u; simp only [pow_mul, sq_abs]
  rw [h1, integral_comp_abs (f := fun x : ℝ => x ^ (2 * r) * rexp (-(Real.pi * x ^ 2)))]
  have h2 := integral_rpow_mul_exp_neg_mul_rpow two_pos (q := ((2 * r : ℕ) : ℝ))
    (by have := Nat.cast_nonneg (α := ℝ) (2 * r); linarith) Real.pi_pos
  have h3 : ∫ x in Ioi (0:ℝ), x ^ (2 * r) * rexp (-(Real.pi * x ^ 2)) =
      Real.pi ^ (-(((2 * r : ℕ) : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma ((((2 * r : ℕ) : ℝ) + 1) / 2) := by
    rw [← h2]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [Real.rpow_natCast, Real.rpow_two, neg_mul]
  rw [h3]
  have h4 : (((2 * r : ℕ) : ℝ) + 1) / 2 = (r : ℝ) + 1 / 2 := by push_cast; ring
  have h5 : -(((2 * r : ℕ) : ℝ) + 1) / 2 = -(1 / 2) - (r : ℝ) := by push_cast; ring
  rw [h4, h5, Real.Gamma_nat_add_half, Real.rpow_sub Real.pi_pos, Real.rpow_neg Real.pi_pos.le, Real.rpow_natCast,
    Real.sqrt_eq_rpow, factorial_two_mul]
  have hπ : (Real.pi : ℝ) ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  have hπ0 : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
  have h4π : (4 * Real.pi) ^ r = 2 ^ r * 2 ^ r * Real.pi ^ r := by
    rw [mul_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
  rw [h4π]
  field_simp

theorem integral_gauss_mul_I_pow (k : ℕ) (c : ℂ) :
    ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * ((Complex.I * (u : ℂ)) ^ k * c) =
      Complex.I ^ k * c * (J k : ℂ) := by
  unfold J
  rw [← integral_complex_ofReal, ← integral_const_mul]
  congr 1; funext u
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, mul_pow]
  ring

theorem integrable_term (k : ℕ) (c : ℂ) :
    Integrable (fun u : ℝ => (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * ((Complex.I * (u : ℂ)) ^ k * c)) := by
  have h0 : Integrable (fun u : ℝ => (((u ^ k * rexp (-(Real.pi * u ^ 2))) : ℝ) : ℂ)) :=
    (integrable_pow_gauss k).ofReal
  have h := h0.const_mul (Complex.I ^ k * c)
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, mul_pow]
  ring

theorem filter_even_range (m : ℕ) :
    (Finset.range (m + 1)).filter (fun k => Even k) = (Finset.range (m / 2 + 1)).image (fun r => 2 * r) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hk, ⟨r, hr⟩⟩
    exact ⟨r, by omega, by omega⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨by omega, ⟨r, by ring⟩⟩

end HermiteC1

open HermiteC1 in
theorem solution (t : ℝ) (m : ℕ) :
    ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * (((t : ℝ) : ℂ) + Complex.I * (u : ℂ)) ^ m =
      ∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            ((t : ℝ) : ℂ) ^ (m - 2 * r) := by
  classical

  have hexp : ∀ u : ℝ, (((t : ℝ) : ℂ) + Complex.I * (u : ℂ)) ^ m =
      ∑ k ∈ Finset.range (m + 1), (Complex.I * (u : ℂ)) ^ k * (((t : ℝ) : ℂ) ^ (m - k) * ((m.choose k : ℕ) : ℂ)) := by
    intro u
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hexp, Finset.mul_sum]
  rw [integral_finsetSum _ (fun k _ => integrable_term k _)]
  simp_rw [integral_gauss_mul_I_pow]

  have hodd : ∀ k ∈ Finset.range (m + 1),
      Complex.I ^ k * (((t : ℝ) : ℂ) ^ (m - k) * ((m.choose k : ℕ) : ℂ)) * (J k : ℂ) ≠ 0 → Even k := by
    intro k _ hk
    by_contra hko
    obtain ⟨r, rfl⟩ := Nat.not_even_iff_odd.mp hko
    apply hk
    rw [J_odd r]
    simp
  rw [← Finset.sum_filter_of_ne hodd, filter_even_range,
    Finset.sum_image (fun a _ b _ (h : 2 * a = 2 * b) => by omega)]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrm : 2 * r ≤ m := by
    have := Finset.mem_range.mp hr; omega
  rw [J_even r, pow_mul, Complex.I_sq]

  have hchoose : ((m.choose (2 * r) : ℕ) : ℂ) * ((2 * r).factorial : ℂ) * ((m - 2 * r).factorial : ℂ) =
      (m.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hrm
  have hf1 : ((2 * r).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf2 : ((m - 2 * r).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hf3 : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  push_cast
  field_simp
  linear_combination (((t : ℝ) : ℂ) ^ (m - 2 * r)) * hchoose

end
end S_LanglandsTunnell_integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum
end P2MW
export P2MW.S_LanglandsTunnell_integral_exp_neg_pi_sq_mul_ofReal_add_I_mul_pow_eq_hermite_sum (solution)
