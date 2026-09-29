-- Prove2me | solution 1 for LanglandsTunnell.setIntegral_oneSided_torusPair_flatBracket_eq_const_mul_laplaceMellin_and_mirror_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6caa86a6-029e-5c17-8cfb-e1ee70af73a6

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Theorems.Thm_LanglandsTunnell_setIntegral_oneSided_torusPair_eq_setIntegral_fiber
import Theorems.Thm_LanglandsTunnell_setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous
import Theorems.Thm_LanglandsTunnell_exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_setIntegral_oneSided_torusPair_flatBracket_eq_const_mul_laplaceMellin_and_mirror_eq_zero

set_option autoImplicit false

open MeasureTheory Set

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "setIntegral_oneSided_torusPair_eq_setIntegral_fiber setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound"
namespace BackK8
p2m_open "LanglandsTunnell"

lemma sum_le_prod_one_add (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a + b + c + d ≤ (1 + a) * (1 + b) * (1 + c) * (1 + d) := by
  nlinarith [mul_nonneg ha hb, mul_nonneg hc hd, mul_nonneg (mul_nonneg ha hb) hc,
    mul_nonneg (mul_nonneg ha hb) hd, mul_nonneg ha hc, mul_nonneg ha hd, mul_nonneg hb hc, mul_nonneg hb hd,
    mul_nonneg (mul_nonneg ha hc) hd, mul_nonneg (mul_nonneg hb hc) hd,
    mul_nonneg (mul_nonneg (mul_nonneg ha hb) hc) hd]

lemma norm_bracket_pow_le (m : ℕ) (x z : ℝ) :
    ‖(((x : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m‖ ≤ (|x| + |z|) ^ m := by
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc ‖((x : ℝ) : ℂ) + Complex.I * (z : ℂ)‖ ≤ ‖((x : ℝ) : ℂ)‖ + ‖Complex.I * (z : ℂ)‖ := norm_add_le _ _
    _ = |x| + |z| := by simp [Complex.norm_real, Real.norm_eq_abs]

lemma bracketMinus_bound (m : ℕ) (p q r z : ℝ) :
    ‖(((p - q + r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m‖
      ≤ 1 * (1 + |p|) ^ m * (1 + |q|) ^ m * (1 + |r|) ^ m * (1 + |z|) ^ m := by
  refine (norm_bracket_pow_le m _ z).trans ?_
  rw [one_mul, ← mul_pow, ← mul_pow, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  calc |p - q + r| + |z| ≤ |p| + |q| + |r| + |z| := by
        have := abs_add_le (p - q) r; have := abs_sub p q; linarith
    _ ≤ (1 + |p|) * (1 + |q|) * (1 + |r|) * (1 + |z|) :=
        sum_le_prod_one_add _ _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)

lemma bracketPlus_bound (m : ℕ) (p q r z : ℝ) :
    ‖(((-p - q - r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m‖
      ≤ 1 * (1 + |p|) ^ m * (1 + |q|) ^ m * (1 + |r|) ^ m * (1 + |z|) ^ m := by
  refine (norm_bracket_pow_le m _ z).trans ?_
  rw [one_mul, ← mul_pow, ← mul_pow, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  calc |-p - q - r| + |z| ≤ |p| + |q| + |r| + |z| := by
        have := abs_sub (-p - q) r; have := abs_sub (-p) q; rw [abs_neg] at this; linarith
    _ ≤ (1 + |p|) * (1 + |q|) * (1 + |r|) * (1 + |z|) :=
        sum_le_prod_one_add _ _ _ _ (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)

noncomputable def pMinus (m : ℕ) : MvPolynomial (Fin 2) ℂ := (-(MvPolynomial.X 0 + MvPolynomial.X 1)) ^ m
noncomputable def pPlus (m : ℕ) : MvPolynomial (Fin 2) ℂ := (MvPolynomial.X 0 - MvPolynomial.X 1) ^ m

lemma pMinus_isHomogeneous (m : ℕ) : (pMinus m).IsHomogeneous m := by
  have h1 : (-(MvPolynomial.X (R := ℂ) (0 : Fin 2) + MvPolynomial.X 1)).IsHomogeneous 1 :=
    ((MvPolynomial.isHomogeneous_X ℂ 0).add (MvPolynomial.isHomogeneous_X ℂ 1)).neg
  have h2 := h1.pow m
  simpa only [pMinus, mul_one, one_mul] using h2

lemma pPlus_isHomogeneous (m : ℕ) : (pPlus m).IsHomogeneous m := by
  have h1 : (MvPolynomial.X (R := ℂ) (0 : Fin 2) - MvPolynomial.X 1).IsHomogeneous 1 :=
    (MvPolynomial.isHomogeneous_X ℂ 0).sub (MvPolynomial.isHomogeneous_X ℂ 1)
  have h2 := h1.pow m
  simpa only [pPlus, mul_one, one_mul] using h2

lemma eval_pMinus (m : ℕ) (a b : ℂ) : MvPolynomial.eval ![a, b] (pMinus m) = (-(a + b)) ^ m := by
  simp [pMinus, MvPolynomial.eval_pow]

lemma eval_pPlus (m : ℕ) (a b : ℂ) : MvPolynomial.eval ![a, b] (pPlus m) = (a - b) ^ m := by
  simp [pPlus, MvPolynomial.eval_pow]

end LanglandsTunnell.BackK8

open LanglandsTunnell.BackK8 in
theorem solution
    (m : ℕ) (hm : 1 ≤ m) (β : ℂ) (g g' : ℝ → ℂ) (hg : Measurable g) (hg' : Measurable g')
    (Cg σg : ℝ) (hσg : 0 ≤ σg) (hgb : ∀ τ : ℝ, τ ≠ 0 → ‖g τ‖ ≤ Cg * (1 + |τ| ^ (-σg)))
    (Cg' σg' : ℝ) (hσg' : 0 ≤ σg') (hgb' : ∀ τ : ℝ, τ ≠ 0 → ‖g' τ‖ ≤ Cg' * (1 + |τ| ^ (-σg'))) :
    ∃ σ₀ : ℝ, ∀ α γ : ℂ, σ₀ < α.re → γ.re < -σ₀ → -2 * α + β - γ - 2 = (1 : ℂ) - (m : ℂ) →
      (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
          ((t : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
            ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
            g (t * |y₁| / y₂) *
            (∫ z : ℝ, (((y₁⁻¹ - y₂⁻¹ + t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))
        = (1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(α - β)) * Complex.Gamma (α - β) * (-2 : ℂ) ^ m *
          ∫ v in Ioi (0 : ℝ), g v * ((v : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * v)) : ℂ) ∧
      (∫ t in Ioi (0 : ℝ), ∫ y₁ in Iio (0 : ℝ), ∫ y₂ in Ioi (0 : ℝ),
          ((t : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * t)) : ℂ) *
            ((|y₁| : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + t ^ 2 * y₁ ^ 2 + (y₂ ^ 2)⁻¹))) : ℂ) *
            g' (t * |y₁| / y₂) *
            (∫ z : ℝ, (((-y₁⁻¹ - y₂⁻¹ - t * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))
        = 0 := by

  obtain ⟨σ₁, hσ₁⟩ :=
    LanglandsTunnell.exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
      β g hg Cg σg hσg hgb (fun p q r z => (((p - q + r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m)
      (by fun_prop) 1 m (fun p q r z => bracketMinus_bound m p q r z)
  obtain ⟨σ₂, hσ₂⟩ :=
    LanglandsTunnell.exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
      β g' hg' Cg' σg' hσg' hgb' (fun p q r z => (((-p - q - r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m)
      (by fun_prop) 1 m (fun p q r z => bracketPlus_bound m p q r z)
  refine ⟨max (max σ₁ σ₂) ((m : ℝ) + β.re), fun α γ hα hγ hw => ?_⟩
  have h12 : max σ₁ σ₂ ≤ max (max σ₁ σ₂) ((m : ℝ) + β.re) := le_max_left _ _
  have hα₁ : σ₁ < α.re := lt_of_le_of_lt ((le_max_left _ _).trans h12) hα
  have hα₂ : σ₂ < α.re := lt_of_le_of_lt ((le_max_right _ _).trans h12) hα
  have hγ₁ : γ.re < -σ₁ := lt_of_lt_of_le hγ (neg_le_neg ((le_max_left _ _).trans h12))
  have hγ₂ : γ.re < -σ₂ := lt_of_lt_of_le hγ (neg_le_neg ((le_max_right _ _).trans h12))
  have hmβ : (m : ℝ) + β.re < α.re := lt_of_le_of_lt (le_max_right _ _) hα
  have ha : (m : ℝ) - 1 < (α - β - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]; linarith

  have hwexp : ∀ w : ℝ, ((w : ℝ) : ℂ) ^ (-2 * α + β - γ - 2) = ((w : ℝ) : ℂ) ^ ((1 : ℤ) - (m : ℤ)) := by
    intro w
    rw [hw, show ((1 : ℂ) - (m : ℂ)) = (((1 : ℤ) - (m : ℤ) : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  constructor
  ·
    have hO := LanglandsTunnell.setIntegral_oneSided_torusPair_eq_setIntegral_fiber α β γ g hg
      (fun p q r z => (((p - q + r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m) (by fun_prop) (hσ₁ α γ hα₁ hγ₁)
    beta_reduce at hO
    rw [hO]
    have key : ∀ v ∈ Ioi (0 : ℝ),
        (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
            (((σ * w - v : ℝ) : ℂ) ^ (α - β - 1)) * ((w : ℝ) : ℂ) ^ (-2 * α + β - γ - 2) *
              (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
              (∫ z : ℝ, (((-((σ * w - v) / w) - w + -(v / w) : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))
          = (1 / 2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(α - β - 1) - 1) * Complex.Gamma (α - β - 1 + 1) *
              (Real.exp (-(2 * Real.pi * v)) : ℂ) * (-2 : ℂ) ^ m := by
      intro v hv
      have hF := LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous
        m (α - β - 1) ha v hv (pMinus m) (pMinus_isHomogeneous m)
      rw [eval_pMinus, show (-((1 : ℂ) + 1)) = (-2 : ℂ) by norm_num] at hF
      rw [← hF]
      refine setIntegral_congr_fun measurableSet_Ioi (fun σ hσ => ?_)
      refine setIntegral_congr_fun measurableSet_Ioi (fun w hw' => ?_)
      have hσ0 : (0 : ℝ) < σ := hσ
      have hw0 : (0 : ℝ) < w := lt_trans (div_pos hv hσ0) hw'
      rw [hwexp w]
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      beta_reduce
      rw [eval_pMinus]
      congr 1
      have hwne : (w : ℝ) ≠ 0 := hw0.ne'
      have : (-((σ * w - v) / w) - w + -(v / w) : ℝ) = -σ - w := by field_simp; ring
      rw [this]; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun v hv => show g v * ((v : ℝ) : ℂ) ^ α * _ = g v * ((v : ℝ) : ℂ) ^ α * _ from by rw [key v hv])]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun v _ => ?_)
    have e1 : (-(α - β - 1) - 1 : ℂ) = -(α - β) := by ring
    have e2 : (α - β - 1 + 1 : ℂ) = α - β := by ring
    rw [e1, e2]; ring
  ·
    have hO := LanglandsTunnell.setIntegral_oneSided_torusPair_eq_setIntegral_fiber α β γ g' hg'
      (fun p q r z => (((-p - q - r : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m) (by fun_prop) (hσ₂ α γ hα₂ hγ₂)
    beta_reduce at hO
    rw [hO]
    have key : ∀ v ∈ Ioi (0 : ℝ),
        (∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
            (((σ * w - v : ℝ) : ℂ) ^ (α - β - 1)) * ((w : ℝ) : ℂ) ^ (-2 * α + β - γ - 2) *
              (Real.exp (-(Real.pi * (σ ^ 2 + w ^ 2))) : ℂ) *
              (∫ z : ℝ, (((-(-((σ * w - v) / w)) - w - -(v / w) : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                (Real.exp (-(Real.pi * z ^ 2)) : ℂ)))
          = 0 := by
      intro v hv
      have hF := LanglandsTunnell.setIntegral_setIntegral_cpow_mul_pow_mul_exp_mul_gaussianAverage_eq_Gamma_mul_exp_mul_eval_of_isHomogeneous
        m (α - β - 1) ha v hv (pPlus m) (pPlus_isHomogeneous m)
      rw [eval_pPlus, sub_self, zero_pow (Nat.one_le_iff_ne_zero.mp hm), mul_zero] at hF
      rw [← hF]
      refine setIntegral_congr_fun measurableSet_Ioi (fun σ hσ => ?_)
      refine setIntegral_congr_fun measurableSet_Ioi (fun w hw' => ?_)
      have hσ0 : (0 : ℝ) < σ := hσ
      have hw0 : (0 : ℝ) < w := lt_trans (div_pos hv hσ0) hw'
      rw [hwexp w]
      congr 1
      rw [← integral_neg_eq_self]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
      beta_reduce
      rw [eval_pPlus]
      have hwne : (w : ℝ) ≠ 0 := hw0.ne'
      have : (-(-((σ * w - v) / w)) - w - -(v / w) : ℝ) = σ - w := by field_simp; ring
      rw [this]; push_cast
      simp only [even_two, Even.neg_pow]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun v hv => show g' v * ((v : ℝ) : ℂ) ^ α * _ = g' v * ((v : ℝ) : ℂ) ^ α * _ from by rw [key v hv])]
    simp

end S_LanglandsTunnell_setIntegral_oneSided_torusPair_flatBracket_eq_const_mul_laplaceMellin_and_mirror_eq_zero
end P2MW
export P2MW.S_LanglandsTunnell_setIntegral_oneSided_torusPair_flatBracket_eq_const_mul_laplaceMellin_and_mirror_eq_zero (solution)
