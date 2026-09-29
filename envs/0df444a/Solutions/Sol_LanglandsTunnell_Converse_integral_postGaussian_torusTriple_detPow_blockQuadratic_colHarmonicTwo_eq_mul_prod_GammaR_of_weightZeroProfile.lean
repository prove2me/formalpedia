-- Prove2me | solution 1 for LanglandsTunnell.Converse.integral_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_eq_mul_prod_GammaR_of_weightZeroProfile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/fe3c0b1c-fe91-539f-87c5-07ae4dd06b55

import Mathlib
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Theorems.Thm_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
import Theorems.Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_integral_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_eq_mul_prod_GammaR_of_weightZeroProfile

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open NumberField LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

namespace S2Q48

theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x : ℝ) : ℂ) ^ z = Complex.exp (z * ((Real.log x : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hx.ne'), Complex.ofReal_log hx.le, mul_comm]

theorem ofReal_eq_exp_log {x : ℝ} (hx : 0 < x) : ((x : ℝ) : ℂ) = Complex.exp ((Real.log x : ℝ) : ℂ) := by
  rw [← Complex.ofReal_exp, Real.exp_log hx]

theorem quasiChar_of_pos (u : ℂ) (a : ZMod 2) {x : ℝ} (hx : 0 < x) : ArchR.quasiChar u a x = ((x : ℝ) : ℂ) ^ u := by
  unfold ArchR.quasiChar
  rw [abs_of_pos hx]
  split_ifs
  · rw [mul_one]
  · rw [sign_pos hx]; simp

theorem quasiChar_neg (u : ℂ) (a : ZMod 2) (x : ℝ) (hx : x ≠ 0) :
    ArchR.quasiChar u a (-x) = (-1 : ℂ) ^ a.val * ArchR.quasiChar u a x := by
  unfold ArchR.quasiChar
  rw [abs_neg]
  have ha : a = 0 ∨ a = 1 := (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a
  rcases ha with h | h
  · subst h; simp
  · subst h
    simp only [one_ne_zero, if_false, ZMod.val_one, pow_one, Left.sign_neg, SignType.coe_neg]
    push_cast
    ring

theorem pointwise00 (ν₁ ν₂ : ℂ) (b c : ZMod 2) (hc : c = b + 1)
    (W : ℝ → ℂ) (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (a₀ : ZMod 2)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) (s : ℂ)
    (t y₁ y₂ : ℝ) (ht : 0 < t) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (hWt : W t + (-1 : ℂ) ^ b.val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWm : W (-t) = (-1 : ℂ) ^ b.val * W t) (hb : b = 0) (hd : δ = 0) :
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * y₁ / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * (-t) ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * (-t) * y₁ / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((((-y₁) * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * (-y₁) / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * (-y₁) ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * (-y₁) / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((((-y₁) * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * (-y₁) / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * (-t) ^ 2 * (-y₁) ^ 2 + 1 / (2 * Real.pi) + 2 * a * (-t) * (-y₁) / y₂ : ℝ)) : ℂ)))) =
    ((-1 : ℂ) ^ b.val * ρ * 2 * Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + 2 + 1)) *
      (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s + 1 / 2) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t * y₁ / y₂ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (t * y₁ / y₂ / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ)) * ((y₂ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ) - cP - 2 * s - 3) *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) := by
  subst ha1 hb hd

  obtain rfl : c = 1 := by rw [hc]; decide
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hδpar
  obtain rfl := (by decide : ∀ x : ZMod 2, (0 : ZMod 2) = x + 0 → x = 0) a₀ hδpar
  subst hP₂
  simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one] at hDpar hWt hWm ⊢
  have eτ : 0 < t * y₁ / y₂ := by positivity
  rw [show (-1 : ℝ) * t * y₁ / y₂ = -(t * y₁ / y₂) by ring,
    show (-1 : ℝ) * -t * y₁ / y₂ = t * y₁ / y₂ by ring,
    show (-1 : ℝ) * t * -y₁ / y₂ = t * y₁ / y₂ by ring,
    show (-1 : ℝ) * -t * -y₁ / y₂ = -(t * y₁ / y₂) by ring]
  rw [hDpar _ eτ, hρ _ eτ, hWm]
  rw [show (-y₁) * y₂ = -(y₁ * y₂) by ring, inv_neg,
    quasiChar_neg _ _ _ (by positivity), quasiChar_of_pos _ _ (by positivity : (0:ℝ) < (y₁ * y₂)⁻¹)]
  simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one]
  have hcc : ArchR.centralChar (RealArchParam.principal μ₁ 1 μ₂ 1) y₂ = ((y₂ : ℝ) : ℂ) ^ (μ₁ + μ₂) := by
    unfold ArchR.centralChar; rw [quasiChar_of_pos _ _ hy₂]; rfl
  have hce : (RealArchParam.principal μ₁ 1 μ₂ 1).centralExponent = μ₁ + μ₂ := rfl
  rw [hcc, hce]
  have r1 : |(y₁ * y₂)⁻¹| = (y₁ * y₂)⁻¹ := abs_of_pos (by positivity)
  have r2 : |(-((y₁ * y₂)⁻¹))| = (y₁ * y₂)⁻¹ := by rw [abs_neg, r1]
  have r3 : |y₁ * y₂| = y₁ * y₂ := abs_of_pos (by positivity)
  have r4 : |(-(y₁ * y₂))| = y₁ * y₂ := by rw [abs_neg, r3]
  have r5 : |y₂| = y₂ := abs_of_pos hy₂
  have r6 : |y₁| = y₁ := abs_of_pos hy₁
  have r7 : |(-y₁)| = y₁ := by rw [abs_neg, r6]
  have r8 : |t| = t := abs_of_pos ht
  have r9 : |(-t)| = t := by rw [abs_neg, r8]
  rw [r2, r4, r1, r3, r5, r7, r6, r9, r8, neg_sq t, neg_sq y₁]
  have hI2 : ∀ X : ℂ, X * (-Complex.I * ((-1 : ℝ) : ℂ)) ^ 2 * (-Complex.I * ((y₂ : ℝ) : ℂ)) ^ 2 = X * ((y₂ : ℝ) : ℂ) ^ 2 := by
    intro X
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination (X * (y₂ : ℂ) ^ 2 * (Complex.I * Complex.I - 1)) * hI
  simp only [hI2]
  have he1 : ((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℝ) : ℂ) =
        ((Real.exp (-(Real.pi / y₁ ^ 2)) : ℝ) : ℂ) * ((Real.exp (-(Real.pi / y₂ ^ 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1; congr 1; ring
  have he2 : ∀ T : ℝ, T ^ 2 = t ^ 2 →
      ((Real.exp (-(Real.pi * ((-1 * T) ^ 2 * y₁ ^ 2))) : ℝ) : ℂ) = ((Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℝ) : ℂ) := by
    intro T hT
    congr 1; congr 1
    rw [mul_pow, hT]; ring
  rw [he1, he2 t rfl, he2 (-t) (neg_sq t)]
  have hk1 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * t * y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) - 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk2 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * -t * y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) + 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk3 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * t * -y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) + 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk4 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * -t * -y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) - 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  rw [hk1, hk2, hk3, hk4]
  have hW2 : (2 : ℂ) * W t = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) := by
    linear_combination hWt + (-1 : ℂ) * hWm

  set Ec : ℂ := ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) with hEc
  set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
  set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            (((t * y₁ / y₂ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (t * y₁ / y₂ / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
  set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2) with htα
  set tα2 : ℂ := ((t : ℝ) : ℂ) ^ (s + 1 / 2) with htα2
  set E1 : ℂ := ((Real.exp (-(Real.pi / y₁ ^ 2)) : ℝ) : ℂ) with hE1
  set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℝ) : ℂ) with hEt
  set E2 : ℂ := ((Real.exp (-(Real.pi / y₂ ^ 2)) : ℝ) : ℂ) with hE2
  set cA : ℂ := (((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ (u₀ + 2) with hcA
  set cY : ℂ := ((y₂ : ℝ) : ℂ) ^ (μ₁ + μ₂) with hcY
  set cB : ℂ := ((Real.pi * (-1) ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2)) with hcB
  set Gm : ℂ := Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2) with hGm
  set GR : ℂ := Complex.Gammaℝ (cP + (μ₁ + μ₂) + 2 * s + 2 + 1) with hGR
  set yβ : ℂ := ((y₁ : ℝ) : ℂ) ^ (-u₀ - 0) with hyβ
  set yγ : ℂ := ((y₂ : ℝ) : ℂ) ^ (-u₀ - 0 - cP - 2 * s - 3) with hyγ
  set Wt : ℂ := W t with hWt0
  set τc : ℂ := ((t * y₁ / y₂ : ℝ) : ℂ) with hτc
  have hτc' : τc = (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by rw [hτc]; push_cast; ring

  have hp : cA * cY * cB * Gm * tα * ((t : ℝ) : ℂ) * (((y₁ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) = GR * tα2 * yβ * yγ := by
    have hp0 : cA * cY * cB * tα * ((t : ℝ) : ℂ) * (((y₁ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) =
        ((Real.pi : ℝ) : ℂ) ^ (-(cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2) * tα2 * yβ * yγ := by
      have hb1 : (0 : ℝ) < (y₁ * y₂)⁻¹ := by positivity
      have hb3 : (0 : ℝ) < Real.pi * (-1) ^ 2 * y₂ ^ 2 := by positivity
      rw [hcA, hcY, hcB, htα, htα2, hyβ, hyγ, ofReal_cpow_eq_exp hb1, ofReal_cpow_eq_exp hy₂, ofReal_cpow_eq_exp hb3,
        ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp Real.pi_pos, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hy₁, ofReal_cpow_eq_exp hy₂,
        ofReal_eq_exp_log ht, ofReal_eq_exp_log hy₁, ofReal_eq_exp_log hy₂, Real.log_inv, Real.log_mul hy₁.ne' hy₂.ne',
        show Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 = Real.pi * y₂ ^ 2 by ring,
        Real.log_mul Real.pi_pos.ne' (pow_ne_zero 2 hy₂.ne'), Real.log_pow]
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hGR, Complex.Gammaℝ_def, hGm]
    linear_combination (Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2)) * hp0
  have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hy10 : ((y₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₁.ne'
  have hy20 : ((y₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₂.ne'
  rw [hτc']
  clear_value Ec Gpt Gqτ tα tα2 E1 Et E2 cA cY cB Gm GR yβ yγ Wt τc
  have hJ : ((((y₁ * y₂)⁻¹ ^ 2)⁻¹ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * (((y₁ * y₂ : ℝ) : ℂ)) * ((y₂ : ℝ) : ℂ) ^ 2 * (1 / 2 : ℂ) *
      ((y₂ ^ 2 * ((y₁ * y₂) ^ 4)⁻¹ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
      (((t : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) / ((y₂ : ℝ) : ℂ)) * (8 * ((t : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) / ((y₂ : ℝ) : ℂ)) = 4 * (((y₁ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) := by
    push_cast
    field_simp
    try ring
  linear_combination ((1 : ℂ) * ρ * Gqτ * Wt * cA * cY * cB * Gm * tα * E1 * Et * E2) * hJ +
    (2 * (((y₁ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) * (1 : ℂ) * ρ * Gqτ * cA * cY * cB * Gm * tα * E1 * Et * E2) * hW2 +
    (2 * (1 : ℂ) * ρ * Gqτ * Gpt * E1 * Et * E2) * hp

theorem pointwise01 (ν₁ ν₂ : ℂ) (b c : ZMod 2) (hc : c = b + 1)
    (W : ℝ → ℂ) (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (a₀ : ZMod 2)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) (s : ℂ)
    (t y₁ y₂ : ℝ) (ht : 0 < t) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (hWt : W t + (-1 : ℂ) ^ b.val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWm : W (-t) = (-1 : ℂ) ^ b.val * W t) (hb : b = 0) (hd : δ = 1) :
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * y₁ / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * (-t) ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * (-t) * y₁ / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((((-y₁) * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * (-y₁) / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * (-y₁) ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * (-y₁) / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((((-y₁) * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * (-y₁) / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * (-t) ^ 2 * (-y₁) ^ 2 + 1 / (2 * Real.pi) + 2 * a * (-t) * (-y₁) / y₂ : ℝ)) : ℂ)))) =
    ((-1 : ℂ) ^ b.val * ρ * 2 * Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + 2 + 1)) *
      (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s + 1 / 2) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t * y₁ / y₂ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (t * y₁ / y₂ / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ)) * ((y₂ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ) - cP - 2 * s - 3) *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) := by
  subst ha1 hb hd

  obtain rfl : c = 1 := by rw [hc]; decide
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hδpar
  obtain rfl := (by decide : ∀ x : ZMod 2, (1 : ZMod 2) = x + 0 → x = 1) a₀ hδpar
  subst hP₂
  simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one] at hDpar hWt hWm ⊢
  have eτ : 0 < t * y₁ / y₂ := by positivity
  rw [show (-1 : ℝ) * t * y₁ / y₂ = -(t * y₁ / y₂) by ring,
    show (-1 : ℝ) * -t * y₁ / y₂ = t * y₁ / y₂ by ring,
    show (-1 : ℝ) * t * -y₁ / y₂ = t * y₁ / y₂ by ring,
    show (-1 : ℝ) * -t * -y₁ / y₂ = -(t * y₁ / y₂) by ring]
  rw [hDpar _ eτ, hρ _ eτ, hWm]
  rw [show (-y₁) * y₂ = -(y₁ * y₂) by ring, inv_neg,
    quasiChar_neg _ _ _ (by positivity), quasiChar_of_pos _ _ (by positivity : (0:ℝ) < (y₁ * y₂)⁻¹)]
  simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one]
  rw [Complex.ofReal_neg ((y₁ * y₂)⁻¹)]
  have hcc : ArchR.centralChar (RealArchParam.principal μ₁ 1 μ₂ 1) y₂ = ((y₂ : ℝ) : ℂ) ^ (μ₁ + μ₂) := by
    unfold ArchR.centralChar; rw [quasiChar_of_pos _ _ hy₂]; rfl
  have hce : (RealArchParam.principal μ₁ 1 μ₂ 1).centralExponent = μ₁ + μ₂ := rfl
  rw [hcc, hce]
  have r1 : |(y₁ * y₂)⁻¹| = (y₁ * y₂)⁻¹ := abs_of_pos (by positivity)
  have r2 : |(-((y₁ * y₂)⁻¹))| = (y₁ * y₂)⁻¹ := by rw [abs_neg, r1]
  have r3 : |y₁ * y₂| = y₁ * y₂ := abs_of_pos (by positivity)
  have r4 : |(-(y₁ * y₂))| = y₁ * y₂ := by rw [abs_neg, r3]
  have r5 : |y₂| = y₂ := abs_of_pos hy₂
  have r6 : |y₁| = y₁ := abs_of_pos hy₁
  have r7 : |(-y₁)| = y₁ := by rw [abs_neg, r6]
  have r8 : |t| = t := abs_of_pos ht
  have r9 : |(-t)| = t := by rw [abs_neg, r8]
  rw [r2, r4, r1, r3, r5, r7, r6, r9, r8, neg_sq t, neg_sq y₁]
  have hI2 : ∀ X : ℂ, X * (-Complex.I * ((-1 : ℝ) : ℂ)) ^ 2 * (-Complex.I * ((y₂ : ℝ) : ℂ)) ^ 2 = X * ((y₂ : ℝ) : ℂ) ^ 2 := by
    intro X
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination (X * (y₂ : ℂ) ^ 2 * (Complex.I * Complex.I - 1)) * hI
  simp only [hI2]
  have he1 : ((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℝ) : ℂ) =
        ((Real.exp (-(Real.pi / y₁ ^ 2)) : ℝ) : ℂ) * ((Real.exp (-(Real.pi / y₂ ^ 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1; congr 1; ring
  have he2 : ∀ T : ℝ, T ^ 2 = t ^ 2 →
      ((Real.exp (-(Real.pi * ((-1 * T) ^ 2 * y₁ ^ 2))) : ℝ) : ℂ) = ((Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℝ) : ℂ) := by
    intro T hT
    congr 1; congr 1
    rw [mul_pow, hT]; ring
  rw [he1, he2 t rfl, he2 (-t) (neg_sq t)]
  have hk1 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * t * y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) - 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk2 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * -t * y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) + 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk3 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * t * -y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) + 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk4 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * -t * -y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) - 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  rw [hk1, hk2, hk3, hk4]
  have hW2 : (2 : ℂ) * W t = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) := by
    linear_combination hWt + (-1 : ℂ) * hWm

  set Ec : ℂ := ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) with hEc
  set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
  set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            (((t * y₁ / y₂ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (t * y₁ / y₂ / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
  set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2) with htα
  set tα2 : ℂ := ((t : ℝ) : ℂ) ^ (s + 1 / 2) with htα2
  set E1 : ℂ := ((Real.exp (-(Real.pi / y₁ ^ 2)) : ℝ) : ℂ) with hE1
  set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℝ) : ℂ) with hEt
  set E2 : ℂ := ((Real.exp (-(Real.pi / y₂ ^ 2)) : ℝ) : ℂ) with hE2
  set cA : ℂ := (((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ (u₀ + 2) with hcA
  set cY : ℂ := ((y₂ : ℝ) : ℂ) ^ (μ₁ + μ₂) with hcY
  set cB : ℂ := ((Real.pi * (-1) ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2)) with hcB
  set Gm : ℂ := Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2) with hGm
  set GR : ℂ := Complex.Gammaℝ (cP + (μ₁ + μ₂) + 2 * s + 2 + 1) with hGR
  set yβ : ℂ := ((y₁ : ℝ) : ℂ) ^ (-u₀ - 1) with hyβ
  set yγ : ℂ := ((y₂ : ℝ) : ℂ) ^ (-u₀ - 1 - cP - 2 * s - 3) with hyγ
  set Wt : ℂ := W t with hWt0
  set τc : ℂ := ((t * y₁ / y₂ : ℝ) : ℂ) with hτc
  have hτc' : τc = (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by rw [hτc]; push_cast; ring

  have hp : cA * cY * cB * Gm * tα * ((t : ℝ) : ℂ) * (((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) = GR * tα2 * yβ * yγ := by
    have hp0 : cA * cY * cB * tα * ((t : ℝ) : ℂ) * (((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) =
        ((Real.pi : ℝ) : ℂ) ^ (-(cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2) * tα2 * yβ * yγ := by
      have hb1 : (0 : ℝ) < (y₁ * y₂)⁻¹ := by positivity
      have hb3 : (0 : ℝ) < Real.pi * (-1) ^ 2 * y₂ ^ 2 := by positivity
      rw [hcA, hcY, hcB, htα, htα2, hyβ, hyγ, ofReal_cpow_eq_exp hb1, ofReal_cpow_eq_exp hy₂, ofReal_cpow_eq_exp hb3,
        ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp Real.pi_pos, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hy₁, ofReal_cpow_eq_exp hy₂,
        ofReal_eq_exp_log ht, ofReal_eq_exp_log hy₁, ofReal_eq_exp_log hy₂, Real.log_inv, Real.log_mul hy₁.ne' hy₂.ne',
        show Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 = Real.pi * y₂ ^ 2 by ring,
        Real.log_mul Real.pi_pos.ne' (pow_ne_zero 2 hy₂.ne'), Real.log_pow]
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hGR, Complex.Gammaℝ_def, hGm]
    linear_combination (Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2)) * hp0
  have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hy10 : ((y₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₁.ne'
  have hy20 : ((y₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₂.ne'
  rw [hτc']
  clear_value Ec Gpt Gqτ tα tα2 E1 Et E2 cA cY cB Gm GR yβ yγ Wt τc
  have hJ : ((((y₁ * y₂)⁻¹ ^ 2)⁻¹ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) * ((y₁ * y₂ : ℝ) : ℂ)) * ((y₂ : ℝ) : ℂ) ^ 2 * (1 / 2 : ℂ) *
      ((y₂ ^ 2 * ((y₁ * y₂) ^ 4)⁻¹ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
      (((t : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) / ((y₂ : ℝ) : ℂ)) * (8 * ((t : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) / ((y₂ : ℝ) : ℂ)) = 4 * (((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) := by
    push_cast
    field_simp
    try ring
  linear_combination ((1 : ℂ) * ρ * Gqτ * Wt * cA * cY * cB * Gm * tα * E1 * Et * E2) * hJ +
    (2 * (((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) * (1 : ℂ) * ρ * Gqτ * cA * cY * cB * Gm * tα * E1 * Et * E2) * hW2 +
    (2 * (1 : ℂ) * ρ * Gqτ * Gpt * E1 * Et * E2) * hp

theorem pointwise10 (ν₁ ν₂ : ℂ) (b c : ZMod 2) (hc : c = b + 1)
    (W : ℝ → ℂ) (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (a₀ : ZMod 2)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) (s : ℂ)
    (t y₁ y₂ : ℝ) (ht : 0 < t) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (hWt : W t + (-1 : ℂ) ^ b.val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWm : W (-t) = (-1 : ℂ) ^ b.val * W t) (hb : b = 1) (hd : δ = 0) :
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * y₁ / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * (-t) ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * (-t) * y₁ / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((((-y₁) * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * (-y₁) / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * (-y₁) ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * (-y₁) / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((((-y₁) * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * (-y₁) / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * (-t) ^ 2 * (-y₁) ^ 2 + 1 / (2 * Real.pi) + 2 * a * (-t) * (-y₁) / y₂ : ℝ)) : ℂ)))) =
    ((-1 : ℂ) ^ b.val * ρ * 2 * Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + 2 + 1)) *
      (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s + 1 / 2) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t * y₁ / y₂ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (t * y₁ / y₂ / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ)) * ((y₂ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ) - cP - 2 * s - 3) *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) := by
  subst ha1 hb hd

  obtain rfl : c = 0 := by rw [hc]; decide
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hδpar
  obtain rfl := (by decide : ∀ x : ZMod 2, (0 : ZMod 2) = x + 1 → x = 1) a₀ hδpar
  subst hP₂
  simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one] at hDpar hWt hWm ⊢
  have eτ : 0 < t * y₁ / y₂ := by positivity
  rw [show (-1 : ℝ) * t * y₁ / y₂ = -(t * y₁ / y₂) by ring,
    show (-1 : ℝ) * -t * y₁ / y₂ = t * y₁ / y₂ by ring,
    show (-1 : ℝ) * t * -y₁ / y₂ = t * y₁ / y₂ by ring,
    show (-1 : ℝ) * -t * -y₁ / y₂ = -(t * y₁ / y₂) by ring]
  rw [hDpar _ eτ, hρ _ eτ, hWm]
  rw [show (-y₁) * y₂ = -(y₁ * y₂) by ring, inv_neg,
    quasiChar_neg _ _ _ (by positivity), quasiChar_of_pos _ _ (by positivity : (0:ℝ) < (y₁ * y₂)⁻¹)]
  simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one]
  have hcc : ArchR.centralChar (RealArchParam.principal μ₁ 0 μ₂ 0) y₂ = ((y₂ : ℝ) : ℂ) ^ (μ₁ + μ₂) := by
    unfold ArchR.centralChar; rw [quasiChar_of_pos _ _ hy₂]; rfl
  have hce : (RealArchParam.principal μ₁ 0 μ₂ 0).centralExponent = μ₁ + μ₂ := rfl
  rw [hcc, hce]
  have r1 : |(y₁ * y₂)⁻¹| = (y₁ * y₂)⁻¹ := abs_of_pos (by positivity)
  have r2 : |(-((y₁ * y₂)⁻¹))| = (y₁ * y₂)⁻¹ := by rw [abs_neg, r1]
  have r3 : |y₁ * y₂| = y₁ * y₂ := abs_of_pos (by positivity)
  have r4 : |(-(y₁ * y₂))| = y₁ * y₂ := by rw [abs_neg, r3]
  have r5 : |y₂| = y₂ := abs_of_pos hy₂
  have r6 : |y₁| = y₁ := abs_of_pos hy₁
  have r7 : |(-y₁)| = y₁ := by rw [abs_neg, r6]
  have r8 : |t| = t := abs_of_pos ht
  have r9 : |(-t)| = t := by rw [abs_neg, r8]
  rw [r2, r4, r1, r3, r5, r7, r6, r9, r8, neg_sq t, neg_sq y₁]
  have hI2 : ∀ X : ℂ, X * (-Complex.I * ((-1 : ℝ) : ℂ)) ^ 2 * (-Complex.I * ((y₂ : ℝ) : ℂ)) ^ 2 = X * ((y₂ : ℝ) : ℂ) ^ 2 := by
    intro X
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination (X * (y₂ : ℂ) ^ 2 * (Complex.I * Complex.I - 1)) * hI
  simp only [hI2]
  have he1 : ((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℝ) : ℂ) =
        ((Real.exp (-(Real.pi / y₁ ^ 2)) : ℝ) : ℂ) * ((Real.exp (-(Real.pi / y₂ ^ 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1; congr 1; ring
  have he2 : ∀ T : ℝ, T ^ 2 = t ^ 2 →
      ((Real.exp (-(Real.pi * ((-1 * T) ^ 2 * y₁ ^ 2))) : ℝ) : ℂ) = ((Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℝ) : ℂ) := by
    intro T hT
    congr 1; congr 1
    rw [mul_pow, hT]; ring
  rw [he1, he2 t rfl, he2 (-t) (neg_sq t)]
  have hk1 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * t * y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) - 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk2 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * -t * y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) + 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk3 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * t * -y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) + 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk4 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * -t * -y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) - 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  rw [hk1, hk2, hk3, hk4]
  have hW2 : (2 : ℂ) * W t = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) := by
    linear_combination hWt + (1 : ℂ) * hWm

  set Ec : ℂ := ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) with hEc
  set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
  set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            (((t * y₁ / y₂ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (t * y₁ / y₂ / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
  set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2) with htα
  set tα2 : ℂ := ((t : ℝ) : ℂ) ^ (s + 1 / 2) with htα2
  set E1 : ℂ := ((Real.exp (-(Real.pi / y₁ ^ 2)) : ℝ) : ℂ) with hE1
  set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℝ) : ℂ) with hEt
  set E2 : ℂ := ((Real.exp (-(Real.pi / y₂ ^ 2)) : ℝ) : ℂ) with hE2
  set cA : ℂ := (((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ (u₀ + 2) with hcA
  set cY : ℂ := ((y₂ : ℝ) : ℂ) ^ (μ₁ + μ₂) with hcY
  set cB : ℂ := ((Real.pi * (-1) ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2)) with hcB
  set Gm : ℂ := Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2) with hGm
  set GR : ℂ := Complex.Gammaℝ (cP + (μ₁ + μ₂) + 2 * s + 2 + 1) with hGR
  set yβ : ℂ := ((y₁ : ℝ) : ℂ) ^ (-u₀ - 0) with hyβ
  set yγ : ℂ := ((y₂ : ℝ) : ℂ) ^ (-u₀ - 0 - cP - 2 * s - 3) with hyγ
  set Wt : ℂ := W t with hWt0
  set τc : ℂ := ((t * y₁ / y₂ : ℝ) : ℂ) with hτc
  have hτc' : τc = (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by rw [hτc]; push_cast; ring

  have hp : cA * cY * cB * Gm * tα * ((t : ℝ) : ℂ) * (((y₁ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) = GR * tα2 * yβ * yγ := by
    have hp0 : cA * cY * cB * tα * ((t : ℝ) : ℂ) * (((y₁ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) =
        ((Real.pi : ℝ) : ℂ) ^ (-(cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2) * tα2 * yβ * yγ := by
      have hb1 : (0 : ℝ) < (y₁ * y₂)⁻¹ := by positivity
      have hb3 : (0 : ℝ) < Real.pi * (-1) ^ 2 * y₂ ^ 2 := by positivity
      rw [hcA, hcY, hcB, htα, htα2, hyβ, hyγ, ofReal_cpow_eq_exp hb1, ofReal_cpow_eq_exp hy₂, ofReal_cpow_eq_exp hb3,
        ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp Real.pi_pos, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hy₁, ofReal_cpow_eq_exp hy₂,
        ofReal_eq_exp_log ht, ofReal_eq_exp_log hy₁, ofReal_eq_exp_log hy₂, Real.log_inv, Real.log_mul hy₁.ne' hy₂.ne',
        show Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 = Real.pi * y₂ ^ 2 by ring,
        Real.log_mul Real.pi_pos.ne' (pow_ne_zero 2 hy₂.ne'), Real.log_pow]
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hGR, Complex.Gammaℝ_def, hGm]
    linear_combination (Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2)) * hp0
  have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hy10 : ((y₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₁.ne'
  have hy20 : ((y₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₂.ne'
  rw [hτc']
  clear_value Ec Gpt Gqτ tα tα2 E1 Et E2 cA cY cB Gm GR yβ yγ Wt τc
  have hJ : ((((y₁ * y₂)⁻¹ ^ 2)⁻¹ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * (((y₁ * y₂ : ℝ) : ℂ)) * ((y₂ : ℝ) : ℂ) ^ 2 * (1 / 2 : ℂ) *
      ((y₂ ^ 2 * ((y₁ * y₂) ^ 4)⁻¹ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
      (((t : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) / ((y₂ : ℝ) : ℂ)) * (8 * ((t : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) / ((y₂ : ℝ) : ℂ)) = 4 * (((y₁ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) := by
    push_cast
    field_simp
    try ring
  linear_combination ((-1 : ℂ) * ρ * Gqτ * Wt * cA * cY * cB * Gm * tα * E1 * Et * E2) * hJ +
    (2 * (((y₁ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) * (-1 : ℂ) * ρ * Gqτ * cA * cY * cB * Gm * tα * E1 * Et * E2) * hW2 +
    (2 * (-1 : ℂ) * ρ * Gqτ * Gpt * E1 * Et * E2) * hp

theorem pointwise11 (ν₁ ν₂ : ℂ) (b c : ZMod 2) (hc : c = b + 1)
    (W : ℝ → ℂ) (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (a₀ : ZMod 2)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) (s : ℂ)
    (t y₁ y₂ : ℝ) (ht : 0 < t) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (hWt : W t + (-1 : ℂ) ^ b.val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWm : W (-t) = (-1 : ℂ) ^ b.val * W t) (hb : b = 1) (hd : δ = 1) :
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * y₁ / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * (-t) ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * (-t) * y₁ / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((((-y₁) * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * (-y₁) / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * (-y₁) ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * (-y₁) / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((((-y₁) * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * (-y₁) / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * (-t) ^ 2 * (-y₁) ^ 2 + 1 / (2 * Real.pi) + 2 * a * (-t) * (-y₁) / y₂ : ℝ)) : ℂ)))) =
    ((-1 : ℂ) ^ b.val * ρ * 2 * Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + 2 + 1)) *
      (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s + 1 / 2) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t * y₁ / y₂ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (t * y₁ / y₂ / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ)) * ((y₂ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ) - cP - 2 * s - 3) *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) := by
  subst ha1 hb hd

  obtain rfl : c = 0 := by rw [hc]; decide
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat] at hδpar
  obtain rfl := (by decide : ∀ x : ZMod 2, (1 : ZMod 2) = x + 1 → x = 0) a₀ hδpar
  subst hP₂
  simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one, Nat.cast_zero, Nat.cast_one] at hDpar hWt hWm ⊢
  have eτ : 0 < t * y₁ / y₂ := by positivity
  rw [show (-1 : ℝ) * t * y₁ / y₂ = -(t * y₁ / y₂) by ring,
    show (-1 : ℝ) * -t * y₁ / y₂ = t * y₁ / y₂ by ring,
    show (-1 : ℝ) * t * -y₁ / y₂ = t * y₁ / y₂ by ring,
    show (-1 : ℝ) * -t * -y₁ / y₂ = -(t * y₁ / y₂) by ring]
  rw [hDpar _ eτ, hρ _ eτ, hWm]
  rw [show (-y₁) * y₂ = -(y₁ * y₂) by ring, inv_neg,
    quasiChar_neg _ _ _ (by positivity), quasiChar_of_pos _ _ (by positivity : (0:ℝ) < (y₁ * y₂)⁻¹)]
  simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one]
  rw [Complex.ofReal_neg ((y₁ * y₂)⁻¹)]
  have hcc : ArchR.centralChar (RealArchParam.principal μ₁ 0 μ₂ 0) y₂ = ((y₂ : ℝ) : ℂ) ^ (μ₁ + μ₂) := by
    unfold ArchR.centralChar; rw [quasiChar_of_pos _ _ hy₂]; rfl
  have hce : (RealArchParam.principal μ₁ 0 μ₂ 0).centralExponent = μ₁ + μ₂ := rfl
  rw [hcc, hce]
  have r1 : |(y₁ * y₂)⁻¹| = (y₁ * y₂)⁻¹ := abs_of_pos (by positivity)
  have r2 : |(-((y₁ * y₂)⁻¹))| = (y₁ * y₂)⁻¹ := by rw [abs_neg, r1]
  have r3 : |y₁ * y₂| = y₁ * y₂ := abs_of_pos (by positivity)
  have r4 : |(-(y₁ * y₂))| = y₁ * y₂ := by rw [abs_neg, r3]
  have r5 : |y₂| = y₂ := abs_of_pos hy₂
  have r6 : |y₁| = y₁ := abs_of_pos hy₁
  have r7 : |(-y₁)| = y₁ := by rw [abs_neg, r6]
  have r8 : |t| = t := abs_of_pos ht
  have r9 : |(-t)| = t := by rw [abs_neg, r8]
  rw [r2, r4, r1, r3, r5, r7, r6, r9, r8, neg_sq t, neg_sq y₁]
  have hI2 : ∀ X : ℂ, X * (-Complex.I * ((-1 : ℝ) : ℂ)) ^ 2 * (-Complex.I * ((y₂ : ℝ) : ℂ)) ^ 2 = X * ((y₂ : ℝ) : ℂ) ^ 2 := by
    intro X
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination (X * (y₂ : ℂ) ^ 2 * (Complex.I * Complex.I - 1)) * hI
  simp only [hI2]
  have he1 : ((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℝ) : ℂ) =
        ((Real.exp (-(Real.pi / y₁ ^ 2)) : ℝ) : ℂ) * ((Real.exp (-(Real.pi / y₂ ^ 2)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1; congr 1; ring
  have he2 : ∀ T : ℝ, T ^ 2 = t ^ 2 →
      ((Real.exp (-(Real.pi * ((-1 * T) ^ 2 * y₁ ^ 2))) : ℝ) : ℂ) = ((Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℝ) : ℂ) := by
    intro T hT
    congr 1; congr 1
    rw [mul_pow, hT]; ring
  rw [he1, he2 t rfl, he2 (-t) (neg_sq t)]
  have hk1 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * t * y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) - 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk2 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * -t * y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) + 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk3 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * t * -y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) + 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  have hk4 : ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * -1 * -t * -y₁ / y₂ : ℝ) : ℂ) =
      ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) - 2 * (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by
    push_cast; ring
  rw [hk1, hk2, hk3, hk4]
  have hW2 : (2 : ℂ) * W t = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) := by
    linear_combination hWt + (1 : ℂ) * hWm

  set Ec : ℂ := ((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - (-1) ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) : ℝ) : ℂ) with hEc
  set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
  set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
          ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
            (((t * y₁ / y₂ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (t * y₁ / y₂ / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
  set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2) with htα
  set tα2 : ℂ := ((t : ℝ) : ℂ) ^ (s + 1 / 2) with htα2
  set E1 : ℂ := ((Real.exp (-(Real.pi / y₁ ^ 2)) : ℝ) : ℂ) with hE1
  set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℝ) : ℂ) with hEt
  set E2 : ℂ := ((Real.exp (-(Real.pi / y₂ ^ 2)) : ℝ) : ℂ) with hE2
  set cA : ℂ := (((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ (u₀ + 2) with hcA
  set cY : ℂ := ((y₂ : ℝ) : ℂ) ^ (μ₁ + μ₂) with hcY
  set cB : ℂ := ((Real.pi * (-1) ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2)) with hcB
  set Gm : ℂ := Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2) with hGm
  set GR : ℂ := Complex.Gammaℝ (cP + (μ₁ + μ₂) + 2 * s + 2 + 1) with hGR
  set yβ : ℂ := ((y₁ : ℝ) : ℂ) ^ (-u₀ - 1) with hyβ
  set yγ : ℂ := ((y₂ : ℝ) : ℂ) ^ (-u₀ - 1 - cP - 2 * s - 3) with hyγ
  set Wt : ℂ := W t with hWt0
  set τc : ℂ := ((t * y₁ / y₂ : ℝ) : ℂ) with hτc
  have hτc' : τc = (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by rw [hτc]; push_cast; ring

  have hp : cA * cY * cB * Gm * tα * ((t : ℝ) : ℂ) * (((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) = GR * tα2 * yβ * yγ := by
    have hp0 : cA * cY * cB * tα * ((t : ℝ) : ℂ) * (((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) =
        ((Real.pi : ℝ) : ℂ) ^ (-(cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2) * tα2 * yβ * yγ := by
      have hb1 : (0 : ℝ) < (y₁ * y₂)⁻¹ := by positivity
      have hb3 : (0 : ℝ) < Real.pi * (-1) ^ 2 * y₂ ^ 2 := by positivity
      rw [hcA, hcY, hcB, htα, htα2, hyβ, hyγ, ofReal_cpow_eq_exp hb1, ofReal_cpow_eq_exp hy₂, ofReal_cpow_eq_exp hb3,
        ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp Real.pi_pos, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hy₁, ofReal_cpow_eq_exp hy₂,
        ofReal_eq_exp_log ht, ofReal_eq_exp_log hy₁, ofReal_eq_exp_log hy₂, Real.log_inv, Real.log_mul hy₁.ne' hy₂.ne',
        show Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 = Real.pi * y₂ ^ 2 by ring,
        Real.log_mul Real.pi_pos.ne' (pow_ne_zero 2 hy₂.ne'), Real.log_pow]
      simp only [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hGR, Complex.Gammaℝ_def, hGm]
    linear_combination (Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 2 + 1) / 2)) * hp0
  have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
  have hy10 : ((y₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₁.ne'
  have hy20 : ((y₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₂.ne'
  rw [hτc']
  clear_value Ec Gpt Gqτ tα tα2 E1 Et E2 cA cY cB Gm GR yβ yγ Wt τc
  have hJ : ((((y₁ * y₂)⁻¹ ^ 2)⁻¹ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) * ((y₁ * y₂ : ℝ) : ℂ)) * ((y₂ : ℝ) : ℂ) ^ 2 * (1 / 2 : ℂ) *
      ((y₂ ^ 2 * ((y₁ * y₂) ^ 4)⁻¹ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
      (((t : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) / ((y₂ : ℝ) : ℂ)) * (8 * ((t : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) / ((y₂ : ℝ) : ℂ)) = 4 * (((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) := by
    push_cast
    field_simp
    try ring
  linear_combination ((-1 : ℂ) * ρ * Gqτ * Wt * cA * cY * cB * Gm * tα * E1 * Et * E2) * hJ +
    (2 * (((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ)) * (-1 : ℂ) * ρ * Gqτ * cA * cY * cB * Gm * tα * E1 * Et * E2) * hW2 +
    (2 * (-1 : ℂ) * ρ * Gqτ * Gpt * E1 * Et * E2) * hp

theorem pointwise (ν₁ ν₂ : ℂ) (b c : ZMod 2) (hc : c = b + 1)
    (W : ℝ → ℂ) (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (a₀ : ZMod 2)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) (s : ℂ)
    (t y₁ y₂ : ℝ) (ht : 0 < t) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (hWt : W t + (-1 : ℂ) ^ b.val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWm : W (-t) = (-1 : ℂ) ^ b.val * W t) :
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * y₁ / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * (-t) ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * (-t) * y₁ / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((((-y₁) * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * (-y₁) / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * (-y₁) ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * (-y₁) / y₂ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((((-y₁) * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * (-y₁) / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * (-t) ^ 2 * (-y₁) ^ 2 + 1 / (2 * Real.pi) + 2 * a * (-t) * (-y₁) / y₂ : ℝ)) : ℂ)))) =
    ((-1 : ℂ) ^ b.val * ρ * 2 * Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + 2 + 1)) *
      (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s + 1 / 2) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t * y₁ / y₂ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (t * y₁ / y₂ / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ)) * ((y₂ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ) - cP - 2 * s - 3) *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) := by
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b with hb | hb <;> rcases hδ with hd | hd
  · exact pointwise00 ν₁ ν₂ b c hc W μ₁ μ₂ D hP₂ ρ hρ hDpar a ha1 u₀ cP a₀ δ (Or.inl hd) hδpar s t y₁ y₂ ht hy₁ hy₂ hWt hWm hb hd
  · exact pointwise01 ν₁ ν₂ b c hc W μ₁ μ₂ D hP₂ ρ hρ hDpar a ha1 u₀ cP a₀ δ (Or.inr hd) hδpar s t y₁ y₂ ht hy₁ hy₂ hWt hWm hb hd
  · exact pointwise10 ν₁ ν₂ b c hc W μ₁ μ₂ D hP₂ ρ hρ hDpar a ha1 u₀ cP a₀ δ (Or.inl hd) hδpar s t y₁ y₂ ht hy₁ hy₂ hWt hWm hb hd
  · exact pointwise11 ν₁ ν₂ b c hc W μ₁ μ₂ D hP₂ ρ hρ hDpar a ha1 u₀ cP a₀ δ (Or.inr hd) hδpar s t y₁ y₂ ht hy₁ hy₂ hWt hWm hb hd

end S2Q48

open S2Q48 Set in

theorem solution
    (ν₁ ν₂ : ℂ) (b c : ZMod 2) (hc : c = b + 1)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ : ZMod 2)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      ∫ q : ℝ × ℝ × ℝ,
        (ArchR.quasiChar (u₀ + 2) a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
          ((((q.2.1 * q.2.2)⁻¹ : ℝ) : ℂ) ^ δ * ((|q.2.1 * q.2.2| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (q.2.2 : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) * ((|q.2.1| : ℝ) : ℂ)) *
          (W q.1 * D.W (ArchR.diagOne (a * q.1 * q.2.1 / q.2.2)) * (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.1 ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * q.1) ^ 2 * q.2.1 ^ 2))) : ℂ) * (((1 / q.2.1 ^ 2 - 1 / q.2.2 ^ 2 - a ^ 2 * q.1 ^ 2 * q.2.1 ^ 2 + 1 / (2 * Real.pi) + 2 * a * q.1 * q.2.1 / q.2.2 : ℝ)) : ℂ))))
        ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) =
      (-1 : ℂ) ^ b.val * ρ *
        ((Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + u₀) + signShift (b + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + u₀) + signShift (b + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₁) + signShift (b + c))) *
            Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₁) + signShift (b + c)))) *
            (Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₂) + signShift (b + c))) *
              Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₂) + signShift (b + c)))))) := by
  have ha : a ≠ 0 := by rw [ha1]; norm_num

  obtain ⟨σI, hI⟩ :=
    LanglandsTunnell.Converse.exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
      ν₁ ν₂ b W hWc hW hWpar D a ha (u₀ + 2) cP a₀ δ hδ
  have hce : P₂.centralExponent = μ₁ + μ₂ := by rw [hP₂]; rfl
  have hδre : ((δ : ℕ) : ℂ).re = 0 ∨ ((δ : ℕ) : ℂ).re = 1 := by
    rcases hδ with rfl | rfl <;> simp
  set R : ℝ := |u₀.re| + |ν₁.re| + |ν₂.re| + |μ₁.re| + |μ₂.re| + |cP.re| + 4 with hR
  refine ⟨max σI R, fun s hs => ?_⟩
  have hsI : σI < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsR : R < s.re := lt_of_le_of_lt (le_max_right _ _) hs

  obtain ⟨F, hFdef⟩ : ∃ F : ℝ × ℝ × ℝ → ℂ, F = fun q : ℝ × ℝ × ℝ =>
        (ArchR.quasiChar (u₀ + 2) a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
          ((((q.2.1 * q.2.2)⁻¹ : ℝ) : ℂ) ^ δ * ((|q.2.1 * q.2.2| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (q.2.2 : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) * ((|q.2.1| : ℝ) : ℂ)) *
          (W q.1 * D.W (ArchR.diagOne (a * q.1 * q.2.1 / q.2.2)) * (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.1 ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * q.1) ^ 2 * q.2.1 ^ 2))) : ℂ) * (((1 / q.2.1 ^ 2 - 1 / q.2.2 ^ 2 - a ^ 2 * q.1 ^ 2 * q.2.1 ^ 2 + 1 / (2 * Real.pi) + 2 * a * q.1 * q.2.1 / q.2.2 : ℝ)) : ℂ)))) := ⟨_, rfl⟩
  rw [show (fun q : ℝ × ℝ × ℝ =>
        (ArchR.quasiChar (u₀ + 2) a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
          ((((q.2.1 * q.2.2)⁻¹ : ℝ) : ℂ) ^ δ * ((|q.2.1 * q.2.2| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (q.2.2 : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) * ((|q.2.1| : ℝ) : ℂ)) *
          (W q.1 * D.W (ArchR.diagOne (a * q.1 * q.2.1 / q.2.2)) * (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.1 ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * q.1) ^ 2 * q.2.1 ^ 2))) : ℂ) * (((1 / q.2.1 ^ 2 - 1 / q.2.2 ^ 2 - a ^ 2 * q.1 ^ 2 * q.2.1 ^ 2 + 1 / (2 * Real.pi) + 2 * a * q.1 * q.2.1 / q.2.2 : ℝ)) : ℂ))))) = F from hFdef.symm]
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi 0) with hν

  have hFint : Integrable F ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) := by
    have h := hI s hsI
    rw [hFdef]
    exact h

  have hΦ : MeasurePreserving (⇑(MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) :=
    measurePreserving_prodAssoc _ _ _
  have hFa : Integrable (F ∘ ⇑(MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) :=
    (hΦ.integrable_comp hFint.aestronglyMeasurable).2 hFint
  have step0 : ∫ q, F q ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) =
      ∫ p : (ℝ × ℝ) × ℝ, F (p.1.1, p.1.2, p.2) ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) := by
    rw [← hΦ.integral_comp (MeasurableEquiv.prodAssoc).measurableEmbedding]
    rfl

  have step1 : ∫ p : (ℝ × ℝ) × ℝ, F (p.1.1, p.1.2, p.2) ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) =
      ∫ p : ℝ × ℝ, (∫ y₂, F (p.1, p.2, y₂) ∂ν) ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    integral_prod (f := fun p : (ℝ × ℝ) × ℝ => F (p.1.1, p.1.2, p.2)) hFa
  have hh : Integrable (fun p : ℝ × ℝ => ∫ y₂, F (p.1, p.2, y₂) ∂ν) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    hFa.integral_prod_left
  have step2 := LanglandsTunnell.integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
    (fun p : ℝ × ℝ => ∫ y₂, F (p.1, p.2, y₂) ∂ν) hh

  have hsl : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume : Measure ℝ)), Integrable (fun y₂ => F (p.1, p.2, y₂)) ν :=
    hFa.prod_right_ae
  have hmp1 : MeasurePreserving (fun p : ℝ × ℝ => (-p.1, p.2)) ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id (volume : Measure ℝ))
  have hmp2 : MeasurePreserving (fun p : ℝ × ℝ => (p.1, -p.2)) ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hsl2 := hmp1.quasiMeasurePreserving.ae hsl
  have hsl3 := hmp2.quasiMeasurePreserving.ae hsl
  have hsl4 := hmp1.quasiMeasurePreserving.ae hsl3
  simp only at hsl2 hsl3 hsl4

  have key : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume : Measure ℝ)), 0 < p.1 → 0 < p.2 →
      (∫ y₂, F (p.1, p.2, y₂) ∂ν) + (∫ y₂, F (-p.1, p.2, y₂) ∂ν) + (∫ y₂, F (p.1, -p.2, y₂) ∂ν) +
        (∫ y₂, F (-p.1, -p.2, y₂) ∂ν) =
      ((-1 : ℂ) ^ b.val * ρ * 2 * Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + 2 + 1)) *
        ∫ y₂ in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((p.1) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((p.1) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p.1 : ℝ) : ℂ) ^ (s + 1 / 2) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((p.1 * p.2 / y₂ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (p.1 * p.2 / y₂ / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p.2 : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ)) * ((y₂ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ) - cP - 2 * s - 3) *
          (Real.exp (-(Real.pi / p.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * p.1 ^ 2 * p.2 ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) := by
    filter_upwards [hsl, hsl2, hsl3, hsl4] with p i1 i2 i3 i4 ht hy
    have i12 : Integrable (fun y₂ => F (p.1, p.2, y₂) + F (-p.1, p.2, y₂)) ν := i1.add i2
    have i123 : Integrable (fun y₂ => F (p.1, p.2, y₂) + F (-p.1, p.2, y₂) + F (p.1, -p.2, y₂)) ν := i12.add i3
    rw [← integral_add i1 i2, ← integral_add i12 i3, ← integral_add i123 i4, hν, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y₂ hy₂ => ?_
    have hy₂ : 0 < y₂ := hy₂
    rw [hFdef]
    exact S2Q48.pointwise ν₁ ν₂ b c hc W μ₁ μ₂ D hP₂ ρ hρ hDpar a ha1 u₀ cP a₀ δ hδ hδpar s p.1 p.2 y₂ ht hy hy₂
      (hW p.1 ht) (hWpar p.1)

  have key' := Measure.ae_ae_of_ae_prod key
  dsimp only at key' step2

  have hbc1 : b + c = 1 := by
    have h2 := (by decide : ∀ x : ZMod 2, x + (x + 1) = 1) b
    rw [hc]; exact h2
  have hs1 : signShift (b + c) = 1 := by
    unfold signShift; rw [hbc1]; simp
  have hsδ : signShift (b + a₀) = ((δ : ℕ) : ℂ) := by
    unfold signShift
    rcases hδ with rfl | rfl
    · have hba : b + a₀ = 0 := by
        have h := hδpar.symm; push_cast at h; rw [add_comm] at h; exact h
      rw [hba]; simp
    · have hba : b + a₀ = 1 := by
        have h := hδpar.symm; push_cast at h; rw [add_comm] at h; exact h
      rw [hba]; simp
  have habs : ∀ x : ℝ, -|x| ≤ x ∧ x ≤ |x| := fun x => ⟨neg_abs_le x, le_abs_self x⟩
  obtain ⟨hu1, hu2⟩ := habs u₀.re
  obtain ⟨hn11, hn12⟩ := habs ν₁.re
  obtain ⟨hn21, hn22⟩ := habs ν₂.re
  obtain ⟨hm11, hm12⟩ := habs μ₁.re
  obtain ⟨hm21, hm22⟩ := habs μ₂.re
  obtain ⟨hc1, hc2⟩ := habs cP.re
  have hR' : |u₀.re| + |ν₁.re| + |ν₂.re| + |μ₁.re| + |μ₂.re| + |cP.re| + 4 < s.re := by rw [hR] at hsR; exact hsR
  have hbal : (-u₀ - (δ : ℂ)) - (-u₀ - (δ : ℂ) - cP - 2 * s - 3) = 2 * (s + 1 / 2) + 2 + ν₁ + ν₂ := by
    rw [hcP]; ring
  have hK8 := LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
    ν₁ ν₂ μ₁ μ₂ (s + 1 / 2) (-u₀ - (δ : ℂ)) (-u₀ - (δ : ℂ) - cP - 2 * s - 3) hbal
    (by rcases hδre with h | h <;> (simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.div_ofNat_re, h]; linarith))
    (by rcases hδre with h | h <;> (simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.div_ofNat_re, h]; linarith))
    (by simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]; linarith)
    (by simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]; linarith)
    (by simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]; linarith)
    (by simp only [Complex.add_re, Complex.one_re, Complex.div_ofNat_re]; linarith)
  have hwre : 0 < (cP + P₂.centralExponent + 2 * s + 2 + 1).re := by
    rw [hce]
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, zero_mul, sub_zero]
    linarith
  have hΓne : Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + 2 + 1) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hwre

  rw [step0, step1, step2]
  have step3 : ∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ),
      ((∫ y₂, F (t, y₁, y₂) ∂ν) + (∫ y₂, F (-t, y₁, y₂) ∂ν) + (∫ y₂, F (t, -y₁, y₂) ∂ν) + (∫ y₂, F (-t, -y₁, y₂) ∂ν)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ),
        ((-1 : ℂ) ^ b.val * ρ * 2 * Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + 2 + 1)) *
          ∫ y₂ in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s + 1 / 2) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t * y₁ / y₂ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (t * y₁ / y₂ / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ)) * ((y₂ : ℝ) : ℂ) ^ (-u₀ - (δ : ℂ) - cP - 2 * s - 3) *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae key'] with t ht hk
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hk] with y₁ hy hk2
    exact hk2 ht hy
  rw [step3]
  simp only [integral_const_mul]
  rw [hK8, hsδ, hs1]
  have e0 : Complex.Gammaℝ (-u₀ - (δ : ℂ) - (-u₀ - (δ : ℂ) - cP - 2 * s - 3) + μ₁ + μ₂) =
      Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + 2 + 1) := by rw [hce]; congr 1; ring
  have e1 : Complex.Gammaℝ (s + 1 / 2 - (-u₀ - (δ : ℂ)) + ν₁) =
      Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + u₀) + (δ : ℂ))) := by congr 1; ring
  have e2 : Complex.Gammaℝ (s + 1 / 2 - (-u₀ - (δ : ℂ)) + ν₂) =
      Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + u₀) + (δ : ℂ))) := by congr 1; ring
  have e3 : Complex.Gammaℝ (s + 1 / 2 + 1 + ν₁ + μ₁) =
      Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₁) + 1)) := by congr 1; ring
  have e4 : Complex.Gammaℝ (s + 1 / 2 + 1 + ν₁ + μ₂) =
      Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₂) + 1)) := by congr 1; ring
  have e5 : Complex.Gammaℝ (s + 1 / 2 + 1 + ν₂ + μ₁) =
      Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₁) + 1)) := by congr 1; ring
  have e6 : Complex.Gammaℝ (s + 1 / 2 + 1 + ν₂ + μ₂) =
      Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₂) + 1)) := by congr 1; ring
  rw [e0, e1, e2, e3, e4, e5, e6]
  revert hΓne
  generalize Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + 2 + 1) = G
  generalize Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + u₀) + (δ : ℂ))) = A₁
  generalize Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + u₀) + (δ : ℂ))) = A₂
  generalize Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₁) + 1)) = B₁
  generalize Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₂) + 1)) = B₂
  generalize Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₁) + 1)) = B₃
  generalize Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₂) + 1)) = B₄
  generalize ((-1 : ℂ) ^ b.val) = ε
  intro hΓne
  have hfin : ∀ Y : ℂ, ε * ρ * 2 * G * (1 / 2 * Y / G) = ε * ρ * Y := by
    intro Y
    rw [show ε * ρ * 2 * G * (1 / 2 * Y / G) = ε * ρ * Y * (G / G) by ring, div_self hΓne, mul_one]
  rw [hfin]
  ring

end S_LanglandsTunnell_Converse_integral_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_eq_mul_prod_GammaR_of_weightZeroProfile
end P2MW
export P2MW.S_LanglandsTunnell_Converse_integral_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_eq_mul_prod_GammaR_of_weightZeroProfile (solution)
