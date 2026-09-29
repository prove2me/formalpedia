-- Prove2me | solution 1 for LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_blockHarmonic_eq_mul_prod_GammaR
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/9560b068-feeb-5a58-b931-e7e51159c090

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

import Theorems.Thm_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
import Theorems.Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_blockHarmonic_of_mulConvGaussian_sheets
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_blockHarmonic_eq_mul_prod_GammaR

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

namespace S2M9

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

theorem pointwise (ν₁ ν₂ : ℂ) (a₁ a₂ c : ZMod 2)
    (W : ℝ → ℂ) (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (a₀ : ZMod 2) (ha₀ : a₀ = c) (s : ℂ)
    (t y₁ y₂ : ℝ) (ht : 0 < t) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂)
    (hWt : W t + (-1 : ℂ) ^ c.val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + c)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + c)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ + 1 / y₂ - a * t * y₁ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * y₁ / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ + 1 / y₂ - a * (-t) * y₁ : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * (-y₁) / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) + 1 / y₂ - a * t * (-y₁) : ℝ)) : ℂ)))) +
    (ArchR.quasiChar (u₀ + 2) a₀ ((-y₁) * y₂)⁻¹ * (((|((-y₁) * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|(-y₁) * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) * (-Complex.I * (y₂ : ℂ)) *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 1 + 1) / 2))) *
          ((y₂ ^ 2 * (|(-y₁) * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / (-y₁) ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|(-y₁)| : ℝ) : ℂ)) *
          (W (-t) * D.W (ArchR.diagOne (a * (-t) * (-y₁) / y₂)) * (((|(-t)| : ℝ) : ℂ) ^ (s - 1 / 2)) * ((((-t) ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * (-t)) ^ 2 * (-y₁) ^ 2))) : ℂ) * (((1 / (-y₁) + 1 / y₂ - a * (-t) * (-y₁) : ℝ)) : ℂ)))) =
    ((-1 : ℂ) ^ c.val * ρ * Complex.Gammaℝ (cP + P₂.centralExponent + 2 * s + 1 + 1)) *
      (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + c)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + c)) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ μ₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ μ₂ * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((y₁ : ℝ) : ℂ) ^ (-u₀ - 1) * ((y₂ : ℝ) : ℂ) ^ (-u₀ - cP - 2 * s - 3) *
          (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)) := by
  subst ha1
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · subst ha₀ hP₂
    simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one] at hDpar hWt ⊢
    have eτ : 0 < t * y₁ / y₂ := by positivity
    rw [show (-1 : ℝ) * t * y₁ / y₂ = -(t * y₁ / y₂) by ring,
      show (-1 : ℝ) * -t * y₁ / y₂ = t * y₁ / y₂ by ring,
      show (-1 : ℝ) * t * -y₁ / y₂ = t * y₁ / y₂ by ring,
      show (-1 : ℝ) * -t * -y₁ / y₂ = -(t * y₁ / y₂) by ring]
    rw [hDpar _ eτ, hρ _ eτ]
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
    have hIy : ∀ X : ℂ, X * (-Complex.I * ((-1 : ℝ) : ℂ)) * (-Complex.I * ((y₂ : ℝ) : ℂ)) = X * ((y₂ : ℝ) : ℂ) := by
      intro X
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      linear_combination (-(X * (y₂ : ℂ))) * hI
    simp only [hIy]
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
    have hk1 : ((1 / y₁ + 1 / y₂ - -1 * t * y₁ : ℝ) : ℂ) = ((y₁ : ℝ) : ℂ)⁻¹ + ((y₂ : ℝ) : ℂ)⁻¹ + (t : ℂ) * (y₁ : ℂ) := by
      push_cast; ring
    have hk2 : ((1 / y₁ + 1 / y₂ - -1 * -t * y₁ : ℝ) : ℂ) = ((y₁ : ℝ) : ℂ)⁻¹ + ((y₂ : ℝ) : ℂ)⁻¹ - (t : ℂ) * (y₁ : ℂ) := by
      push_cast; ring
    have hk3 : ((1 / -y₁ + 1 / y₂ - -1 * t * -y₁ : ℝ) : ℂ) = -((y₁ : ℝ) : ℂ)⁻¹ + ((y₂ : ℝ) : ℂ)⁻¹ - (t : ℂ) * (y₁ : ℂ) := by
      rw [div_neg]; push_cast; ring
    have hk4 : ((1 / -y₁ + 1 / y₂ - -1 * -t * -y₁ : ℝ) : ℂ) = -((y₁ : ℝ) : ℂ)⁻¹ + ((y₂ : ℝ) : ℂ)⁻¹ + (t : ℂ) * (y₁ : ℂ) := by
      rw [div_neg]; push_cast; ring
    rw [hk1, hk2, hk3, hk4]
    rw [eq_sub_of_add_eq hWt]

    set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + 0)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + 0)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
    set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
    set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2) with htα
    set E1 : ℂ := ((Real.exp (-(Real.pi / y₁ ^ 2)) : ℝ) : ℂ) with hE1
    set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℝ) : ℂ) with hEt
    set E2 : ℂ := ((Real.exp (-(Real.pi / y₂ ^ 2)) : ℝ) : ℂ) with hE2
    set cA : ℂ := (((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ (u₀ + 2) with hcA
    set cY : ℂ := ((y₂ : ℝ) : ℂ) ^ (μ₁ + μ₂) with hcY
    set cB : ℂ := ((Real.pi * (-1) ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + (μ₁ + μ₂) + 2 * s + 1 + 1) / 2)) with hcB
    set Gm : ℂ := Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 1 + 1) / 2) with hGm
    set GR : ℂ := Complex.Gammaℝ (cP + (μ₁ + μ₂) + 2 * s + 1 + 1) with hGR
    set yβ : ℂ := ((y₁ : ℝ) : ℂ) ^ (-u₀ - 1) with hyβ
    set yγ : ℂ := ((y₂ : ℝ) : ℂ) ^ (-u₀ - cP - 2 * s - 3) with hyγ
    set Wm : ℂ := W (-t) with hWm
    set τc : ℂ := ((t * y₁ / y₂ : ℝ) : ℂ) with hτc
    have hτc' : τc = (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by rw [hτc]; push_cast; ring

    have hp : cA * cY * cB * Gm * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) = GR * yβ * yγ := by
      have hp0 : cA * cY * cB * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) ^ (-(cP + (μ₁ + μ₂) + 2 * s + 1 + 1) / 2) * yβ * yγ := by
        have hb1 : (0 : ℝ) < (y₁ * y₂)⁻¹ := by positivity
        have hb3 : (0 : ℝ) < Real.pi * (-1) ^ 2 * y₂ ^ 2 := by positivity
        rw [hcA, hcY, hcB, hyβ, hyγ, ofReal_cpow_eq_exp hb1, ofReal_cpow_eq_exp hy₂, ofReal_cpow_eq_exp hb3,
          ofReal_cpow_eq_exp Real.pi_pos, ofReal_cpow_eq_exp hy₁, ofReal_cpow_eq_exp hy₂, ofReal_eq_exp_log hy₁,
          ofReal_eq_exp_log hy₂, Real.log_inv, Real.log_mul hy₁.ne' hy₂.ne',
          show Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 = Real.pi * y₂ ^ 2 by ring,
          Real.log_mul Real.pi_pos.ne' (pow_ne_zero 2 hy₂.ne'), Real.log_pow]
        simp only [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hGR, Complex.Gammaℝ_def, hGm]
      linear_combination (Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 1 + 1) / 2)) * hp0
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    have hy10 : ((y₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₁.ne'
    have hy20 : ((y₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₂.ne'
    rw [hτc']
    clear_value Gpt Gqτ tα E1 Et E2 cA cY cB Gm GR yβ yγ Wm τc
    have hJ : ((((y₁ * y₂)⁻¹ ^ 2)⁻¹ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₁ * y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * (1 / 2 : ℂ) *
        ((y₂ ^ 2 * ((y₁ * y₂) ^ 4)⁻¹ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * (((t ^ 2)⁻¹ : ℝ) : ℂ) * (2 * ((y₂ : ℝ) : ℂ)⁻¹) *
        ((t : ℝ) : ℂ) * (((t : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) / ((y₂ : ℝ) : ℂ)) = ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) := by
      push_cast
      field_simp
    linear_combination ((1 : ℂ) * ρ * Gpt * Gqτ * tα * E1 * Et * E2 * cA * cY * cB * Gm) * hJ +
      ((1 : ℂ) * ρ * Gpt * Gqτ * tα * E1 * Et * E2) * hp
  · subst ha₀ hP₂
    simp only [ZMod.val_zero, ZMod.val_one, pow_zero, pow_one] at hDpar hWt ⊢
    have eτ : 0 < t * y₁ / y₂ := by positivity
    rw [show (-1 : ℝ) * t * y₁ / y₂ = -(t * y₁ / y₂) by ring,
      show (-1 : ℝ) * -t * y₁ / y₂ = t * y₁ / y₂ by ring,
      show (-1 : ℝ) * t * -y₁ / y₂ = t * y₁ / y₂ by ring,
      show (-1 : ℝ) * -t * -y₁ / y₂ = -(t * y₁ / y₂) by ring]
    rw [hDpar _ eτ, hρ _ eτ]
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
    have hIy : ∀ X : ℂ, X * (-Complex.I * ((-1 : ℝ) : ℂ)) * (-Complex.I * ((y₂ : ℝ) : ℂ)) = X * ((y₂ : ℝ) : ℂ) := by
      intro X
      have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      linear_combination (-(X * (y₂ : ℂ))) * hI
    simp only [hIy]
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
    have hk1 : ((1 / y₁ + 1 / y₂ - -1 * t * y₁ : ℝ) : ℂ) = ((y₁ : ℝ) : ℂ)⁻¹ + ((y₂ : ℝ) : ℂ)⁻¹ + (t : ℂ) * (y₁ : ℂ) := by
      push_cast; ring
    have hk2 : ((1 / y₁ + 1 / y₂ - -1 * -t * y₁ : ℝ) : ℂ) = ((y₁ : ℝ) : ℂ)⁻¹ + ((y₂ : ℝ) : ℂ)⁻¹ - (t : ℂ) * (y₁ : ℂ) := by
      push_cast; ring
    have hk3 : ((1 / -y₁ + 1 / y₂ - -1 * t * -y₁ : ℝ) : ℂ) = -((y₁ : ℝ) : ℂ)⁻¹ + ((y₂ : ℝ) : ℂ)⁻¹ - (t : ℂ) * (y₁ : ℂ) := by
      rw [div_neg]; push_cast; ring
    have hk4 : ((1 / -y₁ + 1 / y₂ - -1 * -t * -y₁ : ℝ) : ℂ) = -((y₁ : ℝ) : ℂ)⁻¹ + ((y₂ : ℝ) : ℂ)⁻¹ + (t : ℂ) * (y₁ : ℂ) := by
      rw [div_neg]; push_cast; ring
    rw [hk1, hk2, hk3, hk4]
    rw [eq_sub_of_add_eq hWt]

    set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + 1)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + 1)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
    set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
    set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2) with htα
    set E1 : ℂ := ((Real.exp (-(Real.pi / y₁ ^ 2)) : ℝ) : ℂ) with hE1
    set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℝ) : ℂ) with hEt
    set E2 : ℂ := ((Real.exp (-(Real.pi / y₂ ^ 2)) : ℝ) : ℂ) with hE2
    set cA : ℂ := (((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ (u₀ + 2) with hcA
    set cY : ℂ := ((y₂ : ℝ) : ℂ) ^ (μ₁ + μ₂) with hcY
    set cB : ℂ := ((Real.pi * (-1) ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + (μ₁ + μ₂) + 2 * s + 1 + 1) / 2)) with hcB
    set Gm : ℂ := Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 1 + 1) / 2) with hGm
    set GR : ℂ := Complex.Gammaℝ (cP + (μ₁ + μ₂) + 2 * s + 1 + 1) with hGR
    set yβ : ℂ := ((y₁ : ℝ) : ℂ) ^ (-u₀ - 1) with hyβ
    set yγ : ℂ := ((y₂ : ℝ) : ℂ) ^ (-u₀ - cP - 2 * s - 3) with hyγ
    set Wm : ℂ := W (-t) with hWm
    set τc : ℂ := ((t * y₁ / y₂ : ℝ) : ℂ) with hτc
    have hτc' : τc = (t : ℂ) * (y₁ : ℂ) / (y₂ : ℂ) := by rw [hτc]; push_cast; ring

    have hp : cA * cY * cB * Gm * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) = GR * yβ * yγ := by
      have hp0 : cA * cY * cB * ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) ^ (-(cP + (μ₁ + μ₂) + 2 * s + 1 + 1) / 2) * yβ * yγ := by
        have hb1 : (0 : ℝ) < (y₁ * y₂)⁻¹ := by positivity
        have hb3 : (0 : ℝ) < Real.pi * (-1) ^ 2 * y₂ ^ 2 := by positivity
        rw [hcA, hcY, hcB, hyβ, hyγ, ofReal_cpow_eq_exp hb1, ofReal_cpow_eq_exp hy₂, ofReal_cpow_eq_exp hb3,
          ofReal_cpow_eq_exp Real.pi_pos, ofReal_cpow_eq_exp hy₁, ofReal_cpow_eq_exp hy₂, ofReal_eq_exp_log hy₁,
          ofReal_eq_exp_log hy₂, Real.log_inv, Real.log_mul hy₁.ne' hy₂.ne',
          show Real.pi * (-1 : ℝ) ^ 2 * y₂ ^ 2 = Real.pi * y₂ ^ 2 by ring,
          Real.log_mul Real.pi_pos.ne' (pow_ne_zero 2 hy₂.ne'), Real.log_pow]
        simp only [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hGR, Complex.Gammaℝ_def, hGm]
      linear_combination (Complex.Gamma ((cP + (μ₁ + μ₂) + 2 * s + 1 + 1) / 2)) * hp0
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    have hy10 : ((y₁ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₁.ne'
    have hy20 : ((y₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₂.ne'
    rw [hτc']
    clear_value Gpt Gqτ tα E1 Et E2 cA cY cB Gm GR yβ yγ Wm τc
    have hJ : ((((y₁ * y₂)⁻¹ ^ 2)⁻¹ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₁ * y₂ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) * (1 / 2 : ℂ) *
        ((y₂ ^ 2 * ((y₁ * y₂) ^ 4)⁻¹ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) * (((t ^ 2)⁻¹ : ℝ) : ℂ) * (2 * ((y₂ : ℝ) : ℂ)⁻¹) *
        ((t : ℝ) : ℂ) * (((t : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) / ((y₂ : ℝ) : ℂ)) = ((y₁ : ℝ) : ℂ) * ((y₂ : ℝ) : ℂ) := by
      push_cast
      field_simp
    linear_combination ((-1 : ℂ) * ρ * Gpt * Gqτ * tα * E1 * Et * E2 * cA * cY * cB * Gm) * hJ +
      ((-1 : ℂ) * ρ * Gpt * Gqτ * tα * E1 * Et * E2) * hp

theorem quasiChar_zero_pos (a : ZMod 2) {x : ℝ} (hx : 0 < x) : ArchR.quasiChar 0 a x = 1 := by
  rw [quasiChar_of_pos _ _ hx, Complex.cpow_zero]

theorem v0 : (0 : ZMod 2).val = 0 := rfl
theorem v1 : (1 : ZMod 2).val = 1 := rfl

theorem dual_pointwise (ν₁ ν₂ : ℂ) (a₁ a₂ c : ZMod 2) (h12 : a₁ ≠ a₂)
    (W : ℝ → ℂ) (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (a₀ sP : ZMod 2) (ha₀ : a₀ = c) (hsP : sP = a₁ + a₂) (s : ℂ)
    (t q p : ℝ) (ht : 0 < t) (hq : 0 < q) (hp0 : 0 < p)
    (hWt : W t + (-1 : ℂ) ^ (c + 1).val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + (c + 1))) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + (c + 1))) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 - (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) +
    (ArchR.quasiChar 0 sP (-(-t : ℝ)) * ArchR.quasiChar 0 a₀ (-(-t : ℝ)) * ArchR.quasiChar 0 1 (-t : ℝ) * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-(-t : ℝ)) * ((a : ℂ) + ((-t : ℝ) : ℂ) * (p : ℂ) ^ 2 - (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 (-t : ℝ) * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |(-t : ℝ)| * p / q))) *
          ((((|(-t : ℝ)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (-t : ℝ) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) +
    (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 1 (-q : ℝ) * ArchR.quasiChar 0 a₀ (-q : ℝ)) *
          (W (-t) * ((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 - (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * (((-q : ℝ)⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |t| * p / (-q : ℝ)))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|(-q : ℝ)| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / (-q : ℝ) ^ 2)) : ℂ)) +
    (ArchR.quasiChar 0 sP (-(-t : ℝ)) * ArchR.quasiChar 0 a₀ (-(-t : ℝ)) * ArchR.quasiChar 0 1 (-t : ℝ) * ArchR.quasiChar 0 1 (-q : ℝ) * ArchR.quasiChar 0 a₀ (-q : ℝ)) *
          (W (-(-t : ℝ)) * ((a : ℂ) + ((-t : ℝ) : ℂ) * (p : ℂ) ^ 2 - (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 (-t : ℝ) * (((-q : ℝ)⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |(-t : ℝ)| * p / (-q : ℝ)))) *
          ((((|(-t : ℝ)| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|(-q : ℝ)| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * (-t : ℝ) ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / (-q : ℝ) ^ 2)) : ℂ)) =
    (2 * (-1 : ℂ) ^ c.val * ρ) *
      (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + (c + 1))) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + (c + 1))) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (μ₁ + μ₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ μ₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ μ₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 1) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) := by
  subst ha1
  have hs1 : sP = 1 := by rw [hsP]; exact (by decide : ∀ x y : ZMod 2, x ≠ y → x + y = 1) a₁ a₂ h12
  subst hs1
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · subst ha₀ hP₂
    have hce : (RealArchParam.principal μ₁ 0 μ₂ 0).centralExponent = μ₁ + μ₂ := rfl
    rw [hce]
    rw [show ((0 : ZMod 2) + 1 : ZMod 2) = 1 by decide] at hWt ⊢
    simp only [v0, v1, pow_zero, pow_one, neg_neg] at hDpar hWt ⊢
    have eτ : 0 < t * p / q := by positivity
    have r8 : |t| = t := abs_of_pos ht
    have r9 : |(-t)| = t := by rw [abs_neg, r8]
    rw [r9, r8]
    rw [show (-1 : ℝ) * t * p / q = -(t * p / q) by ring,
      show (-1 : ℝ) * t * p / -q = t * p / q by ring]
    rw [hDpar _ eτ, hρ _ eτ]
    simp only [quasiChar_neg _ _ _ ht.ne', quasiChar_neg _ _ _ hq.ne', quasiChar_zero_pos _ ht, quasiChar_zero_pos _ hq,
      v0, v1, pow_zero, pow_one]
    have r5 : |q| = q := abs_of_pos hq
    have r7 : |(-q)| = q := by rw [abs_neg, r5]
    rw [r7, r5, neg_sq t, neg_sq q, inv_neg]
    have he1 : ((Real.exp (-(Real.pi * (-1) ^ 2 / p ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    have he2 : ((Real.exp (-(Real.pi * (-1) ^ 2 / q ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    rw [he1, he2]
    rw [eq_sub_of_add_eq hWt]
    set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + 1)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + 1)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
    set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
    set tA : ℂ := ((t : ℝ) : ℂ) ^ (s - 5 / 2 - cP - (μ₁ + μ₂)) with htA
    set qC : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 1) with hqC
    set pE : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 3) with hpE
    set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (μ₁ + μ₂)) with htα
    set pβ : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 1) with hpβ
    set qγ : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) with hqγ
    set E1 : ℂ := ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) with hE1
    set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℝ) : ℂ) with hEt
    set E2 : ℂ := ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) with hE2
    set Wm : ℂ := W (-t) with hWm
    set τc : ℂ := ((t * p / q : ℝ) : ℂ) with hτc
    have hτc' : τc = (t : ℂ) * (p : ℂ) / (q : ℂ) := by rw [hτc]; push_cast; ring
    have hp : tA * ((t : ℝ) : ℂ) * ((t : ℝ) : ℂ) * (pE * ((p : ℝ) : ℂ) * ((p : ℝ) : ℂ)) *
        (qC * ((q : ℝ) : ℂ)⁻¹ * ((q : ℝ) : ℂ)⁻¹) = tα * pβ * qγ := by
      rw [htA, hpE, hqC, htα, hpβ, hqγ, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_eq_exp_log ht, ofReal_eq_exp_log hp0, ofReal_eq_exp_log hq, ← Complex.exp_neg]
      simp only [← Complex.exp_add]
      congr 1
      ring
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    have hq0 : ((q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq.ne'
    have hp0' : ((p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp0.ne'
    rw [hτc']
    clear_value Gpt Gqτ tA qC pE tα pβ qγ E1 Et E2 Wm τc
    push_cast
    linear_combination (2 * (1 : ℂ) * ρ * Gpt * Gqτ * E1 * Et * E2) * hp
  · subst ha₀ hP₂
    have hce : (RealArchParam.principal μ₁ 1 μ₂ 1).centralExponent = μ₁ + μ₂ := rfl
    rw [hce]
    rw [show ((1 : ZMod 2) + 1 : ZMod 2) = 0 by decide] at hWt ⊢
    simp only [v0, v1, pow_zero, pow_one, neg_neg] at hDpar hWt ⊢
    have eτ : 0 < t * p / q := by positivity
    have r8 : |t| = t := abs_of_pos ht
    have r9 : |(-t)| = t := by rw [abs_neg, r8]
    rw [r9, r8]
    rw [show (-1 : ℝ) * t * p / q = -(t * p / q) by ring,
      show (-1 : ℝ) * t * p / -q = t * p / q by ring]
    rw [hDpar _ eτ, hρ _ eτ]
    simp only [quasiChar_neg _ _ _ ht.ne', quasiChar_neg _ _ _ hq.ne', quasiChar_zero_pos _ ht, quasiChar_zero_pos _ hq,
      v0, v1, pow_zero, pow_one]
    have r5 : |q| = q := abs_of_pos hq
    have r7 : |(-q)| = q := by rw [abs_neg, r5]
    rw [r7, r5, neg_sq t, neg_sq q, inv_neg]
    have he1 : ((Real.exp (-(Real.pi * (-1) ^ 2 / p ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    have he2 : ((Real.exp (-(Real.pi * (-1) ^ 2 / q ^ 2)) : ℝ) : ℂ) = ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) := by
      congr 1; congr 1; ring
    rw [he1, he2]
    rw [eq_sub_of_add_eq hWt]
    set Gpt : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + 0)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + 0)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGpt
    set Gqτ : ℂ := ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) with hGqτ
    set tA : ℂ := ((t : ℝ) : ℂ) ^ (s - 5 / 2 - cP - (μ₁ + μ₂)) with htA
    set qC : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 1) with hqC
    set pE : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 3) with hpE
    set tα : ℂ := ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (μ₁ + μ₂)) with htα
    set pβ : ℂ := ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 1) with hpβ
    set qγ : ℂ := ((q : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) with hqγ
    set E1 : ℂ := ((Real.exp (-(Real.pi / p ^ 2)) : ℝ) : ℂ) with hE1
    set Et : ℂ := ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℝ) : ℂ) with hEt
    set E2 : ℂ := ((Real.exp (-(Real.pi / q ^ 2)) : ℝ) : ℂ) with hE2
    set Wm : ℂ := W (-t) with hWm
    set τc : ℂ := ((t * p / q : ℝ) : ℂ) with hτc
    have hτc' : τc = (t : ℂ) * (p : ℂ) / (q : ℂ) := by rw [hτc]; push_cast; ring
    have hp : tA * ((t : ℝ) : ℂ) * ((t : ℝ) : ℂ) * (pE * ((p : ℝ) : ℂ) * ((p : ℝ) : ℂ)) *
        (qC * ((q : ℝ) : ℂ)⁻¹ * ((q : ℝ) : ℂ)⁻¹) = tα * pβ * qγ := by
      rw [htA, hpE, hqC, htα, hpβ, hqγ, ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_cpow_eq_exp ht, ofReal_cpow_eq_exp hp0, ofReal_cpow_eq_exp hq,
        ofReal_eq_exp_log ht, ofReal_eq_exp_log hp0, ofReal_eq_exp_log hq, ← Complex.exp_neg]
      simp only [← Complex.exp_add]
      congr 1
      ring
    have ht0 : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
    have hq0 : ((q : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq.ne'
    have hp0' : ((p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hp0.ne'
    rw [hτc']
    clear_value Gpt Gqτ tA qC pE tα pβ qγ E1 Et E2 Wm τc
    push_cast
    linear_combination (2 * (-1 : ℂ) * ρ * Gpt * Gqτ * E1 * Et * E2) * hp

end S2M9

open S2M9 Set in

theorem solution
    (ν₁ ν₂ : ℂ) (a₁ a₂ c : ZMod 2) (h12 : a₁ ≠ a₂)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (μ₁ μ₂ : ℂ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (ha₀ : a₀ = c) (hsP : sP = a₁ + a₂) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + 1 + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 - (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ c.val * ρ * ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (a₁ + c))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (a₂ + c)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₁) + signShift (a₁ + c))) *
            Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₁) + signShift (a₂ + c)))) *
            (Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₂) + signShift (a₁ + c))) *
              Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₂) + signShift (a₂ + c)))))) := by
  have ha : a ≠ 0 := by rw [ha1]; norm_num
  obtain ⟨σI, hI⟩ :=
    LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_blockHarmonic_of_mulConvGaussian_sheets
      ν₁ ν₂ a₁ a₂ W hWc hW D a ha u₀ cP a₀ sP
  have hce : P₂.centralExponent = μ₁ + μ₂ := by rw [hP₂]; rfl
  have hsre : ∀ z : ZMod 2, (signShift z).re = 0 ∨ (signShift z).re = 1 := by
    intro z; unfold signShift; split_ifs <;> simp
  set R : ℝ := |u₀.re| + |ν₁.re| + |ν₂.re| + |μ₁.re| + |μ₂.re| + |cP.re| + 4 with hR
  refine ⟨max σI R, fun s hs => ?_⟩
  have hsI : σI < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hsR : R < s.re := lt_of_le_of_lt (le_max_right _ _) hs

  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ → ℝ → ℂ, ∀ t q p : ℝ, F t q p =
        (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 1 q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 - (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ)) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) := ⟨_, fun _ _ _ => rfl⟩
  simp only [← hF]
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi 0) with hν

  have hbr : ∀ t q p : ℝ, (1 : ℂ) * (a : ℂ) + (1 : ℂ) * ((t : ℂ) * (p : ℂ) ^ 2) +
      (-1 : ℂ) * ((a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ)) =
      (a : ℂ) + (t : ℂ) * (p : ℂ) ^ 2 - (a : ℂ) * (p : ℂ) * ArchR.quasiChar 0 1 t * ((q⁻¹ : ℝ) : ℂ) := by
    intro t q p; ring
  have hFint : Integrable (fun x : ℝ × ℝ × ℝ => F x.1 x.2.1 x.2.2) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) := by
    have h := (hI s hsI).2 1 1 (-1)
    simp only [hbr] at h
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [hF]

  have hiter : (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ), F t q p) =
      ∫ x, F x.1 x.2.1 x.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) := by
    rw [integral_prod (f := fun x : ℝ × ℝ × ℝ => F x.1 x.2.1 x.2.2) hFint]
    refine integral_congr_ae ?_
    filter_upwards [hFint.prod_right_ae] with t ht
    exact (integral_prod (f := fun yz : ℝ × ℝ => F t yz.1 yz.2) ht).symm

  have hΦ : MeasurePreserving (⇑(MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) :=
    measurePreserving_prodAssoc _ _ _
  have hFa : Integrable ((fun x : ℝ × ℝ × ℝ => F x.1 x.2.1 x.2.2) ∘ ⇑(MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ))
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) :=
    (hΦ.integrable_comp hFint.aestronglyMeasurable).2 hFint
  have step0 : ∫ x, F x.1 x.2.1 x.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) =
      ∫ pr : (ℝ × ℝ) × ℝ, F pr.1.1 pr.1.2 pr.2 ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) := by
    rw [← hΦ.integral_comp (MeasurableEquiv.prodAssoc).measurableEmbedding]
    rfl
  have step1 : ∫ pr : (ℝ × ℝ) × ℝ, F pr.1.1 pr.1.2 pr.2 ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) =
      ∫ pq : ℝ × ℝ, (∫ p, F pq.1 pq.2 p ∂ν) ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    integral_prod (f := fun pr : (ℝ × ℝ) × ℝ => F pr.1.1 pr.1.2 pr.2) hFa
  have hh : Integrable (fun pq : ℝ × ℝ => ∫ p, F pq.1 pq.2 p ∂ν) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    hFa.integral_prod_left
  have step2 := LanglandsTunnell.integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
    (fun pq : ℝ × ℝ => ∫ p, F pq.1 pq.2 p ∂ν) hh
  have hsl : ∀ᵐ pq : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume : Measure ℝ)), Integrable (fun p => F pq.1 pq.2 p) ν :=
    hFa.prod_right_ae
  have hmp1 : MeasurePreserving (fun pq : ℝ × ℝ => (-pq.1, pq.2)) ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id (volume : Measure ℝ))
  have hmp2 : MeasurePreserving (fun pq : ℝ × ℝ => (pq.1, -pq.2)) ((volume : Measure ℝ).prod (volume : Measure ℝ))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hsl2 := hmp1.quasiMeasurePreserving.ae hsl
  have hsl3 := hmp2.quasiMeasurePreserving.ae hsl
  have hsl4 := hmp1.quasiMeasurePreserving.ae hsl3
  simp only at hsl2 hsl3 hsl4
  have hWt : ∀ t : ℝ, 0 < t → W t + (-1 : ℂ) ^ (c + 1).val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + (c + 1))) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + (c + 1))) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) :=
    hW (c + 1)

  have key : ∀ᵐ pq : ℝ × ℝ ∂((volume : Measure ℝ).prod (volume : Measure ℝ)), 0 < pq.1 → 0 < pq.2 →
      (∫ p, F pq.1 pq.2 p ∂ν) + (∫ p, F (-pq.1) pq.2 p ∂ν) + (∫ p, F pq.1 (-pq.2) p ∂ν) + (∫ p, F (-pq.1) (-pq.2) p ∂ν) =
      (2 * (-1 : ℂ) ^ c.val * ρ) * ∫ p in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + (c + 1))) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((pq.1 / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + (c + 1))) * (Real.exp (-(Real.pi * (pq.1 / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((pq.1 : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (μ₁ + μ₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ μ₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((pq.1 * p / pq.2) / r : ℝ) : ℂ) ^ μ₂ * (Real.exp (-(Real.pi * ((pq.1 * p / pq.2) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 1) * ((pq.2 : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * pq.1 ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / pq.2 ^ 2)) : ℂ)) := by
    filter_upwards [hsl, hsl2, hsl3, hsl4] with pq i1 i2 i3 i4 ht hq
    have i12 : Integrable (fun p => F pq.1 pq.2 p + F (-pq.1) pq.2 p) ν := i1.add i2
    have i123 : Integrable (fun p => F pq.1 pq.2 p + F (-pq.1) pq.2 p + F pq.1 (-pq.2) p) ν := i12.add i3
    rw [← integral_add i1 i2, ← integral_add i12 i3, ← integral_add i123 i4, hν, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun p hp => ?_
    have hp : 0 < p := hp
    rw [hF, hF, hF, hF]
    exact S2M9.dual_pointwise ν₁ ν₂ a₁ a₂ c h12 W μ₁ μ₂ D hP₂ ρ hρ hDpar a ha1 u₀ cP a₀ sP ha₀ hsP s pq.1 pq.2 p ht hq hp
      (hWt pq.1 ht)
  have key' := Measure.ae_ae_of_ae_prod key
  dsimp only at key' step2
  rw [hiter, step0, step1, step2]
  have step3 : ∫ t in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ),
      ((∫ p, F t q p ∂ν) + (∫ p, F (-t) q p ∂ν) + (∫ p, F t (-q) p ∂ν) + (∫ p, F (-t) (-q) p ∂ν)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ),
        (2 * (-1 : ℂ) ^ c.val * ρ) * ∫ p in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + (c + 1))) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + (c + 1))) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (μ₁ + μ₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ μ₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ μ₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 1) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae key'] with t ht hk
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hk] with q hq hk2
    exact hk2 ht hq
  rw [step3]
  simp only [integral_const_mul]

  rcases eq_or_ne ρ 0 with hρ0 | hρ0
  · simp [hρ0]
  have hCst : (2 * (-1 : ℂ) ^ c.val * ρ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ (by norm_num))) hρ0
  have hswap : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), 0 < t →
      (∫ q in Set.Ioi (0 : ℝ), ∫ p in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + (c + 1))) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + (c + 1))) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (μ₁ + μ₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ μ₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ μ₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 1) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ))) =
      ∫ p in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + (c + 1))) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + (c + 1))) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (μ₁ + μ₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ μ₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ μ₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 1) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) := by
    have hst : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), Integrable (fun qp : ℝ × ℝ => F t qp.1 qp.2) ((volume : Measure ℝ).prod ν) :=
      hFint.prod_right_ae
    have hst' : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), Integrable (fun qp : ℝ × ℝ => F (-t) qp.1 qp.2) ((volume : Measure ℝ).prod ν) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hst
    have hmq : MeasurePreserving (fun qp : ℝ × ℝ => (-qp.1, qp.2)) ((volume : Measure ℝ).prod ν) ((volume : Measure ℝ).prod ν) :=
      (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id ν)
    filter_upwards [hst, hst'] with t i1 i2 ht
    have i3 : Integrable (fun qp : ℝ × ℝ => F t (-qp.1) qp.2) ((volume : Measure ℝ).prod ν) :=
      (hmq.integrable_comp i1.aestronglyMeasurable).mpr i1
    have i4 : Integrable (fun qp : ℝ × ℝ => F (-t) (-qp.1) qp.2) ((volume : Measure ℝ).prod ν) :=
      (hmq.integrable_comp i2.aestronglyMeasurable).mpr i2
    have hsum0 : Integrable (fun qp : ℝ × ℝ => (2 * (-1 : ℂ) ^ c.val * ρ)⁻¹ *
        (F t qp.1 qp.2 + F (-t) qp.1 qp.2 + F t (-qp.1) qp.2 + F (-t) (-qp.1) qp.2))
        ((volume : Measure ℝ).prod ν) := (((i1.add i2).add i3).add i4).const_mul _
    have hmeas_eq : ((volume : Measure ℝ).prod ν) = ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioi 0) := by
      rw [hν, ← Measure.prod_restrict, Measure.restrict_univ]
    have hsum : Integrable (fun qp : ℝ × ℝ => (2 * (-1 : ℂ) ^ c.val * ρ)⁻¹ *
        (F t qp.1 qp.2 + F (-t) qp.1 qp.2 + F t (-qp.1) qp.2 + F (-t) (-qp.1) qp.2))
        (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict (Set.Ioi 0 ×ˢ Set.Ioi 0)) := by
      rw [hmeas_eq] at hsum0
      exact hsum0.mono_measure (Measure.restrict_mono (Set.prod_mono (Set.subset_univ _) subset_rfl) le_rfl)
    have hK : Integrable (Function.uncurry fun (q p : ℝ) => ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + (c + 1))) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + (c + 1))) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (μ₁ + μ₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ μ₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ μ₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 1) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ))
        (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) := by
      rw [Measure.prod_restrict]
      refine hsum.congr ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with qp hqp
      obtain ⟨hq, hp⟩ := hqp
      have hq : 0 < qp.1 := hq
      have hp : 0 < qp.2 := hp
      have e := S2M9.dual_pointwise ν₁ ν₂ a₁ a₂ c h12 W μ₁ μ₂ D hP₂ ρ hρ hDpar a ha1 u₀ cP a₀ sP ha₀ hsP s t qp.1 qp.2 ht hq hp
        (hWt t ht)
      rw [← hF, ← hF, ← hF, ← hF] at e
      dsimp only [Function.uncurry]
      rw [e, ← mul_assoc, inv_mul_cancel₀ hCst, one_mul]
    exact integral_integral_swap hK
  have step4 : ∫ t in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ), ∫ p in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + (c + 1))) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + (c + 1))) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (μ₁ + μ₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ μ₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ μ₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 1) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ p in Set.Ioi (0 : ℝ), ∫ q in Set.Ioi (0 : ℝ), (((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + (c + 1))) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((t / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + (c + 1))) * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((t : ℝ) : ℂ) ^ (s - 1 / 2 - cP - (μ₁ + μ₂)) *
          ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ μ₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t * p / q) / r : ℝ) : ℂ) ^ μ₂ * (Real.exp (-(Real.pi * ((t * p / q) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
          ((p : ℝ) : ℂ) ^ (u₀ - (μ₁ + μ₂) - 1) * ((q : ℝ) : ℂ) ^ (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) *
          (Real.exp (-(Real.pi / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) *
          (Real.exp (-(Real.pi / q ^ 2)) : ℂ)) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hswap] with t ht hk
    exact hk ht
  rw [step4]

  have ha12 : a₁ + (c + 1) = a₂ + c := (by decide : ∀ x y z : ZMod 2, x ≠ y → x + (z + 1) = y + z) a₁ a₂ c h12
  have ha21 : a₂ + (c + 1) = a₁ + c := (by decide : ∀ x y z : ZMod 2, x ≠ y → y + (z + 1) = x + z) a₁ a₂ c h12
  have hss : signShift (a₁ + (c + 1)) + signShift (a₂ + (c + 1)) = 1 := by
    rw [ha12, ha21]
    have h4 := (by decide : ∀ x y z : ZMod 2, x ≠ y → ((x + z = 0 ∧ ¬ y + z = 0) ∨ (¬ x + z = 0 ∧ y + z = 0))) a₁ a₂ c h12
    unfold signShift
    rcases h4 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  have hs1 := hsre (a₁ + (c + 1))
  have hs2 := hsre (a₂ + (c + 1))
  have habs : ∀ x : ℝ, -|x| ≤ x ∧ x ≤ |x| := fun x => ⟨neg_abs_le x, le_abs_self x⟩
  obtain ⟨hu1, hu2⟩ := habs u₀.re
  obtain ⟨hn11, hn12⟩ := habs ν₁.re
  obtain ⟨hn21, hn22⟩ := habs ν₂.re
  obtain ⟨hm11, hm12⟩ := habs μ₁.re
  obtain ⟨hm21, hm22⟩ := habs μ₂.re
  obtain ⟨hc1, hc2⟩ := habs cP.re
  have hR' : |u₀.re| + |ν₁.re| + |ν₂.re| + |μ₁.re| + |μ₂.re| + |cP.re| + 4 < s.re := by rw [hR] at hsR; exact hsR
  have hbal : (u₀ - (μ₁ + μ₂) - 1) - (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) =
      2 * (s - 1 / 2 - cP - (μ₁ + μ₂)) + 2 + (ν₁ + signShift (a₁ + (c + 1))) + (ν₂ + signShift (a₂ + (c + 1))) := by
    rw [hcP]; linear_combination (-1 : ℂ) * hss
  have hK8 := LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
    (ν₁ + signShift (a₁ + (c + 1))) (ν₂ + signShift (a₂ + (c + 1))) μ₁ μ₂ (s - 1 / 2 - cP - (μ₁ + μ₂))
    (u₀ - (μ₁ + μ₂) - 1) (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) hbal
    (by rcases hs1 with h | h <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, h]; linarith))
    (by rcases hs2 with h | h <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, h]; linarith))
    (by rcases hs1 with h | h <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, h]; linarith))
    (by rcases hs1 with h | h <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, h]; linarith))
    (by rcases hs2 with h | h <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, h]; linarith))
    (by rcases hs2 with h | h <;> (simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, h]; linarith))
  rw [hK8]
  have hwre : 0 < (2 * s - cP - P₂.centralExponent + 1 + 1).re := by
    rw [hce]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, zero_mul, sub_zero]
    linarith
  have hΓne : Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + 1 + 1) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hwre
  have e0 : Complex.Gammaℝ ((u₀ - (μ₁ + μ₂) - 1) - (u₀ + cP + (μ₁ + μ₂) - 2 * s - 3) + μ₁ + μ₂) =
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + 1 + 1) := by rw [hce]; congr 1; ring
  have e1 : Complex.Gammaℝ ((s - 1 / 2 - cP - (μ₁ + μ₂)) - (u₀ - (μ₁ + μ₂) - 1) + (ν₁ + signShift (a₁ + (c + 1)))) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (a₂ + c))) := by rw [ha12, hcP]; congr 1; ring
  have e2 : Complex.Gammaℝ ((s - 1 / 2 - cP - (μ₁ + μ₂)) - (u₀ - (μ₁ + μ₂) - 1) + (ν₂ + signShift (a₂ + (c + 1)))) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (a₁ + c))) := by rw [ha21, hcP]; congr 1; ring
  have e3 : Complex.Gammaℝ ((s - 1 / 2 - cP - (μ₁ + μ₂)) + 1 + (ν₁ + signShift (a₁ + (c + 1))) + μ₁) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₂) + signShift (a₂ + c))) := by rw [ha12, hcP]; congr 1; ring
  have e4 : Complex.Gammaℝ ((s - 1 / 2 - cP - (μ₁ + μ₂)) + 1 + (ν₁ + signShift (a₁ + (c + 1))) + μ₂) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₁) + signShift (a₂ + c))) := by rw [ha12, hcP]; congr 1; ring
  have e5 : Complex.Gammaℝ ((s - 1 / 2 - cP - (μ₁ + μ₂)) + 1 + (ν₂ + signShift (a₂ + (c + 1))) + μ₁) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₂) + signShift (a₁ + c))) := by rw [ha21, hcP]; congr 1; ring
  have e6 : Complex.Gammaℝ ((s - 1 / 2 - cP - (μ₁ + μ₂)) + 1 + (ν₂ + signShift (a₂ + (c + 1))) + μ₂) =
      Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₁) + signShift (a₁ + c))) := by rw [ha21, hcP]; congr 1; ring
  rw [e0, e1, e2, e3, e4, e5, e6]
  revert hΓne
  generalize Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + 1 + 1) = G
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (a₁ + c))) = A₁
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (a₂ + c))) = A₂
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₁) + signShift (a₁ + c))) = B₁
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₁) + signShift (a₂ + c))) = B₂
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -μ₂) + signShift (a₁ + c))) = B₃
  generalize Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -μ₂) + signShift (a₂ + c))) = B₄
  generalize ((-1 : ℂ) ^ c.val) = ε
  intro hΓne
  have hfin : ∀ Y : ℂ, G * (2 * ε * ρ * (1 / 2 * Y / G)) = ε * ρ * Y := by
    intro Y
    rw [show G * (2 * ε * ρ * (1 / 2 * Y / G)) = ε * ρ * Y * (G / G) by ring, div_self hΓne, mul_one]
  rw [hfin]
  ring

end S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_blockHarmonic_eq_mul_prod_GammaR
end P2MW
export P2MW.S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_blockHarmonic_eq_mul_prod_GammaR (solution)
