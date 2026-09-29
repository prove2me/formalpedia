-- Prove2me | solution 1 for LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_conjBlock_eq_integral_postGaussian_torusTriple
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/dbed5832-b844-533d-a943-84a12851559a

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Theorems.Thm_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_conjBlock_eq_integral_postGaussian_torusTriple

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws14K7flatX

open LanglandsTunnell.Converse.ArchR

theorem moment_zero (ξ : ℝ) :
    ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
  have h := LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv 0 ξ
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
  exact h

theorem deriv_Gc (η : ℝ) :
    deriv (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) η = -(2 * Real.pi * η) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := by
  have h1 : HasDerivAt (fun y : ℝ => -(Real.pi * y ^ 2)) (-(Real.pi * (2 * η))) η := by
    have h__af := ((hasDerivAt_pow 2 η).const_mul Real.pi).fun_neg
    simp [pow_one] at h__af
    exact h__af
  have h3 : HasDerivAt (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ))
      (((Real.exp (-(Real.pi * η ^ 2)) * -(Real.pi * (2 * η)) : ℝ) : ℂ)) η :=
    ((Real.hasDerivAt_exp _).comp η h1).ofReal_comp
  rw [h3.deriv]
  push_cast
  ring

theorem moment_one (ξ : ℝ) :
    ∫ u : ℝ, ((u : ℝ) : ℂ) * (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) =
      Complex.I * (ξ : ℂ) * (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
  have h := LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv 1 ξ
  simp only [pow_one, iteratedDeriv_one] at h
  rw [h, deriv_Gc]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem integrable_pow_mul_G_mul (k : ℕ) (ξ : ℝ) :
    Integrable (fun u : ℝ => ((u : ℂ) ^ k * (Real.exp (-(Real.pi * u ^ 2)) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))) := by
  have h0 := (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := k)
    (by have := k.cast_nonneg (α := ℝ); linarith)).ofReal (𝕜 := ℂ)
  have h : Integrable (fun x : ℝ => (((x ^ (k : ℝ) * Real.exp (-Real.pi * x ^ 2) : ℝ)) : ℂ)) := h0
  have h' : Integrable (fun u : ℝ => (u : ℂ) ^ k * (Real.exp (-(Real.pi * u ^ 2)) : ℂ)) := by
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow, neg_mul]
  refine h'.mul_bdd (c := 1) (by fun_prop : Continuous fun u : ℝ => Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ) * (u : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

theorem x_moment_AB (A B : ℂ) (c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (A + B * Complex.I * (x : ℂ)) * psi (c * x) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * (A - B * ((c * y₁ ^ 2 : ℝ) : ℂ)) := by
  have hy : 0 < |y₁| := abs_pos.2 hy₁
  set ξ : ℝ := c * |y₁| with hξ
  set f : ℝ → ℂ := fun x => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (A + B * Complex.I * (x : ℂ)) * psi (c * x) with hf
  have hpt : ∀ u : ℝ, f (|y₁| * u) =
      A * ((Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))) +
        (B * Complex.I * ((|y₁| : ℝ) : ℂ)) *
          (((u : ℝ) : ℂ) * (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))) := by
    intro u
    have hsq : (|y₁| * u) ^ 2 / y₁ ^ 2 = u ^ 2 := by rw [mul_pow, sq_abs]; field_simp
    have hpsi : psi (c * (|y₁| * u)) = Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) := by
      rw [psi, hξ]; congr 1; push_cast; ring
    simp only [hf, hsq, hpsi]
    push_cast
    ring
  have hint1 := integrable_pow_mul_G_mul 0 ξ
  have hint2 := integrable_pow_mul_G_mul 1 ξ
  simp only [pow_zero, one_mul] at hint1
  simp only [pow_one] at hint2
  have hscaled : ∫ u : ℝ, f (|y₁| * u) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (A - B * ((|y₁| : ℝ) : ℂ) * (ξ : ℂ)) := by
    simp_rw [hpt]
    rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul, integral_const_mul, moment_zero, moment_one]
    linear_combination (B * ((|y₁| : ℝ) : ℂ) * (ξ : ℂ) * (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ)) * Complex.I_sq
  have hsub := Measure.integral_comp_mul_left f |y₁|
  rw [abs_inv, abs_abs, hscaled, Complex.real_smul] at hsub
  have hne : (((|y₁| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have key : ∫ x, f x = ((|y₁| : ℝ) : ℂ) * ((Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (A - B * ((|y₁| : ℝ) : ℂ) * (ξ : ℂ))) := by
    rw [hsub]
    push_cast
    field_simp
  rw [show (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (A + B * Complex.I * (x : ℂ)) * psi (c * x)) = ∫ x, f x from rfl,
    key, hξ]
  have hξ2 : (c * |y₁|) ^ 2 = c ^ 2 * y₁ ^ 2 := by rw [mul_pow, sq_abs]
  rw [hξ2]
  have habs : (|y₁| : ℝ) * (c * |y₁|) = c * y₁ ^ 2 := by rw [← sq_abs y₁]; ring
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  have habs' : ((|y₁| : ℝ) : ℂ) * ((c : ℂ) * ((|y₁| : ℝ) : ℂ)) = (c : ℂ) * (y₁ : ℂ) ^ 2 := by exact_mod_cast habs
  linear_combination ((Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * (-(B * ((|y₁| : ℝ) : ℂ)))) * habs'

theorem x_step_flat (Wt f : ℝ → ℂ) (A B : ℂ) (a : ℝ) (s : ℂ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) (y₂ : ℝ)
    (hInt : Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) * (A + B * Complex.I * (q.1 : ℂ)) * psi (a * q.2 * q.1)) *
          (Wt q.2 * f (a * q.2 * y₁ / y₂) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ))) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * (A + B * Complex.I * (x : ℂ)) *
        ∫ t : ℝ, Wt t * psi (a * t * x) * f (a * t * y₁ / y₂) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) =
      (Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ) *
        ∫ t : ℝ, Wt t * f (a * t * y₁ / y₂) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
          ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (A - B * (((a * t) * y₁ ^ 2 : ℝ) : ℂ))) := by
  have hsplit : ∀ x : ℝ, (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) =
      (Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) := by
    intro x
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1; congr 1
    rw [add_div]; ring
  have hin : ∀ x : ℝ, (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * (A + B * Complex.I * (x : ℂ)) *
        (∫ t : ℝ, Wt t * psi (a * t * x) * f (a * t * y₁ / y₂) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) =
      (Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
        ∫ t : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (A + B * Complex.I * (x : ℂ)) * psi (a * t * x) *
          (Wt t * f (a * t * y₁ / y₂) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) := by
    intro x
    rw [hsplit x, ← integral_const_mul, ← integral_const_mul]
    congr 1; funext t; ring
  simp_rw [hin]
  rw [integral_const_mul, integral_integral_swap hInt, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  congr 1; funext t
  have hm := x_moment_AB A B (a * t) hy₁
  have hpt : (fun x : ℝ => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (A + B * Complex.I * (x : ℂ)) * psi (a * t * x) *
        (Wt t * f (a * t * y₁ / y₂) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ))) =
      fun x : ℝ => ((Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (A + B * Complex.I * (x : ℂ)) * psi (a * t * x)) *
        (Wt t * f (a * t * y₁ / y₂) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) := rfl
  rw [hpt, integral_mul_const, hm]
  push_cast
  ring

end Ws14K7flatX

namespace Ws14K7flatS1
open LanglandsTunnell.Converse.ArchR

theorem hInt_affine {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (a : ℝ) (s : ℂ) (y₁ y₂ : ℝ) (A B : ℂ)
    (h10 : Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) * (1 + 0 * Complex.I * (q.1 : ℂ)) * ArchR.psi (a * q.2 * q.1)) *
          (W q.2 * D.W (ArchR.diagOne (a * q.2 * y₁ / y₂)) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)))
    (h01 : Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) * (0 + 1 * Complex.I * (q.1 : ℂ)) * ArchR.psi (a * q.2 * q.1)) *
          (W q.2 * D.W (ArchR.diagOne (a * q.2 * y₁ / y₂)) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ))) :
    Integrable (fun q : ℝ × ℝ =>
        ((Real.exp (-(Real.pi * (q.1 ^ 2 / y₁ ^ 2))) : ℂ) * (A + B * Complex.I * (q.1 : ℂ)) * ArchR.psi (a * q.2 * q.1)) *
          (W q.2 * (fun τ : ℝ => D.W (ArchR.diagOne τ)) (a * q.2 * y₁ / y₂) * (((|q.2| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.2 ^ 2)⁻¹ : ℝ) : ℂ)))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  refine ((h10.const_mul A).add (h01.const_mul B)).congr (ae_of_all _ fun q => ?_)
  simp only [Pi.add_apply]
  ring

theorem main
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) (n : ℕ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      (∫ x : ℝ,
        ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) =
      ∫ t : ℝ,
        (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ - 1 / y₂ - a * t * y₁ : ℝ)) : ℂ)))) := by
  obtain ⟨σ₀, h0⟩ := LanglandsTunnell.Converse.exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR
    ν₁ ν₂ a₁ a₂ W hWc hW D a ha 1 0
  obtain ⟨σ₁, h1⟩ := LanglandsTunnell.Converse.exists_forall_integrable_xAffineGaussian_psi_mul_torusPair_of_archDatumR
    ν₁ ν₂ a₁ a₂ W hWc hW D a ha 0 1
  refine ⟨max σ₀ σ₁, fun s hs y₁ hy₁ y₂ hy₂ => ?_⟩
  have hs0 : σ₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs1 : σ₁ < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  obtain ⟨A, hA⟩ : ∃ A : ℂ, A = (((1 / y₁ - 1 / y₂ : ℝ)) : ℂ) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℂ, B = (((1 / y₁ : ℝ)) : ℂ) := ⟨_, rfl⟩
  have hInt := hInt_affine D W a s y₁ y₂ A B (h0 s hs0 y₁ hy₁ y₂ hy₂) (h1 s hs1 y₁ hy₁ y₂ hy₂)
  have hx := Ws14K7flatX.x_step_flat W (fun τ : ℝ => D.W (ArchR.diagOne τ)) A B a s hy₁ y₂ hInt

  obtain ⟨Cst, hCst⟩ : ∃ Cst : ℂ, Cst = ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
      (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
      (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
        ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
          Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2))) *
      ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩

  have hblk : ∀ x : ℝ, ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) = A + B * Complex.I * (x : ℂ) := by
    intro x; rw [hA, hB]; push_cast; ring

  have hbr : ∀ t : ℝ, A - B * ((((a * t) * y₁ ^ 2 : ℝ)) : ℂ) = (((1 / y₁ - 1 / y₂ - a * t * y₁ : ℝ)) : ℂ) := by
    intro t; rw [hA, hB]; push_cast; field_simp; (try ring)

  have hL : (∫ x : ℝ,
        ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) =
      Cst * ∫ x : ℝ, (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * (A + B * Complex.I * (x : ℂ)) *
        ∫ t : ℝ, W t * psi (a * t * x) * (fun τ : ℝ => D.W (ArchR.diagOne τ)) (a * t * y₁ / y₂) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    beta_reduce
    rw [hblk x, hCst]
    ring
  have hR : (∫ t : ℝ,
        (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ - 1 / y₂ - a * t * y₁ : ℝ)) : ℂ))))) =
      Cst * ((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ) *
        ∫ t : ℝ, W t * (fun τ : ℝ => D.W (ArchR.diagOne τ)) (a * t * y₁ / y₂) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
          ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (A - B * (((a * t) * y₁ ^ 2 : ℝ) : ℂ)))) := by
    rw [mul_assoc, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    beta_reduce
    rw [← hbr t, hCst]
    ring
  rw [hL, hR, hx]

end Ws14K7flatS1

theorem solution
    (ν₁ ν₂ : ℂ) (a₁ a₂ : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (a₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (a₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (a : ℝ) (ha : a ≠ 0) (u₀ cP : ℂ) (a₀ : ZMod 2) (n : ℕ) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      (∫ x : ℝ,
        ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) =
      ∫ t : ℝ,
        (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ - 1 / y₂ - a * t * y₁ : ℝ)) : ℂ)))) := Ws14K7flatS1.main ν₁ ν₂ a₁ a₂ W hWc hW D a ha u₀ cP a₀ n

end S_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_conjBlock_eq_integral_postGaussian_torusTriple
end P2MW
export P2MW.S_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_conjBlock_eq_integral_postGaussian_torusTriple (solution)
