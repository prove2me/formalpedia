-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ab28f759-3845-51d7-9c8b-35391281fbbf

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
import Theorems.Thm_LanglandsTunnell_integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections
import Theorems.Thm_MeasureTheory_setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
import Theorems.Thm_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_eq_integral_postGaussian_torusTriple
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
import Theorems.Thm_LanglandsTunnell_Converse_integral_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_eq_mul_prod_GammaR_of_weightZeroProfile
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_detPow_blockQuadratic_colHarmonic_gaussian3
import Theorems.Thm_LanglandsTunnell_add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor
import Theorems.Thm_LanglandsTunnell_CubicInduction_archDatumR_W_diagOne_neg_eq_of_weightZero
import Theorems.Thm_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_archOfParamR_principal_three_real
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.Algebra.GroupWithZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile
p2m_attr_erase "simp" "AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory

namespace Ws14P0kit

open LanglandsTunnell.Converse.ArchR Set

noncomputable def gM (x y₁ y₂ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
     y₂ * Real.sin θ, y₂ * Real.cos θ]

noncomputable def rotM (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem det_rotM (θ : ℝ) : (rotM θ).det = 1 := by
  rw [rotM, Matrix.det_fin_two_of]; have := Real.sin_sq_add_cos_sq θ; nlinarith [this]

noncomputable def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM θ) (by rw [det_rotM]; exact one_ne_zero)

theorem rotGL_coe (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM θ := rfl

theorem rotGL_mem (θ : ℝ) : rotGL θ ∈ rowIsometrySubgroup₀ ℝ := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [rotGL_coe, det_rotM], ?_, ?_⟩
  · rw [rotGL_coe, det_rotM, norm_one]
  · intro x y
    simp only [rotGL_coe, rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * h

theorem diagOne_mul_gM (c x y₁ y₂ θ : ℝ) (hy₂ : y₂ ≠ 0) :
    ArchR.diagOne c * gM x y₁ y₂ θ = unip (c * x) * (y₂ • (ArchR.diagOne (c * y₁ / y₂) * rotM θ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ArchR.diagOne, gM, unip, rotM, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem W_diagOne_mul_gM {P : RealArchParam} (D : ArchDatumR P)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    {c : ℝ} (hc : c ≠ 0) (x : ℝ) {y₁ y₂ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) (θ : ℝ) :
    D.W (ArchR.diagOne c * gM x y₁ y₂ θ) = psi (c * x) * (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (c * y₁ / y₂)) := by
  have hτ : c * y₁ / y₂ ≠ 0 := div_ne_zero (mul_ne_zero hc hy₁) hy₂.ne'
  set X : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (ArchR.diagOne (c * y₁ / y₂))
    (by rw [ArchR.diagOne, Matrix.det_fin_two_of]; simpa using hτ) with hX
  have hXc : ((X : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ArchR.diagOne (c * y₁ / y₂) := rfl
  have hK : D.W (ArchR.diagOne (c * y₁ / y₂) * rotM θ) = D.W (ArchR.diagOne (c * y₁ / y₂)) := by
    have h := hDW0 ⟨rotGL θ, rotGL_mem θ⟩ X
    rw [Units.val_mul, hXc] at h
    exact h
  rw [diagOne_mul_gM c x y₁ y₂ θ hy₂.ne', D.unip_law, D.central_law y₂ _ hy₂.ne', hK]
  ring

theorem Gc_def : (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) = fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := rfl

theorem deriv_Gc (η : ℝ) :
    deriv (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) η = -(2 * Real.pi * η) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := by
  have h1 : HasDerivAt (fun y : ℝ => -(Real.pi * y ^ 2)) (-(Real.pi * (2 * η))) η := by
    have h := ((hasDerivAt_pow 2 η).const_mul Real.pi).fun_neg
    simp [pow_one] at h
    exact h
  have h3 : HasDerivAt (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ))
      (((Real.exp (-(Real.pi * η ^ 2)) * -(Real.pi * (2 * η)) : ℝ) : ℂ)) η :=
    ((Real.hasDerivAt_exp _).comp η h1).ofReal_comp
  rw [h3.deriv]
  push_cast
  ring

theorem moment_zero (ξ : ℝ) :
    ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
  have h := LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv 0 ξ
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
  exact h

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

theorem x_moment (c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (c * x) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * (1 - ((c * y₁ ^ 2 : ℝ) : ℂ)) := by
  have hy : 0 < |y₁| := abs_pos.2 hy₁
  set ξ : ℝ := c * |y₁| with hξ
  set f : ℝ → ℂ := fun x => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (c * x) with hf

  have hpt : ∀ u : ℝ, f (|y₁| * u) =
      (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) +
        (Complex.I * ((|y₁| : ℝ) : ℂ)) *
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
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (1 - ((|y₁| : ℝ) : ℂ) * (ξ : ℂ)) := by
    simp_rw [hpt]
    rw [integral_add hint1 (hint2.const_mul _), integral_const_mul, moment_zero, moment_one]
    linear_combination (((|y₁| : ℝ) : ℂ) * (ξ : ℂ) * (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ)) * Complex.I_sq
  have hsub := Measure.integral_comp_mul_left f |y₁|
  rw [abs_inv, abs_abs, hscaled, Complex.real_smul] at hsub

  have hne : (((|y₁| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have key : ∫ x, f x = ((|y₁| : ℝ) : ℂ) * ((Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (1 - ((|y₁| : ℝ) : ℂ) * (ξ : ℂ))) := by
    rw [hsub]
    push_cast
    field_simp
  rw [show (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (c * x)) = ∫ x, f x from rfl,
    key, hξ]
  have habs : (|y₁| : ℝ) * (c * |y₁|) = c * y₁ ^ 2 := by rw [← sq_abs y₁]; ring
  have hξ2 : (c * |y₁|) ^ 2 = c ^ 2 * y₁ ^ 2 := by rw [mul_pow, sq_abs]
  rw [hξ2]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  have habs' : ((|y₁| : ℝ) : ℂ) * ((c : ℂ) * ((|y₁| : ℝ) : ℂ)) = (c : ℂ) * (y₁ : ℂ) ^ 2 := by exact_mod_cast habs
  linear_combination ((Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * (-( ((|y₁| : ℝ) : ℂ)))) * habs'

theorem W_diagOne_mul_gM_weight {P : RealArchParam} (D : ArchDatumR P) (k : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    {c : ℝ} (hc : c ≠ 0) (x : ℝ) {y₁ y₂ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) (θ : ℝ) :
    D.W (ArchR.diagOne c * gM x y₁ y₂ θ) =
      psi (c * x) * (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) *
        ((archWeightCharℝ k ⟨rotGL θ, rotGL_mem θ⟩ : ℂ) * D.W (ArchR.diagOne (c * y₁ / y₂))) := by
  have hτ : c * y₁ / y₂ ≠ 0 := div_ne_zero (mul_ne_zero hc hy₁) hy₂.ne'
  set X : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (ArchR.diagOne (c * y₁ / y₂))
    (by rw [ArchR.diagOne, Matrix.det_fin_two_of]; simpa using hτ) with hX
  have hXc : ((X : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ArchR.diagOne (c * y₁ / y₂) := rfl
  have hK : D.W (ArchR.diagOne (c * y₁ / y₂) * rotM θ) =
      (archWeightCharℝ k ⟨rotGL θ, rotGL_mem θ⟩ : ℂ) * D.W (ArchR.diagOne (c * y₁ / y₂)) := by
    have h := hDW ⟨rotGL θ, rotGL_mem θ⟩ X
    rw [Units.val_mul, hXc] at h
    exact h
  rw [diagOne_mul_gM c x y₁ y₂ θ hy₂.ne', D.unip_law, D.central_law y₂ _ hy₂.ne', hK]
  ring

theorem x_moment0 (c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * psi (c * x) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) := by
  have hy : 0 < |y₁| := abs_pos.2 hy₁
  set ξ : ℝ := c * |y₁| with hξ
  set f : ℝ → ℂ := fun x => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * psi (c * x) with hf
  have hpt : ∀ u : ℝ, f (|y₁| * u) =
      (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) := by
    intro u
    have hsq : (|y₁| * u) ^ 2 / y₁ ^ 2 = u ^ 2 := by rw [mul_pow, sq_abs]; field_simp
    have hpsi : psi (c * (|y₁| * u)) = Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) := by
      rw [psi, hξ]; congr 1; push_cast; ring
    simp only [hf, hsq, hpsi]
  have hscaled : ∫ u : ℝ, f (|y₁| * u) = (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
    simp_rw [hpt]; exact moment_zero ξ
  have hsub := Measure.integral_comp_mul_left f |y₁|
  rw [abs_inv, abs_abs, hscaled, Complex.real_smul] at hsub
  have hne : (((|y₁| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have key : ∫ x, f x = ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
    rw [hsub]; push_cast; field_simp
  rw [show (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * psi (c * x)) = ∫ x, f x from rfl, key, hξ, mul_pow, sq_abs]

end Ws14P0kit

namespace Ws14PQpw

open Ws14P0kit

theorem ae_ne_zero : ∀ᵐ t : ℝ, t ≠ 0 := by
  have h : ({(0 : ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
  exact Filter.Eventually.mono h fun t ht => by simpa using ht

theorem phase_cancel (y₂ θ : ℝ) :
    ((((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ)) ^ 2) *
      (((y₂ * Real.sin θ : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ 2 =
    (-Complex.I * (y₂ : ℂ)) ^ 2 := by
  have hcs : ((Real.cos θ : ℝ) : ℂ) ^ 2 + ((Real.sin θ : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq θ
  have h1 : (((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
      (((y₂ * Real.sin θ : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) = -Complex.I * (y₂ : ℂ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_one]
    linear_combination (-Complex.I * (y₂ : ℂ)) * hcs + ((y₂ : ℂ) * ((Real.sin θ : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ)) * Complex.I_sq
  rw [← mul_pow, h1]

theorem integrand_pointwise {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₀ cP : ℂ) (a₀ : ZMod 2) (W : ℝ → ℂ) (a : ℝ) (ha : a ≠ 0) (s : ℂ) (ε' : ℝ) (hε' : ε' = -1) (δ : ℕ)
    {x y₁ y₂ θ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    (let g : Matrix (Fin 2) (Fin 2) ℝ :=
       !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
          y₂ * Real.sin θ, y₂ * Real.cos θ]
     ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ *
         (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
       ((∫ t : ℝ, W t * D.W (ArchR.diagOne (a * t) * g) *
           (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
        (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ δ *
          ((((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ)) ^ 2 *
              ((((1 + x ^ 2) / y₁ ^ 2 - 1 / y₂ ^ 2 : ℝ) : ℂ) - Complex.I * (((2 * x / (y₁ * y₂) : ℝ) : ℂ)))) *
          (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
          ((|y₁ * y₂| : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) ^ 2 *
          (((y₂ * Real.sin θ : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ 2 *
          ((1 / 2 : ℂ) *
            ((Real.pi * a ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
            Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)))) *
       ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) =
    ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ δ *
              ((((1 + x ^ 2) / y₁ ^ 2 - 1 / y₂ ^ 2 : ℝ) : ℂ) - Complex.I * (((2 * x / (y₁ * y₂) : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) := by
  subst hε'
  have hsc : (y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2 = y₂ ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ; nlinarith [this]
  simp only [hsc]
  have hpt : ∀ᵐ t : ℝ, W t * D.W (ArchR.diagOne (a * t) * gM x y₁ y₂ θ) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) =
      (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
        (W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) := by
    refine ae_ne_zero.mono fun t ht => ?_
    rw [W_diagOne_mul_gM D hDW0 (mul_ne_zero ha ht) x hy₁ hy₂ θ]
    ring
  have hT : (∫ t : ℝ, W t * D.W (ArchR.diagOne (a * t) *
        !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
           y₂ * Real.sin θ, y₂ * Real.cos θ]) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) =
      (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
        ∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
           (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) := by
    change (∫ t : ℝ, W t * D.W (ArchR.diagOne (a * t) * gM x y₁ y₂ θ) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) = _
    rw [integral_congr_ae hpt, integral_const_mul]
  rw [hT]
  have hph := phase_cancel y₂ θ
  linear_combination (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
      ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
        (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
           (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
        (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ δ *
          ((((1 + x ^ 2) / y₁ ^ 2 - 1 / y₂ ^ 2 : ℝ) : ℂ) - Complex.I * (((2 * x / (y₁ * y₂) : ℝ) : ℂ))) *
          (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
          ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 *
          ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) * Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)))) *
      ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) * hph

end Ws14PQpw

namespace Ws23K7mt

theorem iterated_eq_prod (H : ℝ → ℝ → ℝ → ℂ)
    (hH : Integrable (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) :
    ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ t : ℝ, H t y₁ y₂ =
      ∫ q, H q.1 q.2.1 q.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by
  rw [integral_prod_symm (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) hH, integral_prod _ hH.integral_prod_right]

theorem prod_eq_fold (H : ℝ → ℝ → ℝ → ℂ)
    (hH : Integrable (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) :
    ∫ q, H q.1 q.2.1 q.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
        (H t y₁ y₂ + H (-t) y₁ y₂ + H t (-y₁) y₂ + H (-t) (-y₁) y₂) := by
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi 0) with hν
  have hmp := measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) ν
  set G : (ℝ × ℝ) × ℝ → ℂ := (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) ∘ (MeasurableEquiv.prodAssoc : (ℝ × ℝ) × ℝ ≃ᵐ ℝ × ℝ × ℝ) with hG
  have hGi : Integrable G (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) :=
    (hmp.integrable_comp_emb (MeasurableEquiv.prodAssoc).measurableEmbedding).2 hH
  have hGpt : ∀ (p : ℝ × ℝ) (y₂ : ℝ), G (p, y₂) = H p.1 p.2 y₂ := by
    intro p y₂; simp only [hG, Function.comp, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply]
  have h1 : ∫ q, H q.1 q.2.1 q.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ν)) =
      ∫ q, G q ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).prod ν) := by
    rw [← hmp.integral_comp']; rfl
  rw [h1, integral_prod G hGi]
  have hF : Integrable (fun p : ℝ × ℝ => ∫ y₂, G (p, y₂) ∂ν) ((volume : Measure ℝ).prod volume) := hGi.integral_prod_left
  rw [LanglandsTunnell.integral_prod_eq_setIntegral_Ioi_setIntegral_Ioi_sum_reflections _ hF]

  have hs : ∀ᵐ p : ℝ × ℝ ∂((volume : Measure ℝ).prod volume), Integrable (fun y₂ => G (p, y₂)) ν := hGi.prod_right_ae
  have mneg := Measure.measurePreserving_neg (volume : Measure ℝ)
  have mid := MeasurePreserving.id (volume : Measure ℝ)
  have hs₂ := (mneg.prod mid).quasiMeasurePreserving.ae hs
  have hs₃ := (mid.prod mneg).quasiMeasurePreserving.ae hs
  have hs₄ := (mneg.prod mneg).quasiMeasurePreserving.ae hs
  have hae := Measure.ae_ae_of_ae_prod (((hs.and hs₂).and hs₃).and hs₄)
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [hae] with t ht _
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [ht] with y₁ hy _
  obtain ⟨⟨⟨i₁, i₂⟩, i₃⟩, i₄⟩ := hy
  simp only [Prod.map, id] at i₂ i₃ i₄
  simp only [hGpt] at i₁ i₂ i₃ i₄ ⊢
  have i12 : Integrable (fun y₂ => H t y₁ y₂ + H (-t) y₁ y₂) ν := i₁.add i₂
  have i123 : Integrable (fun y₂ => H t y₁ y₂ + H (-t) y₁ y₂ + H t (-y₁) y₂) ν := i12.add i₃
  rw [integral_add i123 i₄, integral_add i12 i₃, integral_add i₁ i₂]

end Ws23K7mt

namespace Ws14PQsl

theorem ae_ne_zero : ∀ᵐ t : ℝ, t ≠ 0 := by
  have h : ({(0 : ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
  exact Filter.Eventually.mono h fun t ht => by simpa using ht

theorem slices {P₂ : RealArchParam} (D : ArchDatumR P₂) (W : ℝ → ℂ) (u₀ cP : ℂ) (a₀ : ZMod 2) (a : ℝ) (s : ℂ) (δ : ℕ)
    (hS1 : ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y₂ : ℝ, 0 < y₂ →
      (∫ x : ℝ, ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ δ *
              ((((1 + x ^ 2) / y₁ ^ 2 - 1 / y₂ ^ 2 : ℝ) : ℂ) - Complex.I * (((2 * x / (y₁ * y₂) : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) = ∫ t : ℝ, (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)) : ℂ))))) :
    ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ, ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ δ *
              ((((1 + x ^ 2) / y₁ ^ 2 - 1 / y₂ ^ 2 : ℝ) : ℂ) - Complex.I * (((2 * x / (y₁ * y₂) : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) =
    ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ t : ℝ, (ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)) : ℂ)))) := by
  refine integral_congr_ae ?_
  filter_upwards [ae_ne_zero] with y₁ hy₁
  refine setIntegral_congr_fun measurableSet_Ioi (fun y₂ hy₂ => ?_)
  exact hS1 y₁ hy₁ y₂ hy₂

end Ws14PQsl

namespace Ws14PQcore

theorem signShift_cc (c : ZMod 2) : signShift (c + c) = 0 := by rw [CharTwo.add_self_eq_zero, signShift_zero]

theorem core {P₂ : RealArchParam} (D : ArchDatumR P₂) (μ₁ μ₂ : ℂ) (b c : ZMod 2) (hc : c = b + 1)
    (hP₂eq : P₂ = RealArchParam.principal μ₁ c μ₂ c)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (ρ : ℂ) (hρ : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((τ) / r : ℝ) : ℂ) ^ (μ₂) * (Real.exp (-(Real.pi * ((τ) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (ν₁ ν₂ : ℂ)
    (hW0 : ∀ t : ℝ, 0 < t → W t + (-1 : ℂ) ^ b.val * W (-t) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ : ZMod 2)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) (ε' : ℝ) (hε' : ε' = -1)
    (a : ℝ) (ha : a ≠ 0) (ha1 : a = -1) :
    ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re →
      ∫ p : ℝ × ℝ × ℝ × ℝ in Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi))),
            (let x : ℝ := p.1
             let y₁ : ℝ := p.2.1
             let y₂ : ℝ := p.2.2.1
             let θ : ℝ := p.2.2.2
             let g : Matrix (Fin 2) (Fin 2) ℝ :=
       !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
          y₂ * Real.sin θ, y₂ * Real.cos θ]
     ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ *
         (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
       ((∫ t : ℝ, W t * D.W (ArchR.diagOne (a * t) * g) *
           (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
        (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ δ *
          ((((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ)) ^ 2 *
              ((((1 + x ^ 2) / y₁ ^ 2 - 1 / y₂ ^ 2 : ℝ) : ℂ) - Complex.I * (((2 * x / (y₁ * y₂) : ℝ) : ℂ)))) *
          (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
          ((|y₁ * y₂| : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) ^ 2 *
          (((y₂ * Real.sin θ : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ 2 *
          ((1 / 2 : ℂ) *
            ((Real.pi * a ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + ((2 : ℕ) : ℂ) + 1) / 2)) *
            Complex.Gamma ((cP + P₂.centralExponent + 2 * s + ((2 : ℕ) : ℂ) + 1) / 2)))) *
       ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ))
        = ((2 * Real.pi : ℝ) : ℂ) * ((-1 : ℂ) ^ b.val * ρ * ((Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + u₀) + signShift (b + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + u₀) + signShift (b + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₁) + signShift (b + c))) *
            Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₁) + signShift (b + c)))) *
            (Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + μ₂) + signShift (b + c))) *
              Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + μ₂) + signShift (b + c))))))) := by
  obtain ⟨σa, hA⟩ := LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
    ν₁ ν₂ b W hWc hW0 hWpar D a ha (u₀ + 2) cP a₀ δ hδ
  obtain ⟨σb, hB⟩ := LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_detPow_blockQuadratic_colHarmonicTwo_eq_integral_postGaussian_torusTriple
    ν₁ ν₂ b W hWc hW0 hWpar D a ha (u₀ + 2) cP a₀ δ hδ
  obtain ⟨σc, hC⟩ := LanglandsTunnell.Converse.exists_forall_integrable_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_of_mulConvGaussian_sheet
    ν₁ ν₂ b W hWc hW0 hWpar D a ha (u₀ + 2) cP a₀ δ hδ
  obtain ⟨σd, hD⟩ := LanglandsTunnell.Converse.integral_postGaussian_torusTriple_detPow_blockQuadratic_colHarmonicTwo_eq_mul_prod_GammaR_of_weightZeroProfile
    ν₁ ν₂ b c hc W hWc hW0 hWpar μ₁ μ₂ D hP₂eq ρ hρ hDpar a ha1 u₀ cP hcP a₀ δ hδ hδpar
  refine ⟨max (max σa σb) (max σc σd), fun s hs => ?_⟩
  have hsa : σa < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hsb : σb < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hsc : σc < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hsd : σd < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  simp only [Nat.cast_ofNat]

  rw [MeasureTheory.setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free _ (fun x y₁ y₂ => ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ δ *
              ((((1 + x ^ 2) / y₁ ^ 2 - 1 / y₂ ^ 2 : ℝ) : ℂ) - Complex.I * (((2 * x / (y₁ * y₂) : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) ?hFG (hA s hsa)]
  case hFG =>
    intro x y₁ y₂ θ hy₁ hy₂
    exact Ws14PQpw.integrand_pointwise D hDW0 (u₀ + 2) cP a₀ W a ha s ε' hε' δ hy₁ hy₂

  rw [Ws14PQsl.slices D W (u₀ + 2) cP a₀ a s δ (hB s hsb)]

  rw [Ws23K7mt.iterated_eq_prod (fun t y₁ y₂ => (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          ((((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ δ * ((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ 2 * (-Complex.I * (y₂ : ℂ)) ^ 2 *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + 2 + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ ^ 2 - 1 / y₂ ^ 2 - a ^ 2 * t ^ 2 * y₁ ^ 2 + 1 / (2 * Real.pi) + 2 * a * t * y₁ / y₂ : ℝ)) : ℂ))))) (hC s hsc)]
  rw [hD s hsd]

end Ws14PQcore

namespace Ws23K7kit2

theorem continuous_diagOneGL :
    Continuous (fun u : ℝˣ => (NumberField.AdelicLevel.diagOne u : GL (Fin 2) ℝ)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ fun u : ℝˣ => (NumberField.AdelicLevel.diagOne u : GL (Fin 2) ℝ)) =
        fun u : ℝˣ => Matrix.diagonal ![((u : ℝˣ) : ℝ), 1] := rfl
    rw [this]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · simpa using Units.continuous_val
    · simpa using continuous_const
  · have : (fun u : ℝˣ => (((NumberField.AdelicLevel.diagOne u : GL (Fin 2) ℝ)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) =
        (fun u : ℝˣ => Matrix.diagonal ![((u⁻¹ : ℝˣ) : ℝ), 1]) := rfl
    rw [this]
    refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fin_cases i
    · simpa using (Units.continuous_coe_inv : Continuous (fun u : ℝˣ => ((u⁻¹ : ℝˣ) : ℝ)))
    · simpa using continuous_const

theorem continuousOn_Wr (WA : GL (Fin 2) ℝ → ℂ) (hWAc : Continuous WA) (Wr : ℝ → ℂ)
    (hWAt : ∀ t : ℝˣ, WA (NumberField.AdelicLevel.diagOne t) = Wr (t : ℝ)) :
    ContinuousOn Wr {t : ℝ | t ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  set φ : {t : ℝ // t ∈ {t : ℝ | t ≠ 0}} → ℝˣ := fun x => Units.mk0 x.1 x.2 with hφ
  have hφc : Continuous φ := by
    rw [Units.isEmbedding_val₀.isInducing.continuous_iff]
    exact continuous_subtype_val
  have heq : ({t : ℝ | t ≠ 0}).domRestrict Wr = fun x => WA (NumberField.AdelicLevel.diagOne (φ x)) := by
    funext x
    rw [hWAt]
    rfl
  rw [heq]
  exact hWAc.comp (continuous_diagOneGL.comp hφc)

theorem archWeightCharℝ_zero (r : rowIsometrySubgroup₀ ℝ) : ((archWeightCharℝ 0 r : ℂˣ) : ℂ) = 1 := by
  show ((((archWeightOneℝ r) ^ (0 : ℤ)) : ℂˣ) : ℂ) = 1
  rw [zpow_zero, Units.val_one]

theorem zmod2_eq_add_one_of_ne {a c : ZMod 2} (h : a ≠ c) : a = c + 1 := by
  revert a c; decide

theorem zmod2_ne_add (c : ZMod 2) : c + 1 ≠ c := by
  revert c; decide

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := CharTwo.add_self_eq_zero c

theorem zmod2_or_of_ne {e₁ e₂ : ZMod 2} (h : e₁ ≠ e₂) (c : ZMod 2) : e₁ = c ∨ e₂ = c := by
  revert e₁ e₂ c; decide

theorem zmod2_any_of_ne {x y : ZMod 2} (h : x ≠ y) (b : ZMod 2) : b = x ∨ b = y := by
  revert x y b; decide

theorem zmod2_sum_one_of_ne {e₁ e₂ : ZMod 2} (h : e₁ ≠ e₂) : e₁ + e₂ = 1 := by
  revert e₁ e₂; decide

theorem zmod2_any (b p : ZMod 2) : b = p ∨ b = p + 1 := by
  revert b p; decide

theorem zmod2_eq_add_one_of_ne' {a c : ZMod 2} (h : a ≠ c) : c = a + 1 := by
  revert a c; decide

theorem archFactor_principal_swap (u₁ u₂ : ℂ) (a₁ a₂ b : ZMod 2) (s : ℂ) :
    ((RealArchParam.principal u₂ a₂ u₁ a₁).twist 0 b).archFactor s =
      ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s := by
  simp only [RealArchParam.twist, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC]
  rw [Multiset.pair_comm]

end Ws23K7kit2

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (_hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hμ : IsAdmissibleTwist K μ)
    (_hns : ¬ (∃ η : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ η ∧
      ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
        IsUnramifiedCharAt η (𝔓.under (𝓞 ℚ)) →
        ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) =
          ((η (uniformizerIdele ℚ (𝔓.under (𝓞 ℚ))) : ℂˣ) : ℂ) ^
            (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal))
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : IsAdmissibleTwist ℚ ω ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), ¬ IsBadPlace K μ p →
        IsUnramifiedCharAt ω p ∧ eulerCoeff ℚ ω p = inducedE3 ℚ (inducedCoeff K μ) p) ∧
      ∀ (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
        (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ),
        (∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ)) →
        (∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw)) →
        ∀ v : InfinitePlace ℚ, v.IsReal →
          IsArchCompAt ℚ ω v
            ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
            ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (ha : a ≠ 0) (ha1 : a = -1) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (P : RealArchParam)
    (_hP₁ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (kw : ZMod 2 → InfinitePlace ℚ → ℤ)
    (Wr : ZMod 2 → InfinitePlace ℚ → ℂ → ℂ)
    (WA : ZMod 2 → GL (Fin 2) ℝ → ℂ)
    (hkw1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₂ →
          (kw par w : ℂ) = signShift (a₁ + par) + signShift (a₂ + par))
    (hkw2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → kw par w = (n : ℤ) + 1)
    (hWr1 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ →
          ∀ t : ℝ, Wr par w (-t) = (-1 : ℂ) ^ a₁.val * Wr par w t)
    (hWr2 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
        P = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr par w t = 0)
    (hWr3 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
        P = RealArchParam.principal u₁ a₁ u₂ a₁ → par = a₁ + 1 →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ a₁.val * Wr par w (-t)) / (t : ℂ)) s
                = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ)) * (P.twist 0 a₁).archFactor s)
    (hWr4 : ∀ par : ZMod 2, ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
        (b = par ∨ b = par + P.centralSign) →
          ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
            MellinConvergent (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s ∧
              mellin (fun t : ℝ => (Wr par w t + (-1 : ℂ) ^ b.val * Wr par w (-t)) / (t : ℂ)) s
                = (P.twist 0 b).archFactor s)
    (hWAN : ∀ par : ZMod 2, ∀ (x : ℝ) (h : GL (Fin 2) ℝ),
        WA par (unipotentGL2 x * h) = Complex.exp (-(2 * Real.pi * Complex.I * (a : ℂ) * x)) * WA par h)
    (hWAZ : ∀ par : ZMod 2, ∀ (z : ℝˣ) (h : GL (Fin 2) ℝ),
        WA par (Matrix.GeneralLinearGroup.scalar (Fin 2) z * h)
          = ((((|(z : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              (((z : ℝ) : ℂ) / ((|(z : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) * WA par h)
    (hWAK : ∀ par : ZMod 2, ∀ (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (h : GL (Fin 2) ℝ),
        WA par (h * κ) = (archWeightCharℝ (kw par default) ⟨κ, hκ⟩ : ℂ) * WA par h)
    (hWAt : ∀ par : ZMod 2, ∀ t : ℝˣ, WA par (diagOne t) = Wr par default (t : ℝ))
    (hWAc : ∀ par : ZMod 2, Continuous (WA par))
    (w₀R : GL (Fin 2) ℝ) (hw₀R : (w₀R : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 1; 1, 0])
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : LanglandsTunnell.Converse.ArchCasimir.IsCasimirEigen D)
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0)
    (hk₀min : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂)) ∧
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P₂ = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1))
    (ν₁ ν₂ : ℂ) (b : ZMod 2) (hPev : P = RealArchParam.principal ν₁ b ν₂ b)
    (hk₀ : k₀ = 0)
    (hLevi : ∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ → a₁ = b + 1)
    (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = aR w₀ h₀ + b)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) ^ 2 + (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ)) ^ 2) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 2) * gaussian3 M)

    (u₁ u₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c u₂ c)
    (ρ : ℂ)
    (hρ : ∀ τ : ℝ, 0 < τ →
      D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((τ) / r : ℝ) : ℂ) ^ (u₂) * (Real.exp (-(Real.pi * ((τ) / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    ∃ σa : ℝ, ∀ s : ℂ, σa < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr b default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = ((((2 * Real.pi : ℝ) : ℂ) * (-1 : ℂ) ^ b.val) * ρ) * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by

  have hS' : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) ^ 2 + (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ)) ^ 2) *
        ((((M 0 2 : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 2) * gaussian3 M := by
    rw [hS]; funext M; congr 2; push_cast; ring
  obtain ⟨σ₁, h05⟩ := LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_detPow_blockQuadratic_colHarmonic_gaussian3
    K _hdeg μ _hμ _hns uR aR uC kC huR huC ω hω E hE a ha ha1 aInf haInf psiInf hpsiInf ν_add hν_add ν_mul P _hP₁ kw Wr WA hkw1 hkw2 hWr1 hWr2 hWr3 hWr4 hWAN hWAZ hWAK hWAt hWAc w₀R hw₀R w₀ h₀ P₂ hP₂ D k₀ hDW hDE hDnz hk₀min b 2 δ hδ (-1) (Or.inr rfl) S hS'

  subst hk₀
  have hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro r x
    rw [hDW r x, show ((archWeightCharℝ 0 r : ℂˣ) : ℂ) = 1 from by
      show ((((archWeightOneℝ r) ^ (0 : ℤ)) : ℂˣ) : ℂ) = 1; rw [zpow_zero, Units.val_one], one_mul]

  have hPc : P.centralExponent = ν₁ + ν₂ := by rw [hPev]; rfl
  have hc : c = b + 1 := hLevi u₁ u₂ c c hP₂eq
  have ha' : ((a : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ha
  have ha1' : ((a : ℚ) : ℝ) = -1 := by rw [ha1]; push_cast; ring

  obtain ⟨w₁, w₂, h₁, h₂, h01, h02, h12, hall, hP₂'⟩ : ∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
      w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
      P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂) := by
    rcases hP₂ with h | ⟨wC, hC, -, hbr⟩
    · exact h
    · exfalso
      rcases hbr with ⟨hk, hd⟩ | ⟨-, hpr⟩
      · rw [hP₂eq] at hd; cases hd
      · rw [hP₂eq] at hpr
        injection hpr with h1 h2 h3 h4
        exact absurd (h2.symm.trans h4) (by decide)
  have hinj : u₁ = uR w₁ h₁ ∧ c = aR w₁ h₁ ∧ u₂ = uR w₂ h₂ ∧ c = aR w₂ h₂ := by
    rw [hP₂eq] at hP₂'
    injection hP₂' with h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩

  have hreal : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _
  have hWc : ContinuousOn (fun t : ℝ => Wr b default t) {t : ℝ | t ≠ 0} :=
    Ws23K7kit2.continuousOn_Wr (WA b) (hWAc b) (fun t : ℝ => Wr b default t) (hWAt b)
  have hMel : ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      MellinConvergent (fun t : ℝ => (Wr b default t + (-1 : ℂ) ^ b.val * Wr b default ((-t : ℝ) : ℂ)) / (t : ℂ)) s ∧
        mellin (fun t : ℝ => (Wr b default t + (-1 : ℂ) ^ b.val * Wr b default ((-t : ℝ) : ℂ)) / (t : ℂ)) s
          = ((RealArchParam.principal ν₁ b ν₂ b).twist 0 b).archFactor s := by
    obtain ⟨s₀, hs₀⟩ := hWr4 b default hreal b (Or.inl rfl)
    refine ⟨s₀, fun s hs => ?_⟩
    rw [← hPev]
    simp only [Complex.ofReal_neg]
    exact hs₀ s hs
  have hW0 : ∀ t : ℝ, 0 < t → Wr b default t + (-1 : ℂ) ^ b.val * Wr b default ((-t : ℝ) : ℂ) = (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)) := by
    intro t ht
    have h := LanglandsTunnell.add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor
      ν₁ ν₂ b b (fun t : ℝ => Wr b default t) hWc b hMel t ht
    simp only [Ws14PQcore.signShift_cc, add_zero] at h
    exact h
  have hWpar : ∀ t : ℝ, Wr b default ((-t : ℝ) : ℂ) = (-1 : ℂ) ^ b.val * Wr b default t := by
    intro t; rw [Complex.ofReal_neg]; exact hWr1 b default hreal ν₁ ν₂ b hPev rfl t

  have hDpar : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ) := fun τ hτ =>
    LanglandsTunnell.CubicInduction.archDatumR_W_diagOne_neg_eq_of_weightZero K _hdeg μ _hμ uR aR uC kC huR huC ω
      (hω.2.2 uR aR uC kC huR huC) E hE a aInf haInf psiInf hpsiInf ν_add hν_add ν_mul ha w₀ h₀ P₂ hP₂ D 0 hDW hDE hDnz
      hk₀min rfl u₁ u₂ c c hP₂eq τ hτ.ne'

  have hRA9 := LanglandsTunnell.Converse.prod_map_GammaR_twistedGammaR_archOfParamR_principal_three_real
    K w₀ w₁ w₂ h₀ h₁ h₂ h01 h02 h12 hall uR aR uC kC P ν₁ ν₂ b b hPev

  obtain ⟨σ₂, hcore⟩ := Ws14PQcore.core D u₁ u₂ b c hc hP₂eq hDW0 ρ hρ hDpar (fun t : ℝ => Wr b default t) hWc ν₁ ν₂ hW0 hWpar
    (uR w₀ h₀) P.centralExponent hPc (aR w₀ h₀) δ hδ (by rw [hδpar, add_comm]) (-1) rfl ((a : ℚ) : ℝ) ha' ha1'
  refine ⟨max σ₁ σ₂, fun s hs => ?_⟩
  obtain ⟨hR, hC⟩ := hRA9 s
  have h := hcore s (lt_of_le_of_lt (le_max_right _ _) hs)
  rw [Complex.ofReal_ratCast] at h
  rw [h05 s (lt_of_le_of_lt (le_max_left _ _) hs), hR, hC, mul_one, h, ← hinj.1, ← hinj.2.1, ← hinj.2.2.1, ← hinj.2.2.2]
  ring

#print axioms solution
end

end S_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_evenPrincipal_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_profile (solution)
