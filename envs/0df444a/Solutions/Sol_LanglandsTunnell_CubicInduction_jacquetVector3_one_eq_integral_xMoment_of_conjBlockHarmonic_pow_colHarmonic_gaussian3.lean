-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/d4a3e141-5e99-5021-9dae-7a44102ebf7a

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.MvPolynomial
import Theorems.Thm_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv
import Theorems.Thm_LanglandsTunnell_CubicInduction_godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3
import Theorems.Thm_LanglandsTunnell_CubicInduction_godementInner3_eq_mul_exp_of_blockPoly_mul_colHarmonic_gaussian3
import Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
p2m_attr_erase "simp" "LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq"

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell LanglandsTunnell.CubicInduction MeasureTheory

namespace Ws23PhiFlatM

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
    diagOne c * gM x y₁ y₂ θ = unip (c * x) * (y₂ • (diagOne (c * y₁ / y₂) * rotM θ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagOne, gM, unip, rotM, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem W_diagOne_mul_gM {P : RealArchParam} (D : ArchDatumR P)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    {c : ℝ} (hc : c ≠ 0) (x : ℝ) {y₁ y₂ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) (θ : ℝ) :
    D.W (diagOne c * gM x y₁ y₂ θ) = psi (c * x) * (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (diagOne (c * y₁ / y₂)) := by
  have hτ : c * y₁ / y₂ ≠ 0 := div_ne_zero (mul_ne_zero hc hy₁) hy₂.ne'
  set X : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagOne (c * y₁ / y₂))
    (by rw [diagOne, Matrix.det_fin_two_of]; simpa using hτ) with hX
  have hXc : ((X : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = diagOne (c * y₁ / y₂) := rfl
  have hK : D.W (diagOne (c * y₁ / y₂) * rotM θ) = D.W (diagOne (c * y₁ / y₂)) := by
    have h := hDW0 ⟨rotGL θ, rotGL_mem θ⟩ X
    rw [Units.val_mul, hXc] at h
    exact h
  rw [diagOne_mul_gM c x y₁ y₂ θ hy₂.ne', D.unip_law, D.central_law y₂ _ hy₂.ne', hK]
  ring

theorem archWeightCharℝ_coe (m : ℕ) {κ : GL (Fin 2) ℝ} (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) :
    ((archWeightCharℝ (m : ℤ) ⟨κ, hκ⟩ : ℂˣ) : ℂ) =
      ((((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) + Complex.I * (((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) ^ m := by
  have h1 : ((archWeightCharℝ (m : ℤ) ⟨κ, hκ⟩ : ℂˣ) : ℂ) = ((archWeightOneℝ ⟨κ, hκ⟩ : ℂˣ) : ℂ) ^ m := by
    show (((archWeightOneℝ ⟨κ, hκ⟩) ^ (m : ℤ) : ℂˣ) : ℂ) = _
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  have h2 : ((archWeightOneℝ ⟨κ, hκ⟩ : ℂˣ) : ℂ) = firstRowℂ κ := rfl
  rw [h1, h2]
  congr 1
  apply Complex.ext <;> simp [firstRowℂ]

theorem W_diagOne_mul_gM_weight {P : RealArchParam} (D : ArchDatumR P) (m : ℕ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (m : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    {c : ℝ} (hc : c ≠ 0) (x : ℝ) {y₁ y₂ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) (θ : ℝ) :
    D.W (diagOne c * gM x y₁ y₂ θ) =
      psi (c * x) * (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) *
        ((((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ)) ^ m * D.W (diagOne (c * y₁ / y₂))) := by
  have hτ : c * y₁ / y₂ ≠ 0 := div_ne_zero (mul_ne_zero hc hy₁) hy₂.ne'
  set X : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagOne (c * y₁ / y₂))
    (by rw [diagOne, Matrix.det_fin_two_of]; simpa using hτ) with hX
  have hXc : ((X : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = diagOne (c * y₁ / y₂) := rfl
  have hK : D.W (diagOne (c * y₁ / y₂) * rotM θ) =
      (((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ)) ^ m * D.W (diagOne (c * y₁ / y₂)) := by
    have h := hDW ⟨rotGL θ, rotGL_mem θ⟩ X
    rw [Units.val_mul, hXc, archWeightCharℝ_coe m (rotGL_mem θ), rotGL_coe] at h
    rw [h]
    congr 2
    simp only [rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    ring
  rw [diagOne_mul_gM c x y₁ y₂ θ hy₂.ne', D.unip_law, D.central_law y₂ _ hy₂.ne', hK]
  ring

theorem Gc_def : (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) = fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := rfl

theorem deriv_Gc (η : ℝ) :
    deriv (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) η = -(2 * Real.pi * η) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := by
  have h1 : HasDerivAt (fun y : ℝ => -(Real.pi * y ^ 2)) (-(Real.pi * (2 * η))) η := by
    simpa [pow_one] using ((hasDerivAt_pow 2 η).const_mul Real.pi).fun_neg
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

theorem x_moment_gen (c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) (α β : ℂ) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (α + β * (x : ℂ)) * psi (c * x) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * (α + Complex.I * β * ((c * y₁ ^ 2 : ℝ) : ℂ)) := by
  have hy : 0 < |y₁| := abs_pos.2 hy₁
  set ξ : ℝ := c * |y₁| with hξ
  set f : ℝ → ℂ := fun x => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (α + β * (x : ℂ)) * psi (c * x) with hf
  have hpt : ∀ u : ℝ, f (|y₁| * u) =
      α * ((Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))) +
        (β * ((|y₁| : ℝ) : ℂ)) *
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
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (α + Complex.I * β * ((|y₁| : ℝ) : ℂ) * (ξ : ℂ)) := by
    simp_rw [hpt]
    rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul, integral_const_mul, moment_zero, moment_one]
    ring
  have hsub := Measure.integral_comp_mul_left f |y₁|
  rw [abs_inv, abs_abs, hscaled, Complex.real_smul] at hsub
  have hne : (((|y₁| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have key : ∫ x, f x = ((|y₁| : ℝ) : ℂ) * ((Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (α + Complex.I * β * ((|y₁| : ℝ) : ℂ) * (ξ : ℂ))) := by
    rw [hsub]
    push_cast
    field_simp
  rw [show (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (α + β * (x : ℂ)) * psi (c * x)) = ∫ x, f x from rfl,
    key, hξ]
  have habs : (|y₁| : ℝ) * (c * |y₁|) = c * y₁ ^ 2 := by rw [← sq_abs y₁]; ring
  have hξ2 : (c * |y₁|) ^ 2 = c ^ 2 * y₁ ^ 2 := by rw [mul_pow, sq_abs]
  rw [hξ2]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  have habs' : ((|y₁| : ℝ) : ℂ) * ((c : ℂ) * ((|y₁| : ℝ) : ℂ)) = (c : ℂ) * (y₁ : ℂ) ^ 2 := by exact_mod_cast habs
  linear_combination ((Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ) * Complex.I * β) * habs'

noncomputable def eM (x y₁ y₂ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ / y₁, -(x * Real.cos θ) / y₁ + Real.sin θ / y₂;
     -(Real.sin θ) / y₁, x * Real.sin θ / y₁ + Real.cos θ / y₂]

section EKit
variable (x y₁ y₂ θ : ℝ)

theorem det_eM : (eM x y₁ y₂ θ).det = (y₁ * y₂)⁻¹ := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [eM, Matrix.det_fin_two_of]
  linear_combination (y₁ * y₂)⁻¹ * h

theorem eM_mul_gM (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) : eM x y₁ y₂ θ * gM x y₁ y₂ θ = 1 := by
  have h := Real.sin_sq_add_cos_sq θ
  have h1 : y₁ * y₁⁻¹ = 1 := mul_inv_cancel₀ hy₁
  have h2 : y₂ * y₂⁻¹ = 1 := mul_inv_cancel₀ hy₂
  rw [eM, gM]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (Real.cos θ ^ 2) * h1 + (Real.sin θ ^ 2) * h2 + h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(Real.cos θ * Real.sin θ)) * h1 + (Real.cos θ * Real.sin θ) * h2
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(Real.sin θ * Real.cos θ)) * h1 + (Real.cos θ * Real.sin θ) * h2
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (Real.sin θ ^ 2) * h1 + (Real.cos θ ^ 2) * h2 + h

theorem inv_eM (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) : (eM x y₁ y₂ θ)⁻¹ = gM x y₁ y₂ θ :=
  Matrix.inv_eq_right_inv (eM_mul_gM x y₁ y₂ θ hy₁ hy₂)

theorem sumsq_eM : ∑ i : Fin 2, ∑ j : Fin 2, eM x y₁ y₂ θ i j ^ 2 = (1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [Fin.sum_univ_two, eM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2) * h

theorem gM_one_zero : gM x y₁ y₂ θ 1 0 = y₂ * Real.sin θ := by simp [gM]
theorem gM_one_one : gM x y₁ y₂ θ 1 1 = y₂ * Real.cos θ := by simp [gM]

theorem lin_eM :
    -(((eM x y₁ y₂ θ 1 0 : ℝ) : ℂ) - Complex.I * ((eM x y₁ y₂ θ 1 1 : ℝ) : ℂ)) * ((y₂ * Real.sin θ : ℝ) : ℂ) +
      (((eM x y₁ y₂ θ 0 0 : ℝ) : ℂ) - Complex.I * ((eM x y₁ y₂ θ 0 1 : ℝ) : ℂ)) * ((y₂ * Real.cos θ : ℝ) : ℂ) =
      ((y₂ / y₁ : ℝ) : ℂ) * (1 + Complex.I * (x : ℂ)) := by
  have hc : Complex.sin (θ : ℂ) ^ 2 + Complex.cos (θ : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
  simp only [eM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  linear_combination (((y₂ : ℝ) : ℂ) / ((y₁ : ℝ) : ℂ) * (1 + Complex.I * ((x : ℝ) : ℂ))) * hc

end EKit

noncomputable def pF : MvPolynomial (Fin 2 × Fin 2) ℂ :=
  (MvPolynomial.X (0, 0) - MvPolynomial.C Complex.I * MvPolynomial.X (1, 0)) -
    MvPolynomial.C Complex.I * (MvPolynomial.X (0, 1) - MvPolynomial.C Complex.I * MvPolynomial.X (1, 1))

theorem eval_pF (f : Fin 2 × Fin 2 → ℂ) :
    MvPolynomial.eval f pF = (f (0, 0) - Complex.I * f (1, 0)) - Complex.I * (f (0, 1) - Complex.I * f (1, 1)) := by
  simp [pF, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]

theorem flatMSection_eq_harm (m n : ℕ) (ε' : ℝ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M) :
    S = fun M : Matrix (Fin 2) (Fin 3) ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((M v.1 (Fin.castSucc v.2) : ℝ) : ℂ)) (pF ^ m) *
        (((M 0 2 : ℝ) : ℂ) + ((ε' : ℝ) : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n * gaussian3 M := by
  rw [hS]
  funext M
  rw [map_pow, eval_pF]
  simp only [Fin.castSucc_zero, Fin.castSucc_one]

theorem flatMSection_mem_polyGauss3 (m n : ℕ) (ε' : ℝ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M) :
    S ∈ polyGauss3 := by
  refine ⟨((MvPolynomial.X (0, 0) - MvPolynomial.C Complex.I * MvPolynomial.X (1, 0)) -
      MvPolynomial.C Complex.I * (MvPolynomial.X (0, 1) - MvPolynomial.C Complex.I * MvPolynomial.X (1, 1))) ^ m *
    (MvPolynomial.X (0, 2) + MvPolynomial.C ((ε' : ℝ) : ℂ) * MvPolynomial.C Complex.I * MvPolynomial.X (1, 2)) ^ n, ?_⟩
  funext M
  simp only [hS, map_mul, map_sub, map_add, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C]

theorem harmF_eM (x y₁ y₂ θ : ℝ) :
    ((((eM x y₁ y₂ θ 0 0 : ℝ) : ℂ) - Complex.I * ((eM x y₁ y₂ θ 1 0 : ℝ) : ℂ)) -
        Complex.I * (((eM x y₁ y₂ θ 0 1 : ℝ) : ℂ) - Complex.I * ((eM x y₁ y₂ θ 1 1 : ℝ) : ℂ))) =
      (((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
        ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) := by
  simp only [eM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  linear_combination (Complex.cos (θ : ℂ) / ((y₂ : ℝ) : ℂ)) * Complex.I_mul_I

section Pointwise

variable (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
  (hpsiInf : ∀ x : InfiniteAdeleRing ℚ, psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
  {P : RealArchParam} (D : ArchDatumR P) (k₀ m n : ℕ) (ε' : ℝ)
  (hcol : (ε' = -1 ∧ (n : ℤ) = (k₀ : ℤ) - m) ∨ (ε' = 1 ∧ (n : ℤ) = (m : ℤ) - k₀))
  (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ (k₀ : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
  (u₃ : ℂ) (a₃ : ZMod 2) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
  (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
  (c : ℝ) (hc : c ≠ 0)

noncomputable def Gfun (e : Fin 2 → Fin 2 → ℝ) : ℂ :=
  godementInner3 psiInf S (Matrix.of e) 1 *
    quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
    D.W (diagOne c * (Matrix.of e)⁻¹)

noncomputable def hX (x y₁ y₂ : ℝ) : ℂ :=
  (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
    ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + (Complex.I * (((1 / y₁ : ℝ)) : ℂ)) * (x : ℂ)) ^ m * psi (c * x)

noncomputable def KY (y₁ y₂ : ℝ) : ℂ :=
  ((ε' : ℂ) * (a : ℂ)) ^ n *
    (quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (n + 1) / |y₁| : ℝ)) : ℂ) *
      (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) *
      (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (diagOne (c * y₁ / y₂)))

include hpsiInf hcol hDW hS hc in
theorem pointwise {x y₁ y₂ θ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    Gfun psiInf D u₃ a₃ S c (fun i j => eM x y₁ y₂ θ i j) * ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) =
      hX m c x y₁ y₂ * KY a D n ε' u₃ a₃ c y₁ y₂ := by
  have hε : ε' = 1 ∨ ε' = -1 := by rcases hcol with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hofe : (Matrix.of fun i j => eM x y₁ y₂ θ i j) = eM x y₁ y₂ θ := rfl
  have hdet : (Matrix.of fun i j => eM x y₁ y₂ θ i j).det ≠ 0 := by
    rw [hofe, det_eM]; exact inv_ne_zero (mul_ne_zero hy₁ hy₂.ne')
  have hGI := LanglandsTunnell.CubicInduction.godementInner3_eq_mul_exp_of_blockPoly_mul_colHarmonic_gaussian3 a psiInf hpsiInf
    (pF ^ m) n ε' hε S (flatMSection_eq_harm m n ε' S hS) (fun i j => eM x y₁ y₂ θ i j) hdet
  rw [Gfun, hGI]
  simp only [hofe]
  rw [map_pow, eval_pF, harmF_eM, mul_pow, inv_eM x y₁ y₂ θ hy₁ hy₂.ne', gM_one_zero, gM_one_one, sumsq_eM, det_eM,
    W_diagOne_mul_gM_weight D k₀ hDW hc x hy₁ hy₂ θ, hX, KY]
  have hy₂' : |y₂| = y₂ := abs_of_pos hy₂
  have habs : |(y₁ * y₂)⁻¹| = (|y₁| * y₂)⁻¹ := by rw [abs_inv, abs_mul, hy₂']
  have hexp : ∀ u v : ℝ, (Real.exp u : ℂ) * (Real.exp v : ℂ) = (Real.exp (u + v) : ℂ) := fun u v => by
    rw [Real.exp_add]; push_cast; ring
  have hy1a : (|y₁| : ℝ) ≠ 0 := abs_ne_zero.2 hy₁
  have e1 : (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
      (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2))) : ℂ) =
      (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
        (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) := by
    rw [hexp, hexp]
    congr 2
    have : (y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2 = y₂ ^ 2 := by linear_combination (y₂ ^ 2) * Real.sin_sq_add_cos_sq θ
    rw [this]
    field_simp
    ring
  have hR : (|(y₁ * y₂)⁻¹|)⁻¹ * (|(y₁ * y₂)⁻¹| ^ 2)⁻¹ * (y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹) = y₂ / |y₁| := by
    rw [habs, abs_mul, hy₂']
    field_simp
  have hRc : (((|(y₁ * y₂)⁻¹| : ℝ) : ℂ))⁻¹ * ((((|(y₁ * y₂)⁻¹| : ℝ) : ℂ)) ^ 2)⁻¹ *
      (((y₂ : ℝ) : ℂ) ^ 2 * ((((|y₁ * y₂| : ℝ) : ℂ)) ^ 4)⁻¹) = ((y₂ : ℝ) : ℂ) / ((|y₁| : ℝ) : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hR
    push_cast at this
    exact this
  push_cast at e1 ⊢
  have hcs : Complex.sin (θ : ℂ) ^ 2 + Complex.cos (θ : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
  set Φp : ℂ := Complex.cos (θ : ℂ) + Complex.I * Complex.sin (θ : ℂ) with hΦp
  set Φm : ℂ := Complex.cos (θ : ℂ) - Complex.I * Complex.sin (θ : ℂ) with hΦm
  have hpm : Φp * Φm = 1 := by
    rw [hΦp, hΦm]; linear_combination hcs + (-(Complex.sin (θ : ℂ)) ^ 2) * Complex.I_sq
  set Ψ : ℂ := ((y₂ : ℝ) : ℂ) * Complex.sin (θ : ℂ) + (ε' : ℂ) * Complex.I * (((y₂ : ℝ) : ℂ) * Complex.cos (θ : ℂ)) with hΨ

  set Cc : ℂ := ((1 / (y₁ : ℂ) - 1 / (y₂ : ℂ) + Complex.I * ((x : ℂ) / (y₁ : ℂ))) ^ m * psi (c * x)) *
    quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (diagOne (c * y₁ / y₂)) with hCc
  set E₁ : ℂ := Complex.exp (-((Real.pi : ℂ) * ((1 + (x : ℂ) ^ 2) / (y₁ : ℂ) ^ 2 + 1 / (y₂ : ℂ) ^ 2))) with hE₁
  set E₂ : ℂ := Complex.exp (-((Real.pi : ℂ) * (a : ℂ) ^ 2 *
    ((((y₂ : ℝ) : ℂ) * Complex.sin (θ : ℂ)) ^ 2 + (((y₂ : ℝ) : ℂ) * Complex.cos (θ : ℂ)) ^ 2))) with hE₂
  set E₃ : ℂ := Complex.exp (-((Real.pi : ℂ) * ((x : ℂ) ^ 2 / (y₁ : ℂ) ^ 2))) with hE₃
  set E₄ : ℂ := Complex.exp (-((Real.pi : ℂ) * (((y₁ : ℂ) ^ 2)⁻¹ + ((y₂ : ℂ) ^ 2)⁻¹ + (a : ℂ) ^ 2 * (y₂ : ℂ) ^ 2))) with hE₄
  set d : ℂ := ((|(y₁ * y₂)⁻¹| : ℝ) : ℂ) with hd
  set R₀ : ℂ := d⁻¹ * (d ^ 2)⁻¹ * (((y₂ : ℝ) : ℂ) ^ 2 * ((((|y₁ * y₂| : ℝ) : ℂ)) ^ 4)⁻¹) with hR₀
  have hRc' : R₀ = ((y₂ : ℝ) : ℂ) / ((|y₁| : ℝ) : ℂ) := by rw [hR₀, hd]; linear_combination hRc

  have hcore : Φp ^ m * ((-Complex.I * (a : ℂ)) ^ n * Ψ ^ n) * Φm ^ k₀ = ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n := by
    rw [← mul_pow]
    rcases hcol with ⟨hε1, hn⟩ | ⟨hε1, hn⟩
    ·
      have hk : k₀ = m + n := by omega
      have hprod : (-Complex.I * (a : ℂ)) * Ψ = (((ε' : ℂ) * (a : ℂ)) * ((y₂ : ℝ) : ℂ)) * Φp := by
        rw [hΨ, hΦp, hε1]; push_cast
        linear_combination ((a : ℂ) * ((y₂ : ℝ) : ℂ) * Complex.cos (θ : ℂ)) * Complex.I_sq
      rw [hprod, hk]
      calc Φp ^ m * ((((ε' : ℂ) * (a : ℂ)) * ((y₂ : ℝ) : ℂ)) * Φp) ^ n * Φm ^ (m + n)
          = ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n * (Φp * Φm) ^ (m + n) := by ring
        _ = ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n := by rw [hpm, one_pow, mul_one]
    ·
      have hk : m = n + k₀ := by omega
      have hprod : (-Complex.I * (a : ℂ)) * Ψ = (((ε' : ℂ) * (a : ℂ)) * ((y₂ : ℝ) : ℂ)) * Φm := by
        rw [hΨ, hΦm, hε1]; push_cast
        linear_combination (-((a : ℂ) * ((y₂ : ℝ) : ℂ) * Complex.cos (θ : ℂ))) * Complex.I_sq
      rw [hprod, hk]
      calc Φp ^ (n + k₀) * ((((ε' : ℂ) * (a : ℂ)) * ((y₂ : ℝ) : ℂ)) * Φm) ^ n * Φm ^ k₀
          = ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n * (Φp * Φm) ^ (n + k₀) := by ring
        _ = ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n := by rw [hpm, one_pow, mul_one]
  linear_combination (Cc * E₁ * E₂ * R₀) * hcore +
    (Cc * ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n * R₀) * e1 +
    (Cc * E₃ * E₄ * ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n) * hRc'

end Pointwise

section Assemble

variable (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
  (hpsiInf : ∀ x : InfiniteAdeleRing ℚ, psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
  {P : RealArchParam} (D : ArchDatumR P) (k₀ m n : ℕ) (ε' : ℝ)
  (hcol : (ε' = -1 ∧ (n : ℤ) = (k₀ : ℤ) - m) ∨ (ε' = 1 ∧ (n : ℤ) = (m : ℤ) - k₀))
  (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ (k₀ : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
  (u₃ : ℂ) (a₃ : ZMod 2) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
  (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
  (c : ℝ) (hc : c ≠ 0)

include hpsiInf hcol hDW hS hc in

theorem assemble (hG : Integrable (Gfun psiInf D u₃ a₃ S c)) :
    ∫ e : Fin 2 → Fin 2 → ℝ, Gfun psiInf D u₃ a₃ S c e =
      2 * (Real.pi : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Ioi (0 : ℝ), (∫ x : ℝ, hX m c x y₁ y₂) * KY a D n ε' u₃ a₃ c y₁ y₂ := by
  have hK := LanglandsTunnell.RankinSelberg.integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional (Gfun psiInf D u₃ a₃ S c)
  obtain ⟨hiff, hcv⟩ := hK
  have hF := hiff.1 hG
  rw [hcv]
  set R : Set (ℝ × ℝ × ℝ × ℝ) := univ ×ˢ (univ ×ˢ (Ioi (0 : ℝ) ×ˢ Ioc (0 : ℝ) (2 * Real.pi))) with hR
  have hRm : MeasurableSet R := MeasurableSet.univ.prod (MeasurableSet.univ.prod (measurableSet_Ioi.prod measurableSet_Ioc))
  set F' : ℝ × ℝ × ℝ × ℝ → ℂ := fun p => hX m c p.1 p.2.1 p.2.2.1 * KY a D n ε' u₃ a₃ c p.2.1 p.2.2.1 with hF'
  have hnull : (volume : Measure (ℝ × ℝ × ℝ × ℝ)) {p | p.2.1 = 0} = 0 := by
    have hset : {p : ℝ × ℝ × ℝ × ℝ | p.2.1 = 0} = (univ : Set ℝ) ×ˢ (({0} : Set ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
      ext p; simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton]
    simp
  have hae : ∀ᵐ p : ℝ × ℝ × ℝ × ℝ, p.2.1 ≠ 0 := measure_eq_zero_iff_ae_notMem.1 hnull
  have hptw : ∀ᵐ p : ℝ × ℝ × ℝ × ℝ ∂(volume.restrict R),
      (Gfun psiInf D u₃ a₃ S c (fun i j =>
          !![Real.cos p.2.2.2 / p.2.1, -(p.1 * Real.cos p.2.2.2) / p.2.1 + Real.sin p.2.2.2 / p.2.2.1;
             -(Real.sin p.2.2.2) / p.2.1, p.1 * Real.sin p.2.2.2 / p.2.1 + Real.cos p.2.2.2 / p.2.2.1] i j) *
        ((p.2.2.1 ^ 2 * (|p.2.1 * p.2.2.1| ^ 4)⁻¹ : ℝ) : ℂ)) = F' p := by
    rw [ae_restrict_iff' hRm]
    filter_upwards [hae] with p hp hpR
    obtain ⟨x, y₁, y₂, θ⟩ := p
    simp only [hR, mem_prod, mem_univ, mem_Ioi, mem_Ioc, true_and] at hpR
    exact pointwise a psiInf hpsiInf D k₀ m n ε' hcol hDW u₃ a₃ S hS c hc hp hpR.1
  rw [integral_congr_ae hptw]
  have hF'int : Integrable F' (volume.restrict R) := hF.congr hptw
  have hμ : (volume.restrict R : Measure (ℝ × ℝ × ℝ × ℝ)) =
      (volume : Measure ℝ).prod ((volume : Measure ℝ).prod
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) := by
    rw [hR, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ, Measure.volume_eq_prod,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [hμ] at hF'int ⊢
  rw [integral_prod_symm _ hF'int]
  have hinner : ∀ q : ℝ × ℝ × ℝ, ∫ x : ℝ, F' (x, q) = (∫ x : ℝ, hX m c x q.1 q.2.1) * KY a D n ε' u₃ a₃ c q.1 q.2.1 := by
    intro q; simp only [hF']; exact integral_mul_const _ _
  simp_rw [hinner]
  have hint2 : Integrable (fun q : ℝ × ℝ × ℝ => (∫ x : ℝ, hX m c x q.1 q.2.1) * KY a D n ε' u₃ a₃ c q.1 q.2.1)
      ((volume : Measure ℝ).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) := by
    have := hF'int.integral_prod_right
    refine this.congr (ae_of_all _ fun q => hinner q)
  rw [integral_prod _ hint2]
  have hstep : ∀ᵐ y₁ : ℝ ∂volume,
      (∫ q : ℝ × ℝ, (∫ x : ℝ, hX m c x (y₁, q).1 (y₁, q).2.1) * KY a D n ε' u₃ a₃ c (y₁, q).1 (y₁, q).2.1
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) =
        2 * (Real.pi : ℂ) * ∫ y₂ in Ioi (0 : ℝ), (∫ x : ℝ, hX m c x y₁ y₂) * KY a D n ε' u₃ a₃ c y₁ y₂ := by
    filter_upwards [hint2.prod_right_ae] with y₁ hy
    rw [integral_prod _ hy]
    have hθ : ∀ y₂ : ℝ, (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), (∫ x : ℝ, hX m c x y₁ y₂) * KY a D n ε' u₃ a₃ c y₁ y₂) =
        2 * (Real.pi : ℂ) * ((∫ x : ℝ, hX m c x y₁ y₂) * KY a D n ε' u₃ a₃ c y₁ y₂) := by
      intro y₂
      rw [setIntegral_const, Real.volume_real_Ioc_of_le (by positivity), Complex.real_smul]
      push_cast; ring
    simp_rw [hθ]
    rw [integral_const_mul]
  rw [integral_congr_ae hstep, integral_const_mul]

end Assemble

namespace SingArr

theorem volume_setOf_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} = 0 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} :=
    measurableSet_eq_fun (measurable_const.mul measurable_snd) (measurable_const.mul measurable_fst)
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  refine Filter.Eventually.of_forall fun u => ?_
  have hsub : Prod.mk u ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} ⊆ {r₁ * u / r₀} := by
    intro v hv
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv
    simp only [Set.mem_singleton_iff]
    field_simp
    linarith [hv]
  exact measure_mono_null hsub (Real.volume_singleton)

theorem volume_setOf_vector_on_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (Fin 2 → ℝ)) {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} = 0 := by
  have hpre : {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} =
      MeasurableEquiv.piFinTwo (fun _ => ℝ) ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} := by
    ext q; rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).map_eq]
  exact volume_setOf_line_eq_zero r₀ r₁ h

theorem volume_setOf_det_eq_zero :
    (volume : Measure (Fin 2 → Fin 2 → ℝ)) {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} = 0 := by
  have hdet : ∀ x : Fin 2 → Fin 2 → ℝ, (Matrix.of x).det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := fun x => by
    rw [Matrix.det_fin_two]; rfl
  set S : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) := {p | p.1 0 * p.2 1 - p.1 1 * p.2 0 = 0} with hS
  have hpre : {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} =
      MeasurableEquiv.piFinTwo (fun _ => Fin 2 → ℝ) ⁻¹' S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hdet, hS]
    rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).map_eq]
  have hmeas : MeasurableSet S := by
    refine measurableSet_eq_fun ?_ measurable_const
    exact ((measurable_pi_apply 0).comp measurable_fst).mul ((measurable_pi_apply 1).comp measurable_snd) |>.sub
      (((measurable_pi_apply 1).comp measurable_fst).mul ((measurable_pi_apply 0).comp measurable_snd))
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  have hae : ∀ᵐ r : Fin 2 → ℝ ∂(volume : Measure (Fin 2 → ℝ)), r 0 ≠ 0 :=
    Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) 0 (0 : ℝ)
  filter_upwards [hae] with r hr
  have hfib : Prod.mk r ⁻¹' S ⊆ {q : Fin 2 → ℝ | r 0 * q 1 = r 1 * q 0} := by
    intro q hq
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq] at hq
    simp only [Set.mem_setOf_eq]
    linarith [hq]
  exact measure_mono_null hfib (volume_setOf_vector_on_line_eq_zero (r 0) (r 1) hr)

end SingArr

section Integrability

open Topology

variable (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
  (hpsiInf : ∀ x : InfiniteAdeleRing ℚ, psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
  {P : RealArchParam} (D : ArchDatumR P) (m n : ℕ) (ε' : ℝ) (hε : ε' = 1 ∨ ε' = -1)
  (u₃ : ℂ) (a₃ : ZMod 2) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
  (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
  (c : ℝ) (hc : c ≠ 0)

theorem continuousOn_quasiChar (u : ℂ) (b : ZMod 2) : ContinuousOn (fun r : ℝ => quasiChar u b r) {r | r ≠ 0} := by
  intro r hr
  refine ContinuousAt.continuousWithinAt ?_
  unfold quasiChar
  refine ContinuousAt.mul ?_ ?_
  · exact (Complex.continuousAt_ofReal_cpow_const |r| u (Or.inr (abs_ne_zero.2 hr))).comp continuous_abs.continuousAt
  · split_ifs
    · exact continuousAt_const
    · exact ((continuous_of_discreteTopology (f := fun s : SignType => ((s : ℝ) : ℂ))).continuousAt).comp
        (continuousAt_sign_of_ne_zero hr)

def U : Set (Fin 2 → Fin 2 → ℝ) := {e | (Matrix.of e).det ≠ 0}

theorem isOpen_U : IsOpen U :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem continuousOn_inv : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e)⁻¹) U := by
  intro e he
  have h : ContinuousAt Ring.inverse (Matrix.of e).det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ he
  exact (continuousAt_matrix_inv (Matrix.of e) h).continuousWithinAt

include hpsiInf hS hc hε in
theorem continuousOn_Gfun : ContinuousOn (Gfun psiInf D u₃ a₃ S c) U := by

  have heq : ∀ e ∈ U, Gfun psiInf D u₃ a₃ S c e =
      (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) (pF ^ m) *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ j : Fin 2, e i j ^ 2)) : ℂ) *
          (((|(Matrix.of e).det|)⁻¹ : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) ^ n *
          ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + ((ε' : ℝ) : ℂ) * Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) ^ n *
          (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
        quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
        D.W (diagOne c * (Matrix.of e)⁻¹) := by
    intro e he
    rw [Gfun, LanglandsTunnell.CubicInduction.godementInner3_eq_mul_exp_of_blockPoly_mul_colHarmonic_gaussian3 a psiInf hpsiInf
      (pF ^ m) n ε' hε S (flatMSection_eq_harm m n ε' S hS) e he]
  refine ContinuousOn.congr ?_ (fun e he => heq e he)
  have hinv := continuousOn_inv
  have hent : ∀ i j : Fin 2, ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e)⁻¹ i j) U := fun i j =>
    (continuous_apply_apply i j).continuousOn.comp hinv (Set.mapsTo_univ _ _)
  have hcoord : Continuous fun e : Fin 2 → Fin 2 → ℝ => (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) :=
    continuous_pi fun v => Complex.continuous_ofReal.comp ((continuous_apply v.2).comp (continuous_apply v.1))
  have hev : ∀ q : MvPolynomial (Fin 2 × Fin 2) ℂ, Continuous fun e : Fin 2 → Fin 2 → ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) q := fun q =>
    (MvPolynomial.continuous_eval q).comp hcoord
  have hdet : Continuous fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det := continuous_id.matrix_det
  have hdetU : ∀ e ∈ U, (Matrix.of e).det ≠ 0 := fun e he => he
  have hW : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => D.W (diagOne c * (Matrix.of e)⁻¹)) U := by
    have h1 : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => (diagOne c * (Matrix.of e)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ)) U :=
      continuousOn_const.mul hinv
    have hmaps : Set.MapsTo (fun e : Fin 2 → Fin 2 → ℝ => (diagOne c * (Matrix.of e)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ)) U glSet := by
      intro e he
      show (Matrix.of (diagOne c * (Matrix.of e)⁻¹)).det ≠ 0
      have : Matrix.of (diagOne c * (Matrix.of e)⁻¹) = diagOne c * (Matrix.of e)⁻¹ := rfl
      rw [this, Matrix.det_mul, Matrix.det_nonsing_inv]
      have hd : (diagOne c).det = c := by simp [diagOne, Matrix.det_fin_two_of]
      rw [hd, Ring.inverse_eq_inv]
      exact mul_ne_zero hc (inv_ne_zero he)
    have h2 := D.smooth.continuousOn.comp h1 hmaps
    exact h2
  have hq : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => quasiChar (u₃ + 2) a₃ (Matrix.of e).det) U :=
    (continuousOn_quasiChar (u₃ + 2) a₃).comp hdet.continuousOn hdetU
  have habs2 : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) U :=
    Complex.continuous_ofReal.continuousOn.comp
      (((continuous_abs.comp hdet).pow 2).continuousOn.inv₀ fun e he => pow_ne_zero 2 (abs_ne_zero.2 he)) (Set.mapsTo_univ _ _)
  have habs1 : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => (((|(Matrix.of e).det|)⁻¹ : ℝ) : ℂ)) U :=
    Complex.continuous_ofReal.continuousOn.comp
      ((continuous_abs.comp hdet).continuousOn.inv₀ fun e he => abs_ne_zero.2 he) (Set.mapsTo_univ _ _)
  have hE1 : Continuous fun e : Fin 2 → Fin 2 → ℝ => (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ j : Fin 2, e i j ^ 2)) : ℂ) := by
    refine Complex.continuous_ofReal.comp (Real.continuous_exp.comp ?_)
    refine (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_).const_mul _ |>.neg
    exact (continuous_apply_apply i j).pow 2
  have hE2 : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ =>
      (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) U := by
    refine Complex.continuous_ofReal.continuousOn.comp (Real.continuous_exp.continuousOn.comp ?_ (Set.mapsTo_univ _ _))
      (Set.mapsTo_univ _ _)
    exact ((((hent 1 0).pow 2).add ((hent 1 1).pow 2)).const_smul (Real.pi * (a : ℝ) ^ 2)).neg.congr
      (fun e _ => by simp [smul_eq_mul, Pi.neg_apply, Pi.smul_apply, Pi.add_apply, Pi.pow_apply]; try ring)
  have hρ : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ =>
      ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + ((ε' : ℝ) : ℂ) * Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) ^ n) U :=
    ((Complex.continuous_ofReal.continuousOn.comp (hent 1 0) (Set.mapsTo_univ _ _)).add
      (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.comp (hent 1 1) (Set.mapsTo_univ _ _)))).pow n
  exact (((((((((hev (pF ^ m)).continuousOn).mul hE1.continuousOn).mul habs1).mul continuousOn_const).mul hρ).mul hE2).mul hq).mul
    habs2).mul hW

theorem Gfun_eq_jacquetIntegrand3 : Gfun psiInf D u₃ a₃ S c = jacquetIntegrand3 D u₃ a₃ c psiInf S 1 := by
  funext e
  rw [Gfun, jacquetIntegrand3, AutomorphicForm.StandardKernel.realMat_one]

theorem neg_re_le_sum_of_mem {M : Multiset ℂ} {μ : ℂ} (h : μ ∈ M) : -μ.re ≤ (M.map (fun z => ‖z‖)).sum := by
  have h1 : -μ.re ≤ ‖μ‖ := by have := Complex.abs_re_le_norm μ; have := neg_abs_le μ.re; linarith
  have h2 : ‖μ‖ ≤ (M.map (fun z => ‖z‖)).sum :=
    Multiset.single_le_sum (fun x hx => by obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg z) _
      (Multiset.mem_map_of_mem _ h)
  linarith

include hpsiInf hS hc hε in
theorem integrable_Gfun (ha : a ≠ 0) : Integrable (Gfun psiInf D u₃ a₃ S c) := by

  set B : ZMod 2 → ℝ := fun b => ((P.twist 0 b).gammaR.map (fun z => ‖z‖)).sum + ((P.twist 0 b).gammaC.map (fun z => ‖z‖)).sum with hB
  set c₀ : ℝ := B 0 + B 1 + 1 with hc₀
  have hBn : ∀ b, 0 ≤ B b := fun b => by
    simp only [hB]
    refine add_nonneg (Multiset.sum_nonneg fun x hx => ?_) (Multiset.sum_nonneg fun x hx => ?_) <;>
    · obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg z
  have hBle : ∀ b, B b ≤ B 0 + B 1 := fun b => by
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl
    · linarith [hBn 1]
    · linarith [hBn 0]
  have hc₀' : ∀ b : ZMod 2, (∀ μ ∈ (P.twist 0 b).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 b).gammaC, -ν.re < c₀) := by
    intro b
    have hgC : 0 ≤ ((P.twist 0 b).gammaC.map (fun z => ‖z‖)).sum :=
      Multiset.sum_nonneg fun x hx => by obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg z
    have hgR : 0 ≤ ((P.twist 0 b).gammaR.map (fun z => ‖z‖)).sum :=
      Multiset.sum_nonneg fun x hx => by obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg z
    refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
    · have := neg_re_le_sum_of_mem hμ; have := hBle b; simp only [hB] at *; linarith
    · have := neg_re_le_sum_of_mem hν; have := hBle b; simp only [hB] at *; linarith
  obtain ⟨hmaj, -, -, -⟩ := LanglandsTunnell.CubicInduction.exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
    (P := P) u₃ a₃ a psiInf hpsiInf ha D S (flatMSection_mem_polyGauss3 m n ε' S hS) c₀ hc₀'
  obtain ⟨V, hV, F, hF, hbound⟩ := hmaj 1 (max c₀ (-u₃.re) + 1) (by linarith)
  have h1 : (1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) ∈ V := mem_of_mem_nhds hV

  have hUc : (volume : Measure (Fin 2 → Fin 2 → ℝ)) Uᶜ = 0 := by
    have : Uᶜ = {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} := by ext x; simp [U]
    rw [this]; exact SingArr.volume_setOf_det_eq_zero
  have haeU : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, e ∈ U := by
    rw [ae_iff]; exact hUc
  have hmeas : AEStronglyMeasurable (Gfun psiInf D u₃ a₃ S c) volume := by
    have h := (continuousOn_Gfun a psiInf hpsiInf D m n ε' hε u₃ a₃ S hS c hc).aestronglyMeasurable (μ := volume) isOpen_U.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem haeU] at h
  refine Integrable.mono' (hF.const_mul (|c| ^ (1 - (max c₀ (-u₃.re) + 1)))) hmeas (ae_of_all _ fun e => ?_)
  rw [Gfun_eq_jacquetIntegrand3]
  exact hbound 1 h1 c hc e

end Integrability

end Ws23PhiFlatM

open Ws23PhiFlatM LanglandsTunnell.Converse.ArchR Set in
theorem solution
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (k₀ : ℕ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (k₀ : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (m n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = (k₀ : ℤ) - m) ∨ (ε' = 1 ∧ (n : ℤ) = (m : ℤ) - k₀))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (y : ℝ) (hy : y ≠ 0) :
    jacquetVector3 D u₃ a₃ ((a : ℝ) * y) psiInf S 1 =
      2 * (Real.pi : ℂ) * ((ε' : ℂ) * (a : ℂ)) ^ n *
        ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ),
          ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ *
            (((y₂ ^ (n + 1) / |y₁| : ℝ)) : ℂ) *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) *
            (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) *
            (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
              ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + (Complex.I * (((1 / y₁ : ℝ)) : ℂ)) * (x : ℂ)) ^ m *
              ArchR.psi ((a : ℝ) * y * x)) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hc : (a : ℝ) * y ≠ 0 := mul_ne_zero ha' hy
  have hε : ε' = 1 ∨ ε' = -1 := by rcases hcol with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hG := integrable_Gfun a psiInf hpsiInf D m n ε' hε u₃ a₃ S hS ((a : ℝ) * y) hc ha
  rw [jacquetVector3_eq, AutomorphicForm.StandardKernel.realMat_one, Matrix.det_one]
  have hq1 : quasiChar (u₃ + 1) a₃ (1 : ℝ) = 1 := by
    unfold quasiChar; rw [abs_one, Complex.ofReal_one, Complex.one_cpow, one_mul]; split_ifs <;> simp
  rw [hq1, one_mul, ← Gfun_eq_jacquetIntegrand3, assemble a psiInf hpsiInf D k₀ m n ε' hcol hDW u₃ a₃ S hS ((a : ℝ) * y) hc hG]
  have key : ∀ y₁ : ℝ, (∫ y₂ in Ioi (0 : ℝ), (∫ x : ℝ, hX m ((a : ℝ) * y) x y₁ y₂) * KY a D n ε' u₃ a₃ ((a : ℝ) * y) y₁ y₂) =
      ((ε' : ℂ) * (a : ℂ)) ^ n * ∫ y₂ in Ioi (0 : ℝ),
          ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ *
            (((y₂ ^ (n + 1) / |y₁| : ℝ)) : ℂ) *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) *
            (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) *
            (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
              ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + (Complex.I * (((1 / y₁ : ℝ)) : ℂ)) * (x : ℂ)) ^ m *
              ArchR.psi ((a : ℝ) * y * x)) := by
    intro y₁
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y₂ _ => ?_
    simp only [KY, hX]
    ring
  simp_rw [key]
  rw [integral_const_mul]
  ring

#print axioms solution

end S_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3 (solution)
