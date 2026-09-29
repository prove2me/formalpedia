-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e8842a16-f6fd-5f10-9014-aa6a44cf63dd

import Mathlib
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
import Definitions.Def_LanglandsTunnell_JLConverse
import Theorems.Thm_LanglandsTunnell_RankinSelberg_archWhittaker_w0R_mul_transposeInv_upperUnit_eq_mul_archProfile
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_longWeyl3_transposeInv3_iota_upperUnit_eq
import Theorems.Thm_LanglandsTunnell_CubicInduction_integral_dualConfig_eq_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_archWeightChar_mul_W_diagOne
import Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional
import Theorems.Thm_MeasureTheory_setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free
import Theorems.Thm_LanglandsTunnell_Converse_integrable_dualThetaFree_integrand
import Theorems.Thm_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv
import Theorems.Thm_LanglandsTunnell_exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm AutomorphicForm.WindowedSiegel LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace K7Rot

noncomputable def rotM (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem det_rotM (θ : ℝ) : (rotM θ).det = 1 := by
  rw [rotM, Matrix.det_fin_two_of]
  have := Real.sin_sq_add_cos_sq θ
  nlinarith

noncomputable def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM θ) (by rw [det_rotM]; exact one_ne_zero)

@[scoped simp] theorem coe_rotGL (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM θ := rfl

theorem rotGL_mem (θ : ℝ) : rotGL θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [coe_rotGL, det_rotM], ?_, ?_⟩
  · rw [coe_rotGL, det_rotM, norm_one]
  · intro x y
    simp only [coe_rotGL, rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', Real.norm_eq_abs, sq_abs]
    have := Real.sin_sq_add_cos_sq θ
    nlinarith [this]

noncomputable def rotK (θ : ℝ) : rowIsometrySubgroup₀ ℝ := ⟨rotGL θ, rotGL_mem θ⟩

theorem coe_rotK (θ : ℝ) :
    ((rotK θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := rfl

theorem archWeightOneℝ_rotK (θ : ℝ) :
    (archWeightOneℝ (rotK θ) : ℂ) = Complex.exp (-(θ : ℂ) * Complex.I) := by
  show firstRowℂ (rotGL θ) = _
  apply Complex.ext
  · simp [firstRowℂ, rotM, Complex.exp_re]
  · simp [firstRowℂ, rotM, Complex.exp_im]

theorem archWeightCharℝ_rotK (k : ℤ) (θ : ℝ) :
    (archWeightCharℝ k (rotK θ) : ℂ) = Complex.exp (-(k : ℂ) * (θ : ℂ) * Complex.I) := by
  have h1 : (archWeightCharℝ k (rotK θ) : ℂ) = ((archWeightOneℝ (rotK θ)) ^ k : ℂˣ) := rfl
  rw [h1, Units.val_zpow_eq_zpow_val, archWeightOneℝ_rotK, ← Complex.exp_int_mul]
  congr 1; ring

theorem cos_add_I_sin (θ : ℝ) :
    ((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ) = Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]; ring

theorem col_factor (θ y₂ ε' : ℝ) (hε' : ε' = 1 ∨ ε' = -1) :
    ((y₂ * Real.sin θ : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ) =
      ((ε' : ℂ) * Complex.I * (y₂ : ℂ)) * Complex.exp (-((ε' : ℂ) * (θ : ℂ)) * Complex.I) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rcases hε' with h | h
  · subst h
    push_cast
    rw [show -((1 : ℂ) * (θ : ℂ)) * Complex.I = (-(θ : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    linear_combination ((y₂ : ℂ) * (Real.sin θ : ℂ)) * hI
  · subst h
    push_cast
    rw [show -((-1 : ℂ) * (θ : ℂ)) * Complex.I = (θ : ℂ) * Complex.I by ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    linear_combination ((y₂ : ℂ) * (Real.sin θ : ℂ)) * hI

theorem phase_eq_one (m n : ℕ) (k₀ : ℤ) (ε' θ : ℝ)
    (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀)) :
    Complex.exp ((θ : ℂ) * Complex.I) ^ m * Complex.exp (-((ε' : ℂ) * (θ : ℂ)) * Complex.I) ^ n *
      Complex.exp (-(k₀ : ℂ) * (θ : ℂ) * Complex.I) = 1 := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
  rcases hcol with ⟨hε, hn⟩ | ⟨hε, hn⟩
  · have hn' : ((n : ℤ) : ℂ) = (k₀ : ℂ) - (m : ℂ) := by rw [hn]; push_cast; ring
    have : (n : ℂ) = (k₀ : ℂ) - (m : ℂ) := by exact_mod_cast hn'
    rw [this, hε]; push_cast
    rw [show (m : ℂ) * ((θ : ℂ) * Complex.I) + ((k₀ : ℂ) - (m : ℂ)) * (-((-1 : ℂ) * (θ : ℂ)) * Complex.I) +
      -(k₀ : ℂ) * (θ : ℂ) * Complex.I = 0 by ring, Complex.exp_zero]
  · have hn' : ((n : ℤ) : ℂ) = (m : ℂ) - (k₀ : ℂ) := by rw [hn]; push_cast; ring
    have : (n : ℂ) = (m : ℂ) - (k₀ : ℂ) := by exact_mod_cast hn'
    rw [this, hε]; push_cast
    rw [show (m : ℂ) * ((θ : ℂ) * Complex.I) + ((m : ℂ) - (k₀ : ℂ)) * (-((1 : ℂ) * (θ : ℂ)) * Complex.I) +
      -(k₀ : ℂ) * (θ : ℂ) * Complex.I = 0 by ring, Complex.exp_zero]

end K7Rot
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.K7Rot"

namespace DualKit

noncomputable def eM (x y₁ y₂ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ / y₁, -(x * Real.cos θ) / y₁ + Real.sin θ / y₂;
     -(Real.sin θ) / y₁, x * Real.sin θ / y₁ + Real.cos θ / y₂]

noncomputable def gM (x y₁ y₂ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
     y₂ * Real.sin θ, y₂ * Real.cos θ]

section
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

theorem gM_one_zero : gM x y₁ y₂ θ 1 0 = y₂ * Real.sin θ := by simp [gM]
theorem gM_one_one : gM x y₁ y₂ θ 1 1 = y₂ * Real.cos θ := by simp [gM]
theorem eM_zero_zero : eM x y₁ y₂ θ 0 0 = Real.cos θ / y₁ := by simp [eM]
theorem eM_one_zero : eM x y₁ y₂ θ 1 0 = -(Real.sin θ) / y₁ := by simp [eM]
theorem eM_zero_one : eM x y₁ y₂ θ 0 1 = -(x * Real.cos θ) / y₁ + Real.sin θ / y₂ := by simp [eM]
theorem eM_one_one : eM x y₁ y₂ θ 1 1 = x * Real.sin θ / y₁ + Real.cos θ / y₂ := by simp [eM]

theorem gaussArg_eM (a₂ : ℝ) :
    a₂⁻¹ ^ 2 * (eM x y₁ y₂ θ 0 1 ^ 2 + eM x y₁ y₂ θ 1 1 ^ 2) + (eM x y₁ y₂ θ 0 0 ^ 2 + eM x y₁ y₂ θ 1 0 ^ 2) =
      x ^ 2 / (a₂ * y₁) ^ 2 + (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹) := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [eM_zero_zero, eM_one_zero, eM_zero_one, eM_one_one]
  linear_combination (a₂⁻¹ ^ 2 * x ^ 2 / y₁ ^ 2 + a₂⁻¹ ^ 2 / y₂ ^ 2 + 1 / y₁ ^ 2) * h

theorem rowsq_gM : gM x y₁ y₂ θ 1 0 ^ 2 + gM x y₁ y₂ θ 1 1 ^ 2 = y₂ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [gM_one_zero, gM_one_one]
  linear_combination y₂ ^ 2 * h

theorem col_eM (ε' : ℝ) (hε' : ε' = 1 ∨ ε' = -1) :
    ((eM x y₁ y₂ θ 0 0 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((eM x y₁ y₂ θ 1 0 : ℝ) : ℂ) =
      ((y₁⁻¹ : ℝ) : ℂ) * Complex.exp (-((ε' : ℂ) * (θ : ℂ)) * Complex.I) := by
  rw [eM_zero_zero, eM_one_zero]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rcases hε' with h | h
  · subst h
    push_cast
    rw [show -((1 : ℂ) * (θ : ℂ)) * Complex.I = (-(θ : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  · subst h
    push_cast
    rw [show -((-1 : ℂ) * (θ : ℂ)) * Complex.I = (θ : ℂ) * Complex.I by ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring

theorem bracket_eM (ac : ℂ) (a₁ a₂ : ℝ) :
    -Complex.I *
        (ac * (a₁ : ℂ) * (((gM x y₁ y₂ θ 1 0 : ℝ) : ℂ) - Complex.I * ((gM x y₁ y₂ θ 1 1 : ℝ) : ℂ)) +
          ((a₂ : ℝ) : ℂ)⁻¹ * (((eM x y₁ y₂ θ 0 1 : ℝ) : ℂ) - Complex.I * ((eM x y₁ y₂ θ 1 1 : ℝ) : ℂ))) =
      Complex.exp ((θ : ℂ) * Complex.I) *
        ((-(ac * (a₁ : ℂ) * (y₂ : ℂ)) - (((a₂ * y₂)⁻¹ : ℝ) : ℂ)) + Complex.I * (((x / (a₂ * y₁) : ℝ)) : ℂ)) := by
  rw [gM_one_zero, gM_one_one, eM_zero_one, eM_one_one, Complex.exp_mul_I]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  push_cast
  linear_combination (-(Complex.cos (θ : ℂ)) * (-(ac * (a₁ : ℂ) * (y₂ : ℂ)) - ((a₂ : ℂ) * (y₂ : ℂ))⁻¹)) * hI

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.K7Rot"
end DualKit
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.K7Rot"

namespace DualB
open DualKit K7Rot

theorem of_eM (x y₁ y₂ θ : ℝ) : Matrix.of (eM x y₁ y₂ θ) = eM x y₁ y₂ θ := rfl

noncomputable def Ssgn (a₀ : ZMod 2) (y : ℝ) : ℂ := if a₀ = 0 then 1 else ((SignType.sign y : ℝ) : ℂ)

theorem quasiChar_eq (u : ℂ) (a₀ : ZMod 2) (y : ℝ) :
    ArchR.quasiChar u a₀ y = ((|y| : ℝ) : ℂ) ^ u * Ssgn a₀ y := rfl

theorem Ssgn_inv_mul (a₀ : ZMod 2) (y₁ y₂ : ℝ) (hy₂ : 0 < y₂) : Ssgn a₀ (y₁ * y₂)⁻¹ = Ssgn a₀ y₁ := by
  unfold Ssgn
  split_ifs
  · rfl
  · congr 2
    rcases lt_trichotomy y₁ 0 with h | h | h
    · rw [sign_neg h, sign_neg (inv_lt_zero.mpr (mul_neg_of_neg_of_pos h hy₂))]
    · subst h; simp
    · rw [sign_pos h, sign_pos (inv_pos.mpr (mul_pos h hy₂))]

theorem centralChar_of_pos (P₂ : RealArchParam) (y₂ : ℝ) (hy₂ : 0 < y₂) :
    ArchR.centralChar P₂ y₂ = ((y₂ : ℝ) : ℂ) ^ P₂.centralExponent := by
  unfold ArchR.centralChar ArchR.quasiChar
  rw [abs_of_pos hy₂, sign_pos hy₂]
  split_ifs <;> simp

theorem inv_ofReal_cpow {r : ℝ} (hr : 0 < r) (s : ℂ) : (((r⁻¹ : ℝ)) : ℂ) ^ s = ((r : ℝ) : ℂ) ^ (-s) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm),
    Complex.cpow_neg]

theorem expand_Y₁ (Y : ℂ) (hY : Y ≠ 0) (u : ℂ) :
    Y ^ (-(u + 3)) = Y * Y ^ (-(u + 2)) * Y ^ 2 * (Y ^ 4)⁻¹ := by
  rw [show -(u + 3) = -(u + 2) + (-1 : ℂ) by ring, Complex.cpow_add _ _ hY, Complex.cpow_neg_one]
  field_simp

theorem expand_Y₂ (Y : ℂ) (hY : Y ≠ 0) (u c : ℂ) :
    Y ^ (c - u) = Y * Y ^ (-(u + 2)) * Y ^ 2 * Y ^ c * Y * Y ^ 2 * (Y ^ 4)⁻¹ := by
  rw [show c - u = -(u + 2) + c + (2 : ℂ) by ring, Complex.cpow_add _ _ hY, Complex.cpow_add _ _ hY, Complex.cpow_two]
  field_simp

theorem pointwise
    (a : ℚ) (ha : a ≠ 0) (ha1 : a = -1)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₀ : ℂ) (a₀ : ZMod 2) (m n : ℕ) (ε' : ℝ)
    (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : 0 < a₂)
    (x y₁ y₂ θ : ℝ) (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    (∫ v : Fin 2 → ℝ,
        S (eM x y₁ y₂ θ * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
          psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1)))) *
      ArchR.quasiChar (u₀ + 2) a₀ (eM x y₁ y₂ θ).det * (((|(eM x y₁ y₂ θ).det| ^ 2)⁻¹ : ℝ) : ℂ) *
      D.W (ArchR.diagOne (a : ℝ) * (eM x y₁ y₂ θ)⁻¹) *
      ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)
    = ((a₁ ^ 2 : ℝ) : ℂ) *
        (((y₁⁻¹ : ℝ) : ℂ) ^ n * Ssgn a₀ y₁ * ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 3)) * ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - u₀) *
          (Real.exp (-(Real.pi * (x ^ 2 / (a₂ * y₁) ^ 2))) : ℂ) * ArchR.psi ((a : ℝ) * x) *
          ((((a₁ * y₂ - (a₂ * y₂)⁻¹ : ℝ) : ℂ)) + Complex.I * (((x / (a₂ * y₁) : ℝ) : ℂ))) ^ m *
          (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2))) : ℂ) *
          D.W (ArchR.diagOne ((a : ℝ) * (y₁ / y₂)))) := by
  have hε' : ε' = 1 ∨ ε' = -1 := by rcases hcol with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [h]
  have haR : ((a : ℚ) : ℝ) = -1 := by rw [ha1]; push_cast; ring
  have hdet : (Matrix.of (eM x y₁ y₂ θ)).det ≠ 0 := by
    rw [of_eM, det_eM]; exact inv_ne_zero (mul_ne_zero hy₁ hy₂.ne')
  have hD3 := LanglandsTunnell.CubicInduction.integral_dualConfig_eq_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
    a ha psiInf hpsiInf n m ε' hε' S hS (eM x y₁ y₂ θ) hdet a₁ ha₁ a₂ ha₂.ne'
  rw [of_eM] at hD3
  rw [hD3, inv_eM x y₁ y₂ θ hy₁ hy₂.ne', det_eM, gaussArg_eM, rowsq_gM,
    show ((((eM x y₁ y₂ θ 0 0 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((eM x y₁ y₂ θ 1 0 : ℝ) : ℂ)))
      = ((y₁⁻¹ : ℝ) : ℂ) * Complex.exp (-((ε' : ℂ) * (θ : ℂ)) * Complex.I) from col_eM x y₁ y₂ θ ε' hε',
    bracket_eM x y₁ y₂ θ (a : ℂ) a₁ a₂]

  have hT := LanglandsTunnell.Converse.ArchDatumR.W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_archWeightChar_mul_W_diagOne
    D k₀ hDW (c := (a : ℝ)) (by rw [haR]; norm_num) x hy₁ hy₂ θ (rotK θ) (coe_rotK θ)
  rw [show gM x y₁ y₂ θ = !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
      y₂ * Real.sin θ, y₂ * Real.cos θ] from rfl, hT, archWeightCharℝ_rotK, centralChar_of_pos P₂ y₂ hy₂,
    quasiChar_eq, Ssgn_inv_mul a₀ y₁ y₂ hy₂]

  have hph := phase_eq_one m n k₀ ε' θ hcol

  have hy₁a : 0 < |y₁| := abs_pos.mpr hy₁
  have hY₁0 : ((|y₁| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy₁a.ne'
  have hY₂0 : ((y₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy₂.ne'
  have haC : ((a : ℚ) : ℂ) = -1 := by rw [ha1]; push_cast; ring
  rw [mul_pow (((y₁⁻¹ : ℝ) : ℂ)), mul_pow (Complex.exp ((θ : ℂ) * Complex.I))]
  rw [show ((|(y₁ * y₂)⁻¹| : ℝ) : ℂ) ^ (u₀ + 2) = ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (-(u₀ + 2)) by
    rw [abs_inv, abs_mul, abs_of_pos hy₂, mul_inv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (inv_nonneg.mpr hy₁a.le) (inv_nonneg.mpr hy₂.le), inv_ofReal_cpow hy₁a, inv_ofReal_cpow hy₂]]
  rw [show Real.exp (-(Real.pi * (x ^ 2 / (a₂ * y₁) ^ 2 + (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹))))
      = Real.exp (-(Real.pi * (x ^ 2 / (a₂ * y₁) ^ 2))) * Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹))) by
    rw [← Real.exp_add]; congr 1; ring,
    show Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2)))
      = Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹))) * Real.exp (-(Real.pi * (a₁ ^ 2 * y₂ ^ 2))) by
    rw [← Real.exp_add]; congr 1; ring,
    show Real.exp (-(Real.pi * (a : ℝ) ^ 2 * a₁ ^ 2 * y₂ ^ 2)) = Real.exp (-(Real.pi * (a₁ ^ 2 * y₂ ^ 2))) by
    rw [haR]; congr 1; ring]
  rw [abs_inv, abs_mul, abs_of_pos hy₂, inv_inv, inv_pow, inv_inv, haR, haC, show (-1 : ℝ) * y₁ / y₂ = -1 * (y₁ / y₂) by ring,
    expand_Y₁ _ hY₁0, expand_Y₂ _ hY₂0]
  push_cast
  refine (Eq.trans ?_ (congrArg (HMul.hMul _) hph)).trans (mul_one _)
  ring

end DualB
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.K7Rot"

open scoped Classical in
theorem DualBody.stepA
    (a : ℚ)
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
        {P₂ : RealArchParam} (D : ArchDatumR P₂) (u₀ : ℂ) (a₀ : ZMod 2)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (par₀ : ZMod 2) (s : ℂ)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : 0 < a₂) :
    (let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂.ne'
     (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) *
        dualWhittakerFn3 (jacquetVector3 D u₀ a₀ (a : ℝ) psiInf S)
          (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) *
        (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) * (((a₁ ^ 2)⁻¹ : ℝ) : ℂ))
      = ((|a₁ * a₂| : ℝ) : ℂ) *
          (Complex.I ^ (kw par₀ default) *
            ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) *
            Wr par₀ default (-a₁ / a₂)) *
          (ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) *
            ∫ e : Fin 2 → Fin 2 → ℝ,
              (∫ v : Fin 2 → ℝ,
                  S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
                    psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1)))) *
                ArchR.quasiChar (u₀ + 2) a₀ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)) *
          ((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2) * (((a₁ ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hdet : (Matrix.GeneralLinearGroup.det (AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha₁ ha₂.ne') : ℝ) = a₁ * a₂ := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    show (!![a₁, 0; 0, a₂] : Matrix (Fin 2) (Fin 2) ℝ).det = a₁ * a₂
    rw [Matrix.det_fin_two_of]; ring
  simp only []
  rw [hdet, dualWhittakerFn3_apply,
    LanglandsTunnell.CubicInduction.jacquetVector3_longWeyl3_transposeInv3_iota_upperUnit_eq D u₀ a₀ (a : ℝ) psiInf S a₁ ha₁ a₂ ha₂,
    LanglandsTunnell.RankinSelberg.archWhittaker_w0R_mul_transposeInv_upperUnit_eq_mul_archProfile
      a P _hP₁ kw Wr WA hkw1 hkw2 hWr1 hWr2 hWr3 hWr4 hWAN hWAZ hWAK hWAt hWAc w₀R hw₀R par₀ a₁ ha₁ a₂ ha₂]

namespace K7D
section
open Complex

theorem add_pow_le_two_pow (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (j : ℕ) :
    (A + B) ^ j ≤ 2 ^ j * (A ^ j + B ^ j) := by
  rcases le_total A B with h | h
  · calc (A + B) ^ j ≤ (2 * B) ^ j := by gcongr; linarith
      _ = 2 ^ j * B ^ j := mul_pow _ _ _
      _ ≤ 2 ^ j * (A ^ j + B ^ j) := by gcongr; have := pow_nonneg hA j; linarith
  · calc (A + B) ^ j ≤ (2 * A) ^ j := by gcongr; linarith
      _ = 2 ^ j * A ^ j := mul_pow _ _ _
      _ ≤ 2 ^ j * (A ^ j + B ^ j) := by gcongr; have := pow_nonneg hB j; linarith

theorem integrable_abs_pow_mul_gauss (j : ℕ) :
    Integrable (fun x : ℝ => |x| ^ j * Real.exp (-(Real.pi * x ^ 2))) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := (j : ℝ))
    (by have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have h' : Integrable (fun x : ℝ => x ^ j * Real.exp (-(Real.pi * x ^ 2))) := by
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.rpow_natCast, neg_mul]
  refine (h'.norm).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem integrable_pow_gauss_cexp (j : ℕ) (ξ : ℝ) :
    Integrable (fun x : ℝ => ((x : ℝ) : ℂ) ^ j * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))) := by
  refine (integrable_abs_pow_mul_gauss j).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ) * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero, mul_one]

theorem integrable_sub_I_mul_pow_gauss (j : ℕ) (σ : ℝ) :
    Integrable (fun z : ℝ => ((σ : ℂ) - Complex.I * (z : ℂ)) ^ j * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by
  have hmaj : Integrable (fun z : ℝ => (2 : ℝ) ^ j * (|σ| ^ j * Real.exp (-(Real.pi * z ^ 2)) +
      |z| ^ j * Real.exp (-(Real.pi * z ^ 2)))) := by
    refine Integrable.const_mul (Integrable.add ?_ (integrable_abs_pow_mul_gauss j)) _
    have := integrable_exp_neg_mul_sq Real.pi_pos
    refine (this.const_mul (|σ| ^ j)).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [neg_mul]
  refine hmaj.mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  rw [norm_mul, norm_pow, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : ‖(σ : ℂ) - Complex.I * (z : ℂ)‖ ≤ |σ| + |z| := by
    calc ‖(σ : ℂ) - Complex.I * (z : ℂ)‖ ≤ ‖(σ : ℂ)‖ + ‖Complex.I * (z : ℂ)‖ := norm_sub_le _ _
      _ = |σ| + |z| := by rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
  have he : 0 ≤ Real.exp (-(Real.pi * z ^ 2)) := (Real.exp_pos _).le
  calc ‖(σ : ℂ) - Complex.I * (z : ℂ)‖ ^ j * Real.exp (-(Real.pi * z ^ 2))
      ≤ (|σ| + |z|) ^ j * Real.exp (-(Real.pi * z ^ 2)) := by gcongr
    _ ≤ (2 ^ j * (|σ| ^ j + |z| ^ j)) * Real.exp (-(Real.pi * z ^ 2)) := by
        gcongr; exact add_pow_le_two_pow _ _ (abs_nonneg _) (abs_nonneg _) j
    _ = _ := by ring

theorem integral_add_I_mul_pow_mul_gauss_mul_cexp (m : ℕ) (c : ℂ) (ξ : ℝ) :
    ∫ x : ℝ, (c + Complex.I * (x : ℂ)) ^ m * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) *
        ∫ z : ℝ, (c - (ξ : ℂ) + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) := by
  have hL : ∀ x : ℝ, (c + Complex.I * (x : ℂ)) ^ m * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ)) =
      ∑ k ∈ Finset.range (m + 1), (c ^ k * Complex.I ^ (m - k) * (m.choose k : ℂ)) *
        (((x : ℝ) : ℂ) ^ (m - k) * (Real.exp (-(Real.pi * x ^ 2)) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (x : ℂ))) := by
    intro x
    rw [add_pow, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]; ring
  have hR : ∀ z : ℝ, (c - (ξ : ℂ) + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) =
      ∑ k ∈ Finset.range (m + 1), (c ^ k * (-1) ^ (m - k) * (m.choose k : ℂ)) *
        (((ξ : ℂ) - Complex.I * (z : ℂ)) ^ (m - k) * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by
    intro z
    rw [show c - (ξ : ℂ) + Complex.I * (z : ℂ) = c + -((ξ : ℂ) - Complex.I * (z : ℂ)) by ring, add_pow,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [neg_pow]; ring
  simp_rw [hL, hR]
  rw [integral_finsetSum _ (fun k _ => (integrable_pow_gauss_cexp (m - k) ξ).const_mul _),
    integral_finsetSum _ (fun k _ => (integrable_sub_I_mul_pow_gauss (m - k) ξ).const_mul _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_const_mul,
    LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv (m - k) ξ]
  conv_rhs => rw [mul_left_comm,
    LanglandsTunnell.exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv (m - k) ξ]
  generalize iteratedDeriv (m - k) (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) ξ = D
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have key : Complex.I ^ (m - k) * (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ^ (m - k) =
      (-1 : ℂ) ^ (m - k) * (-(2 * (Real.pi : ℂ)))⁻¹ ^ (m - k) := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    field_simp
  linear_combination (c ^ k * (m.choose k : ℂ) * D) * key

end
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.K7Rot"

theorem cpow_ofReal_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
    (((a * b : ℝ) : ℂ)) ^ r = ((a : ℝ) : ℂ) ^ r * ((b : ℝ) : ℂ) ^ r := by
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg ha hb r

theorem cpow_ofReal_inv {a : ℝ} (ha : 0 < a) (r : ℂ) :
    (((a⁻¹ : ℝ) : ℂ)) ^ r = ((a : ℝ) : ℂ) ^ (-r) := by
  rw [Complex.cpow_neg, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg ha.le]; exact Real.pi_ne_zero.symm)]

theorem cpow_combine41 (A : ℂ) (hA : A ≠ 0) (a b c d : ℂ) :
    A ^ a * A ^ b * A ^ c * A ^ d * A = A ^ (a + b + c + d + 1) := by
  rw [Complex.cpow_add _ _ hA, Complex.cpow_add _ _ hA, Complex.cpow_add _ _ hA, Complex.cpow_add _ _ hA,
    Complex.cpow_one]

theorem cpow_combine32 (A : ℂ) (hA : A ≠ 0) (a b c : ℂ) :
    A ^ a * A ^ b * A ^ c * A * A = A ^ (a + b + c + 1 + 1) := by
  rw [Complex.cpow_add _ _ hA, Complex.cpow_add _ _ hA, Complex.cpow_add _ _ hA, Complex.cpow_add _ _ hA,
    Complex.cpow_one]

theorem xstep_dual (m : ℕ) (c₀ L ξ : ℝ) (hL : L ≠ 0) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / L ^ 2))) : ℂ) * ArchR.psi (ξ * x) *
        ((((c₀ : ℝ) : ℂ)) + Complex.I * (((x / L : ℝ) : ℂ))) ^ m =
      ((|L| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (ξ * L) ^ 2)) : ℂ) *
        ∫ z : ℝ, (((c₀ - ξ * L : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) := by
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  set g : ℝ → ℂ := fun z => (((c₀ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m * (Real.exp (-(Real.pi * z ^ 2)) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((ξ * L : ℝ) : ℂ) * (z : ℂ)) with hg
  have hsub : ∀ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / L ^ 2))) : ℂ) * ArchR.psi (ξ * x) *
        ((((c₀ : ℝ) : ℂ)) + Complex.I * (((x / L : ℝ) : ℂ))) ^ m = g (L⁻¹ * x) := by
    intro x
    simp only [hg, ArchR.psi]
    have e1 : (((x / L : ℝ)) : ℂ) = (((L⁻¹ * x : ℝ)) : ℂ) := by push_cast; ring
    have e2 : Real.exp (-(Real.pi * (x ^ 2 / L ^ 2))) = Real.exp (-(Real.pi * (L⁻¹ * x) ^ 2)) := by
      congr 1; field_simp
    have e3 : (2 * (Real.pi : ℂ) * Complex.I * ((ξ * x : ℝ) : ℂ)) =
        2 * Real.pi * Complex.I * ((ξ * L : ℝ) : ℂ) * (((L⁻¹ * x : ℝ)) : ℂ) := by
      push_cast; field_simp
    rw [e1, e2, e3]; ring
  simp_rw [hsub]
  rw [Measure.integral_comp_mul_left g, inv_inv, Complex.real_smul, hg,
    integral_add_I_mul_pow_mul_gauss_mul_cexp m ((c₀ : ℝ) : ℂ) (ξ * L)]
  have : ((c₀ : ℝ) : ℂ) - ((ξ * L : ℝ) : ℂ) = ((c₀ - ξ * L : ℝ) : ℂ) := by push_cast; ring
  rw [this]; ring

theorem measurable_sgnChar (a₀ : ZMod 2) :
    Measurable (fun y : ℝ => if a₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ)) := by
  by_cases h : a₀ = 0
  · simp only [h, if_true]; exact measurable_const
  · simp only [h, if_false]
    have hf : (fun y : ℝ => ((SignType.sign y : ℝ) : ℂ)) =
        fun y => if 0 < y then (1 : ℂ) else if y < 0 then (-1 : ℂ) else 0 := by
      ext y
      rcases lt_trichotomy y 0 with hy | hy | hy
      · rw [sign_neg hy, if_neg (not_lt.mpr hy.le), if_pos hy]; push_cast; simp
      · subst hy; simp
      · rw [sign_pos hy, if_pos hy]; push_cast; simp
    rw [hf]
    refine Measurable.ite measurableSet_Ioi measurable_const (Measurable.ite measurableSet_Iio measurable_const measurable_const)

theorem norm_sgnChar_le (a₀ : ZMod 2) (y : ℝ) :
    ‖(if a₀ = 0 then (1 : ℂ) else ((SignType.sign y : ℝ) : ℂ))‖ ≤ 1 := by
  split_ifs
  · simp
  · rcases lt_trichotomy y 0 with hy | hy | hy
    · rw [sign_neg hy]; push_cast; simp
    · subst hy; simp
    · rw [sign_pos hy]; push_cast; simp

theorem ycollect (P₂ : RealArchParam) (u₀ : ℂ) (m n : ℕ)
    (a₁ a₂ y₁ y₂ : ℝ) (ha₂ : 0 < a₂) (hy₁ : y₁ ≠ 0) (ξ : ℝ) (hξ : ξ = -1)
    (Ssgn : ℂ) (Dw : ℂ) :
    ((a₁ ^ 2 : ℝ) : ℂ) *
        (((y₁⁻¹ : ℝ) : ℂ) ^ n * Ssgn * ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 3)) * ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - u₀) *
          (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2))) : ℂ) * Dw) *
        (((|a₂ * y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (ξ * (a₂ * y₁)) ^ 2)) : ℂ) *
          ∫ z : ℝ, (((a₁ * y₂ - (a₂ * y₂)⁻¹ - ξ * (a₂ * y₁) : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
            (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      = ((a₁ ^ 2 * a₂ : ℝ) : ℂ) *
        (((y₁⁻¹ : ℝ) : ℂ) ^ n * Ssgn *
          ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - u₀) *
          (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2 + a₂ ^ 2 * y₁ ^ 2))) : ℂ) *
          Dw *
          (∫ z : ℝ, (((a₁ * y₂ - (a₂ * y₂)⁻¹ + a₂ * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
            (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) := by
  subst hξ
  have hA0 : ((|y₁| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hy₁)
  have habs : ((|a₂ * y₁| : ℝ) : ℂ) = ((a₂ : ℝ) : ℂ) * ((|y₁| : ℝ) : ℂ) := by
    rw [abs_mul, abs_of_pos ha₂]; push_cast; ring
  have hpow : ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 3)) * ((|y₁| : ℝ) : ℂ) = ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) := by
    rw [show -(u₀ + 2) = -(u₀ + 3) + 1 by ring, Complex.cpow_add _ _ hA0, Complex.cpow_one]
  have hbr : (a₁ * y₂ - (a₂ * y₂)⁻¹ - (-1 : ℝ) * (a₂ * y₁) : ℝ) = a₁ * y₂ - (a₂ * y₂)⁻¹ + a₂ * y₁ := by ring
  have hE : ((Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2))) : ℝ) : ℂ) *
      ((Real.exp (-(Real.pi * ((-1 : ℝ) * (a₂ * y₁)) ^ 2)) : ℝ) : ℂ) =
      ((Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2 + a₂ ^ 2 * y₁ ^ 2))) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 1; ring
  rw [hbr, habs, ← hpow, ← hE]
  push_cast
  ring

theorem acollect (P : RealArchParam) (uP : ℂ) (nP m : ℕ) (hm : m = nP + 1) (kw : ℤ) (hkw : kw = (nP : ℤ) + 1)
    (Wr : ℂ → ℂ)
    (hWpos : ∀ t : ℝ, 0 < t → Wr t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (u₀ : ℂ) (a₀ : ZMod 2) (s : ℂ) (a₁ a₂ : ℝ) (ha₁ : a₁ < 0) (ha₂ : 0 < a₂) (X : ℂ) :
    ((|a₁ * a₂| : ℝ) : ℂ) *
          (Complex.I ^ kw *
            ((((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ) ^ (P.centralExponent + 1)) *
              ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) ^ (P.centralSign.val : ℤ)) *
            Wr (-a₁ / a₂)) *
          (ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) *
            (((2 * Real.pi : ℝ) : ℂ) * (((a₁ ^ 2 * a₂ : ℝ) : ℂ) * X))) *
          ((|a₁ * a₂| : ℝ) : ℂ) ^ (s - 1 / 2) * (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
      = 4 * (Real.pi : ℂ) * Complex.I ^ m *
        (((|a₁| : ℝ) : ℂ) ^ (s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - u₀ - 3 / 2) *
          ((a₂ : ℝ) : ℂ) ^ (s - (uP + (nP : ℂ) / 2 + 1) - u₀ + 1 / 2) *
          (Real.exp (-(2 * Real.pi * (|a₁| / a₂))) : ℂ) * X) := by

  have ha₁' : 0 < |a₁| := abs_pos.mpr ha₁.ne
  have hA0 : ((|a₁| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha₁'.ne'
  have hB0 : ((a₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha₂.ne'
  have hneg : |a₁| = -a₁ := abs_of_neg ha₁
  have h1 : (|a₁ * a₂| : ℝ) = |a₁| * a₂ := by rw [abs_mul, abs_of_pos ha₂]
  have h2 : (|(-a₁⁻¹ : ℝ)| : ℝ) = |a₁|⁻¹ := by rw [abs_neg, abs_inv]
  have h3p : 0 < (-a₁⁻¹ : ℝ) := by rw [neg_pos]; exact inv_lt_zero.mpr ha₁
  have h3 : ((((-a₁⁻¹ : ℝ)) : ℂ) / ((|(-a₁⁻¹ : ℝ)| : ℝ) : ℂ)) = 1 := by
    rw [abs_of_pos h3p, div_self (Complex.ofReal_ne_zero.mpr h3p.ne')]
  have h4 : (-a₁ / a₂ : ℝ) = |a₁| * a₂⁻¹ := by rw [hneg]; ring
  have h4p : 0 < (-a₁ / a₂ : ℝ) := div_pos (neg_pos.mpr ha₁) ha₂
  have h5 : (-(a₁ * a₂)⁻¹ : ℝ) = |a₁|⁻¹ * a₂⁻¹ := by rw [hneg]; field_simp
  have h5p : 0 < (-(a₁ * a₂)⁻¹ : ℝ) := by rw [h5]; positivity
  have h6 : (a₁ ^ 2 : ℝ) = |a₁| ^ 2 := (sq_abs a₁).symm

  have eW : Wr (-a₁ / a₂) = Wr (((-a₁ / a₂ : ℝ)) : ℂ) := by congr 1; push_cast; ring
  rw [eW, hWpos _ h4p, h3, one_zpow, mul_one, h2, h4, h1]

  have hq : ArchR.quasiChar (u₀ + 1) a₀ (-(a₁ * a₂)⁻¹) =
      ((|a₁| : ℝ) : ℂ) ^ (-(u₀ + 1)) * ((a₂ : ℝ) : ℂ) ^ (-(u₀ + 1)) := by
    unfold ArchR.quasiChar
    rw [abs_of_pos h5p, sign_pos h5p, h5, cpow_ofReal_mul (inv_nonneg.mpr ha₁'.le) (inv_nonneg.mpr ha₂.le),
      cpow_ofReal_inv ha₁', cpow_ofReal_inv ha₂]
    split_ifs <;> simp
  rw [hq]

  have hQ : (((|a₁| * a₂⁻¹ : ℝ)) : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) =
      ((|a₁| : ℝ) : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * ((a₂ : ℝ) : ℂ) ^ (-(uP + (nP : ℂ) / 2 + 1)) := by
    rw [cpow_ofReal_mul ha₁'.le (inv_nonneg.mpr ha₂.le), cpow_ofReal_inv ha₂]
  have hC : (((|a₁|⁻¹ : ℝ)) : ℂ) ^ (P.centralExponent + 1) = ((|a₁| : ℝ) : ℂ) ^ (-(P.centralExponent + 1)) :=
    cpow_ofReal_inv ha₁' _
  have hS : (((|a₁| * a₂ : ℝ)) : ℂ) ^ (s - 1 / 2) = ((|a₁| : ℝ) : ℂ) ^ (s - 1 / 2) * ((a₂ : ℝ) : ℂ) ^ (s - 1 / 2) := by
    exact cpow_ofReal_mul ha₁'.le ha₂.le _
  rw [hQ, hC, hS, h6, hkw, show ((nP : ℤ) + 1 : ℤ) = ((nP + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, ← hm,
    show (-(2 * Real.pi * (|a₁| * a₂⁻¹)) : ℝ) = -(2 * Real.pi * (|a₁| / a₂)) by rw [div_eq_mul_inv]]

  have hA1 : ((|a₁| : ℝ) : ℂ) ^ (-(P.centralExponent + 1)) * ((|a₁| : ℝ) : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) *
      ((|a₁| : ℝ) : ℂ) ^ (-(u₀ + 1)) * ((|a₁| : ℝ) : ℂ) ^ (s - 1 / 2) * ((|a₁| : ℝ) : ℂ) =
      ((|a₁| : ℝ) : ℂ) ^ (s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - u₀ - 3 / 2) := by
    rw [cpow_combine41 _ hA0]; congr 1; ring
  have hA2 : ((a₂ : ℝ) : ℂ) ^ (-(uP + (nP : ℂ) / 2 + 1)) * ((a₂ : ℝ) : ℂ) ^ (-(u₀ + 1)) *
      ((a₂ : ℝ) : ℂ) ^ (s - 1 / 2) * ((a₂ : ℝ) : ℂ) * ((a₂ : ℝ) : ℂ) =
      ((a₂ : ℝ) : ℂ) ^ (s - (uP + (nP : ℂ) / 2 + 1) - u₀ + 1 / 2) := by
    rw [cpow_combine32 _ hB0]; congr 1; ring
  have hJ : ((|a₁| : ℝ) : ℂ) ^ 2 * (((|a₁| : ℝ) : ℂ) ^ 2)⁻¹ = 1 := by field_simp
  rw [← hA1, ← hA2]
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_ofNat]
  linear_combination (4 * (Real.pi : ℂ) * Complex.I ^ m *
    ((((|a₁| : ℝ) : ℂ) ^ (-(P.centralExponent + 1)) * ((|a₁| : ℝ) : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) *
      ((|a₁| : ℝ) : ℂ) ^ (-(u₀ + 1)) * ((|a₁| : ℝ) : ℂ) ^ (s - 1 / 2) * ((|a₁| : ℝ) : ℂ)) *
     (((a₂ : ℝ) : ℂ) ^ (-(uP + (nP : ℂ) / 2 + 1)) * ((a₂ : ℝ) : ℂ) ^ (-(u₀ + 1)) *
      ((a₂ : ℝ) : ℂ) ^ (s - 1 / 2) * ((a₂ : ℝ) : ℂ) * ((a₂ : ℝ) : ℂ)) *
     (Real.exp (-(2 * Real.pi * (|a₁| / a₂))) : ℂ) * X)) * hJ

end K7D
p2m_reactivate "P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3.K7Rot"

theorem DMain_xInt {P₂ : RealArchParam} (D : ArchDatumR P₂) (a : ℚ) (haR : ((a : ℚ) : ℝ) = -1)
    (u₀ : ℂ) (a₀ : ZMod 2) (m n : ℕ) (a₁ a₂ : ℝ) (ha₂ : 0 < a₂) (y₁ : ℝ) (hy₁ : y₁ ≠ 0) (y₂ : ℝ) :
    (∫ x : ℝ, ((a₁ ^ 2 : ℝ) : ℂ) *
        (((y₁⁻¹ : ℝ) : ℂ) ^ n * DualB.Ssgn (a₀) y₁ * ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 3)) *
          ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - u₀) *
          (Real.exp (-(Real.pi * (x ^ 2 / (a₂ * y₁) ^ 2))) : ℂ) * ArchR.psi ((a : ℝ) * x) *
          ((((a₁ * y₂ - (a₂ * y₂)⁻¹ : ℝ) : ℂ)) + Complex.I * (((x / (a₂ * y₁) : ℝ) : ℂ))) ^ m *
          (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2))) : ℂ) *
          D.W (ArchR.diagOne ((a : ℝ) * (y₁ / y₂))))) =
      ((a₁ ^ 2 * a₂ : ℝ) : ℂ) *
        (((y₁⁻¹ : ℝ) : ℂ) ^ n * DualB.Ssgn (a₀) y₁ *
          ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - u₀) *
          (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2 + a₂ ^ 2 * y₁ ^ 2))) : ℂ) *
          D.W (ArchR.diagOne ((a : ℝ) * (y₁ / y₂))) *
          (∫ z : ℝ, (((a₁ * y₂ - (a₂ * y₂)⁻¹ + a₂ * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
            (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) := by
  have hre : ∀ x : ℝ, ((a₁ ^ 2 : ℝ) : ℂ) *
        (((y₁⁻¹ : ℝ) : ℂ) ^ n * DualB.Ssgn (a₀) y₁ * ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 3)) *
          ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - u₀) *
          (Real.exp (-(Real.pi * (x ^ 2 / (a₂ * y₁) ^ 2))) : ℂ) * ArchR.psi ((a : ℝ) * x) *
          ((((a₁ * y₂ - (a₂ * y₂)⁻¹ : ℝ) : ℂ)) + Complex.I * (((x / (a₂ * y₁) : ℝ) : ℂ))) ^ m *
          (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2))) : ℂ) *
          D.W (ArchR.diagOne ((a : ℝ) * (y₁ / y₂)))) =
        (((a₁ ^ 2 : ℝ) : ℂ) *
          (((y₁⁻¹ : ℝ) : ℂ) ^ n * DualB.Ssgn a₀ y₁ * ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 3)) *
            ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - u₀) *
            (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2))) : ℂ) *
            D.W (ArchR.diagOne ((a : ℝ) * (y₁ / y₂))))) *
        ((Real.exp (-(Real.pi * (x ^ 2 / (a₂ * y₁) ^ 2))) : ℂ) * ArchR.psi ((a : ℝ) * x) *
          ((((a₁ * y₂ - (a₂ * y₂)⁻¹ : ℝ) : ℂ)) + Complex.I * (((x / (a₂ * y₁) : ℝ) : ℂ))) ^ m) := by
    intro x; ring
  simp_rw [hre]
  rw [integral_const_mul, K7D.xstep_dual m (a₁ * y₂ - (a₂ * y₂)⁻¹) (a₂ * y₁) (a : ℝ) (mul_ne_zero ha₂.ne' hy₁)]
  exact K7D.ycollect P₂ u₀ m n a₁ a₂ y₁ y₂ ha₂ hy₁ (a : ℝ) haR _ _

open scoped Classical in
theorem DMain_eInt (a : ℚ) (ha : a ≠ 0) (ha1 : a = -1)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₀ : ℂ) (a₀ : ZMod 2) (m n : ℕ) (ε' : ℝ)
    (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (a₁ : ℝ) (ha₁ : a₁ ≠ 0) (a₂ : ℝ) (ha₂ : 0 < a₂) :
    (∫ e : Fin 2 → Fin 2 → ℝ,
          (∫ v : Fin 2 → ℝ,
              S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
                psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1)))) *
            ArchR.quasiChar (u₀ + 2) (a₀) (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
            D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹)) =
      ((2 * Real.pi : ℝ) : ℂ) * (((a₁ ^ 2 * a₂ : ℝ) : ℂ) *
        ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ),
          ((y₁⁻¹ : ℝ) : ℂ) ^ n * DualB.Ssgn (a₀) y₁ *
            ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - u₀) *
            (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2 + a₂ ^ 2 * y₁ ^ 2))) : ℂ) *
            D.W (ArchR.diagOne ((a : ℝ) * (y₁ / y₂))) *
            (∫ z : ℝ, (((a₁ * y₂ - (a₂ * y₂)⁻¹ + a₂ * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) := by
  have haR : ((a : ℚ) : ℝ) = -1 := by rw [ha1]; push_cast; ring
  have ha0R : ((a : ℚ) : ℝ) ≠ 0 := by rw [haR]; norm_num
  have hSm : Measurable (DualB.Ssgn a₀) := K7D.measurable_sgnChar _
  have hSb : ∀ y : ℝ, ‖DualB.Ssgn a₀ y‖ ≤ 1 := K7D.norm_sgnChar_le _
  have hae : ∀ᵐ y₁ : ℝ ∂volume, y₁ ≠ 0 := by rw [ae_iff]; simp
  rw [(LanglandsTunnell.RankinSelberg.integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional _).2]
  have hT : (∫ p : ℝ × ℝ × ℝ × ℝ in Set.univ ×ˢ (Set.univ ×ˢ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioc (0 : ℝ) (2 * Real.pi))),
      (fun e : Fin 2 → Fin 2 → ℝ =>
        (∫ v : Fin 2 → ℝ,
              S (Matrix.of e * !![v 0 / a₁, 0, 1; v 1 / a₁, a₂⁻¹, 0]) *
                psiInf (AutomorphicForm.StandardKernel.ofReal (-(v 1)))) *
            ArchR.quasiChar (u₀ + 2) (a₀) (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
            D.W (ArchR.diagOne (a : ℝ) * (Matrix.of e)⁻¹))
        (fun i j => (!![Real.cos p.2.2.2 / p.2.1, -(p.1 * Real.cos p.2.2.2) / p.2.1 + Real.sin p.2.2.2 / p.2.2.1;
                          -(Real.sin p.2.2.2) / p.2.1, p.1 * Real.sin p.2.2.2 / p.2.1 + Real.cos p.2.2.2 / p.2.2.1] : Matrix (Fin 2) (Fin 2) ℝ) i j) *
        ((p.2.2.1 ^ 2 * (|p.2.1 * p.2.2.1| ^ 4)⁻¹ : ℝ) : ℂ)) =
      ((2 * Real.pi : ℝ) : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
        ((a₁ ^ 2 : ℝ) : ℂ) *
        (((y₁⁻¹ : ℝ) : ℂ) ^ n * DualB.Ssgn (a₀) y₁ * ((|y₁| : ℝ) : ℂ) ^ (-(u₀ + 3)) *
          ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - u₀) *
          (Real.exp (-(Real.pi * (x ^ 2 / (a₂ * y₁) ^ 2))) : ℂ) * ArchR.psi ((a : ℝ) * x) *
          ((((a₁ * y₂ - (a₂ * y₂)⁻¹ : ℝ) : ℂ)) + Complex.I * (((x / (a₂ * y₁) : ℝ) : ℂ))) ^ m *
          (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2))) : ℂ) *
          D.W (ArchR.diagOne ((a : ℝ) * (y₁ / y₂)))) :=
    MeasureTheory.setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free _ _
      (fun x y₁ y₂ θ hy₁ hy₂ =>
        DualB.pointwise a ha ha1 psiInf hpsiInf D k₀ hDW u₀ a₀ m n ε' hcol S hS a₁ ha₁ a₂ ha₂ x y₁ y₂ θ hy₁ hy₂)
      ((LanglandsTunnell.Converse.integrable_dualThetaFree_integrand D (a : ℝ) ha0R (-(u₀ + 3))
        (P₂.centralExponent - u₀) m n (DualB.Ssgn a₀) hSm 1 hSb a₁ ha₁ a₂ ha₂).const_mul
          (((a₁ ^ 2 : ℝ) : ℂ)))
  rw [hT]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with y₁ hy₁
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y₂ hy₂ => ?_)
  exact DMain_xInt D a haR u₀ a₀ m n a₁ a₂ ha₂ y₁ hy₁ y₂

open scoped Classical in
theorem DMain_key
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
    (uP : ℂ) (nP : ℕ) (hnP : 1 ≤ nP) (hPdisc : P = RealArchParam.discrete uP nP hnP)
    (m : ℕ) (hm : m = nP + 1)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (hWpos : ∀ t : ℝ, 0 < t → Wr par₀ default t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → Wr par₀ default t = 0)
    (s : ℂ) (a₂ : ℝ) (ha₂ : a₂ ∈ Set.Ioi (0 : ℝ)) :
      (∫ a₁ : ℝ,
        if ha : a₁ ≠ 0 ∧ 0 < a₂ then
          let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
          (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
            (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
        else 0) =
      ∫ a₁ in Set.Iio (0 : ℝ), 4 * (Real.pi : ℂ) * Complex.I ^ m *
        (((|a₁| : ℝ) : ℂ) ^ (s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) *
          ((a₂ : ℝ) : ℂ) ^ (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) *
          (Real.exp (-(2 * Real.pi * (|a₁| / a₂))) : ℂ) *
          ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ),
          ((y₁⁻¹ : ℝ) : ℂ) ^ n * DualB.Ssgn (aR w₀ h₀) y₁ *
            ((|y₁| : ℝ) : ℂ) ^ (-(uR w₀ h₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - uR w₀ h₀) *
            (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2 + a₂ ^ 2 * y₁ ^ 2))) : ℂ) *
            D.W (ArchR.diagOne ((a : ℝ) * (y₁ / y₂))) *
            (∫ z : ℝ, (((a₁ * y₂ - (a₂ * y₂)⁻¹ + a₂ * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
              (Real.exp (-(Real.pi * z ^ 2)) : ℂ))) := by
  have ha₂' : 0 < a₂ := ha₂
  have hkw : kw par₀ default = (nP : ℤ) + 1 := hkw2 par₀ default (IsTotallyReal.isReal _) uP nP hnP hPdisc
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Iio (0 : ℝ))]
  · refine setIntegral_congr_fun measurableSet_Iio (fun a₁ ha₁ => ?_)
    have ha₁' : a₁ < 0 := ha₁
    have hh : a₁ ≠ 0 ∧ 0 < a₂ := ⟨ne_of_lt ha₁', ha₂'⟩
    rw [dif_pos hh,
      DualBody.stepA a P _hP₁ kw Wr WA hkw1 hkw2 hWr1 hWr2 hWr3 hWr4 hWAN hWAZ hWAK hWAt hWAc w₀R hw₀R D
        (uR w₀ h₀) (aR w₀ h₀) psiInf S par₀ s a₁ hh.1 a₂ hh.2,
      DMain_eInt a ha ha1 psiInf hpsiInf D k₀ hDW (uR w₀ h₀) (aR w₀ h₀) m n ε' hcol S hS a₁ hh.1 a₂ ha₂']
    exact K7D.acollect P uP nP m hm (kw par₀ default) hkw (Wr par₀ default) hWpos (uR w₀ h₀) (aR w₀ h₀)
      s a₁ a₂ ha₁' ha₂' _
  · intro a₁ ha₁
    by_cases h0 : a₁ = 0
    · subst h0; simp
    · have hpos : 0 < a₁ := lt_of_le_of_ne (not_lt.mp ha₁) (Ne.symm h0)
      have hh : a₁ ≠ 0 ∧ 0 < a₂ := ⟨h0, ha₂'⟩
      have hW0 : Wr par₀ default (-a₁ / a₂) = 0 := by
        have eW : Wr par₀ default (-a₁ / a₂) = Wr par₀ default (((-a₁ / a₂ : ℝ)) : ℂ) := by
          congr 1; push_cast; ring
        rw [eW]; exact hWneg (-a₁ / a₂) (div_neg_of_neg_of_pos (neg_neg_of_pos hpos) ha₂')
      rw [dif_pos hh,
        DualBody.stepA a P _hP₁ kw Wr WA hkw1 hkw2 hWr1 hWr2 hWr3 hWr4 hWAN hWAZ hWAK hWAt hWAc w₀R hw₀R D
          (uR w₀ h₀) (aR w₀ h₀) psiInf S par₀ s a₁ hh.1 a₂ hh.2, hW0]
      ring

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
    (uP : ℂ) (nP : ℕ) (hnP : 1 ≤ nP) (hPdisc : P = RealArchParam.discrete uP nP hnP)
    (m : ℕ) (hm : m = nP + 1)
    (n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = k₀ - m) ∨ (ε' = 1 ∧ (n : ℤ) = m - k₀))
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (hWpos : ∀ t : ℝ, 0 < t → Wr par₀ default t = (2 : ℂ) * (t : ℂ) ^ (uP + (nP : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * t)) : ℂ))
    (hWneg : ∀ t : ℝ, t < 0 → Wr par₀ default t = 0) :
    ∀ s : ℂ,
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = 4 * (Real.pi : ℂ) * Complex.I ^ m *
              ∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ in Set.Iio (0 : ℝ),
                ((|a₁| : ℝ) : ℂ) ^ (s + (uP + (nP : ℂ) / 2 + 1) - P.centralExponent - uR w₀ h₀ - 3 / 2) *
                  ((a₂ : ℝ) : ℂ) ^ (s - (uP + (nP : ℂ) / 2 + 1) - uR w₀ h₀ + 1 / 2) *
                  (Real.exp (-(2 * Real.pi * (|a₁| / a₂))) : ℂ) *
                ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ),
                  ((y₁⁻¹ : ℝ) : ℂ) ^ n * (if aR w₀ h₀ = 0 then (1 : ℂ) else ((SignType.sign y₁ : ℝ) : ℂ)) *
                    ((|y₁| : ℝ) : ℂ) ^ (-(uR w₀ h₀ + 2)) * ((y₂ : ℝ) : ℂ) ^ (P₂.centralExponent - uR w₀ h₀) *
                    (Real.exp (-(Real.pi * (((a₂ * y₂) ^ 2)⁻¹ + (y₁ ^ 2)⁻¹ + a₁ ^ 2 * y₂ ^ 2 + a₂ ^ 2 * y₁ ^ 2))) : ℂ) *
                    (fun v : ℝ => D.W (ArchR.diagOne ((a : ℝ) * v))) (y₁ / y₂) *
                    (∫ z : ℝ, (((a₁ * y₂ - (a₂ * y₂)⁻¹ + a₂ * y₁ : ℝ) : ℂ) + Complex.I * (z : ℂ)) ^ m *
                      (Real.exp (-(Real.pi * z ^ 2)) : ℂ)) := by
  intro s
  rw [setIntegral_congr_fun measurableSet_Ioi (fun a₂ ha₂ => DMain_key K _hdeg μ _hμ _hns uR aR uC kC huR huC ω hω E hE a ha ha1 aInf haInf psiInf hpsiInf ν_add hν_add ν_mul P _hP₁ kw Wr WA hkw1 hkw2 hWr1 hWr2 hWr3 hWr4 hWAN hWAZ hWAK hWAt hWAc w₀R hw₀R w₀ h₀ P₂ hP₂ D k₀ hDW hDE hDnz hk₀min uP nP hnP hPdisc m hm n ε' hcol par₀ S hS hWpos hWneg s a₂ ha₂)]
  simp_rw [integral_const_mul]
  rfl

#print axioms solution

end S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_const_mul_setIntegral_scaledShape_of_discreteSeries_of_conjBlockHarmonic_colHarmonic_gaussian3 (solution)
