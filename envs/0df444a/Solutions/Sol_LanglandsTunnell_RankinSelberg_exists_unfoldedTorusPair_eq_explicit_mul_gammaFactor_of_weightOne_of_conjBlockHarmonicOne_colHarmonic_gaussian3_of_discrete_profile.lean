-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_discrete_profile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e81f6572-914a-5f55-94be-c27409a7e2bc

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
import Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_conjBlockHarmonic_colHarmonic_gaussian3
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_archWeightChar_mul_W_diagOne
import Theorems.Thm_MeasureTheory_setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlock_of_mulConvGaussian_profile
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_postGaussian_torusTriple_conjBlock_of_mulConvGaussian_profile
import Theorems.Thm_LanglandsTunnell_add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_eq_archFactor
import Theorems.Thm_LanglandsTunnell_Converse_integral_postGaussian_torusTriple_conjBlock_eq_mul_prod_GammaR_of_discreteProfile
import Theorems.Thm_LanglandsTunnell_Converse_integral_thetaFree_iwasawaIntegrand_conjBlock_eq_integral_postGaussian_torusTriple
import Theorems.Thm_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_archOfParamR_principal_one_real_one_complex
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_discrete_profile

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws14K7flatKit

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

theorem eθ_mul_conj (θ : ℝ) :
    (((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) * (((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ)) = 1 := by
  have h := Real.sin_sq_add_cos_sq θ
  have h' : ((Real.sin θ : ℝ) : ℂ) ^ 2 + ((Real.cos θ : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast h
  linear_combination (norm := ring_nf) h'
  all_goals (simp [Complex.I_sq]; try ring)

theorem eθ_ne_zero (θ : ℝ) : (((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) ≠ 0 := by
  intro h; have := eθ_mul_conj θ; rw [h, zero_mul] at this; exact zero_ne_one this

theorem archWeightOneℝ_rotGL (θ : ℝ) :
    ((archWeightOneℝ ⟨rotGL θ, rotGL_mem θ⟩ : ℂˣ) : ℂ) = ((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ) := by
  show firstRowℂ (rotGL θ) = _
  apply Complex.ext <;>
    simp only [firstRowℂ, rotGL_coe, rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

theorem archWeightOneℝ_rotGL_mul_eθ (θ : ℝ) :
    ((archWeightOneℝ ⟨rotGL θ, rotGL_mem θ⟩ : ℂˣ) : ℂ) * (((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) = 1 := by
  rw [archWeightOneℝ_rotGL, mul_comm, eθ_mul_conj]

theorem archWeightCharℝ_rotGL_mul_eθ_pow (k : ℕ) (θ : ℝ) :
    ((archWeightCharℝ (k : ℤ) ⟨rotGL θ, rotGL_mem θ⟩ : ℂˣ) : ℂ) *
      (((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) ^ k = 1 := by
  have h1 : ((archWeightCharℝ (k : ℤ) ⟨rotGL θ, rotGL_mem θ⟩ : ℂˣ) : ℂ) =
      (((archWeightOneℝ ⟨rotGL θ, rotGL_mem θ⟩ : ℂˣ) : ℂ)) ^ k := by
    simp [archWeightCharℝ, zpowGroupHom, Units.val_pow_eq_pow_val]
  rw [h1, ← mul_pow, archWeightOneℝ_rotGL_mul_eθ, one_pow]

theorem flat_phase (n : ℕ) (k₀ : ℤ) (hk : k₀ = (n : ℤ) + 1) (y₂ θ : ℝ) :
    ((archWeightCharℝ k₀ ⟨rotGL θ, rotGL_mem θ⟩ : ℂˣ) : ℂ) *
        (((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
        (((y₂ * Real.sin θ : ℝ) : ℂ) + (-1 : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ n =
      (-Complex.I * (y₂ : ℂ)) ^ n := by
  have hcol : ((y₂ * Real.sin θ : ℝ) : ℂ) + (-1 : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ) =
      (-Complex.I * (y₂ : ℂ)) * (((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) := by
    push_cast; ring_nf; (try simp [Complex.I_sq])
  have hk' : k₀ = ((n + 1 : ℕ) : ℤ) := by rw [hk]; push_cast; ring
  rw [hcol, mul_pow, hk']
  have := archWeightCharℝ_rotGL_mul_eθ_pow (n + 1) θ
  calc ((archWeightCharℝ ((n + 1 : ℕ) : ℤ) ⟨rotGL θ, rotGL_mem θ⟩ : ℂˣ) : ℂ) *
        (((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
        ((-Complex.I * (y₂ : ℂ)) ^ n * (((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) ^ n)
      = (((archWeightCharℝ ((n + 1 : ℕ) : ℤ) ⟨rotGL θ, rotGL_mem θ⟩ : ℂˣ) : ℂ) *
          (((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) ^ (n + 1)) * (-Complex.I * (y₂ : ℂ)) ^ n := by ring
    _ = (-Complex.I * (y₂ : ℂ)) ^ n := by rw [this, one_mul]

end Ws14K7flatKit

namespace Ws14K7flatKit

theorem ae_ne_zero : ∀ᵐ t : ℝ, t ≠ 0 := by
  have h : ({(0 : ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.2 (measure_singleton 0)
  exact Filter.Eventually.mono h fun t ht => by simpa using ht

theorem integrand_pointwise_flat {P₂ : RealArchParam} (D : ArchDatumR P₂) (k₀ : ℤ) (n : ℕ) (hk : k₀ = (n : ℤ) + 1)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₀ w : ℂ) (a₀ : ZMod 2) (Wt : ℝ → ℂ) (a : ℝ) (ha : a ≠ 0) (s : ℂ)
    {x y₁ y₂ θ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    (let g : Matrix (Fin 2) (Fin 2) ℝ :=
       !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
          y₂ * Real.sin θ, y₂ * Real.cos θ]
     ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ *
         (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
       ((∫ t : ℝ, Wt t * D.W (ArchR.diagOne (a * t) * g) *
           (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
        (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ (0 : ℕ) *
          ((((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
              ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ)))) ^ (1 : ℕ) *
          (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
          ((|y₁ * y₂| : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) ^ n *
          (((y₂ * Real.sin θ : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ n *
          ((1 / 2 : ℂ) *
            ((Real.pi * a ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ) ^ (-(w / 2)) *
            Complex.Gamma (w / 2)))) *
       ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) =
    ArchR.quasiChar u₀ a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
      ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
        (∫ t : ℝ, Wt t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
           (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
        (((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) *
          (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
          ((|y₁ * y₂| : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
          ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-(w / 2)) * Complex.Gamma (w / 2)))) *
      ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) := by
  have hsc : (y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2 = y₂ ^ 2 := by
    have := Real.sin_sq_add_cos_sq θ; nlinarith [this]
  simp only [hsc]
  have hr : (((⟨rotGL θ, rotGL_mem θ⟩ : rowIsometrySubgroup₀ ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := rfl
  have hpt : ∀ᵐ t : ℝ, Wt t * D.W (ArchR.diagOne (a * t) *
        !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
           y₂ * Real.sin θ, y₂ * Real.cos θ]) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) =
      (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ) * ((archWeightCharℝ k₀ ⟨rotGL θ, rotGL_mem θ⟩ : ℂˣ) : ℂ)) *
        (Wt t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) := by
    refine ae_ne_zero.mono fun t ht => ?_
    rw [LanglandsTunnell.Converse.ArchDatumR.W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_archWeightChar_mul_W_diagOne
      D k₀ hDW (mul_ne_zero ha ht) x hy₁ hy₂ θ ⟨rotGL θ, rotGL_mem θ⟩ hr]
    ring
  have hT : (∫ t : ℝ, Wt t * D.W (ArchR.diagOne (a * t) *
        !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
           y₂ * Real.sin θ, y₂ * Real.cos θ]) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) =
      (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ) * ((archWeightCharℝ k₀ ⟨rotGL θ, rotGL_mem θ⟩ : ℂˣ) : ℂ)) *
        ∫ t : ℝ, Wt t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
           (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) := by
    rw [integral_congr_ae hpt, integral_const_mul]
  have hph := flat_phase n k₀ hk y₂ θ
  simp only [Complex.ofReal_neg, Complex.ofReal_one] at hph ⊢
  rw [hT, ← hph]
  ring

end Ws14K7flatKit

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

namespace Ws23K7mt
open MeasureTheory

theorem iterated_eq_prod (H : ℝ → ℝ → ℝ → ℂ)
    (hH : Integrable (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))))) :
    ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ t : ℝ, H t y₁ y₂ =
      ∫ q, H q.1 q.2.1 q.2.2 ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by
  rw [integral_prod_symm (fun q : ℝ × ℝ × ℝ => H q.1 q.2.1 q.2.2) hH, integral_prod _ hH.integral_prod_right]
end Ws23K7mt

namespace Ws48K7flatDiscCore

open LanglandsTunnell.Converse.ArchR

theorem core_flat_disc {P₂ : RealArchParam} (D : ArchDatumR P₂) (k₀ : ℤ) (n : ℕ) (hk : k₀ = (n : ℤ) + 1)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u : ℂ) (k : ℕ) (hkk : 1 ≤ k) (hP₂eq : P₂ = RealArchParam.discrete u k hkk) (hnk : n = k)
    (ρ : ℂ)
    (hρ : (∀ τ : ℝ, 0 < τ →
        D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (u + (k : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0))
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (ν₁ ν₂ : ℂ) (e₁ e₂ : ZMod 2) (hne : e₁ ≠ e₂)
    (hW : ∀ b : ZMod 2, ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (e₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (e₂ + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ : ZMod 2)
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
                (((((y₁ * y₂)⁻¹ : ℝ) : ℂ)) ^ (0 : ℕ) *
                  ((((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
                      ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ)))) ^ (1 : ℕ) *
                  (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
                  ((|y₁ * y₂| : ℝ) : ℂ) *
                  (-Complex.I * (a : ℂ)) ^ n *
                  (((y₂ * Real.sin θ : ℝ) : ℂ) + ((-1 : ℝ) : ℂ) * Complex.I * ((y₂ * Real.cos θ : ℝ) : ℂ)) ^ n *
                  ((1 / 2 : ℂ) *
                    ((Real.pi * a ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2) : ℝ) : ℂ)
                        ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                    Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
               ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ))
        = ((((-1 : ℂ) ^ (a₀.val + 1) * ((Real.pi : ℂ) / 2)) * ρ)) *
          ((Complex.Gammaℝ (s + 1 / 2 + ((ν₁ + u₀) + signShift (e₁ + a₀))) *
            Complex.Gammaℝ (s + 1 / 2 + ((ν₂ + u₀) + signShift (e₂ + a₀)))) *
           (Complex.Gammaℂ (s + 1 / 2 + ((ν₁ + u) + ((k : ℂ)) / 2)) *
            Complex.Gammaℂ (s + 1 / 2 + ((ν₂ + u) + ((k : ℂ)) / 2)))) := by
  obtain ⟨σa, hA⟩ := LanglandsTunnell.Converse.exists_forall_integrable_thetaFree_iwasawaIntegrand_conjBlock_of_mulConvGaussian_profile
    ν₁ ν₂ e₁ e₂ W hWc hW D a ha (u₀ + 2) cP a₀ n
  obtain ⟨σ1, hS1⟩ := LanglandsTunnell.Converse.integral_thetaFree_iwasawaIntegrand_conjBlock_eq_integral_postGaussian_torusTriple
    ν₁ ν₂ e₁ e₂ W hWc hW D a ha (u₀ + 2) cP a₀ n
  obtain ⟨σc, hC⟩ := LanglandsTunnell.Converse.exists_forall_integrable_postGaussian_torusTriple_conjBlock_of_mulConvGaussian_profile
    ν₁ ν₂ e₁ e₂ W hWc hW D a ha (u₀ + 2) cP a₀ n
  obtain ⟨σ2, hS2⟩ := LanglandsTunnell.Converse.integral_postGaussian_torusTriple_conjBlock_eq_mul_prod_GammaR_of_discreteProfile
    ν₁ ν₂ e₁ e₂ hne W hWc hW u k hkk D hP₂eq ρ hρ a ha1 u₀ cP hcP a₀ n hnk
  refine ⟨max (max σa σ1) (max σc σ2), fun s hs => ?_⟩
  have hsa : σa < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hs1 : σ1 < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hsc : σc < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hs2 : σ2 < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs

  rw [MeasureTheory.setIntegral_iwasawaRegion_eq_two_pi_mul_of_theta_free _ (fun x y₁ y₂ =>
        ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          ((ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            (∫ t : ℝ, W t * ArchR.psi (a * t * x) * D.W (ArchR.diagOne (a * t * y₁ / y₂)) *
               (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
            (((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) *
              (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
              ((|y₁ * y₂| : ℝ) : ℂ) *
              (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
              ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
                Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2)))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) ?hFG (hA s hsa)]
  case hFG =>
    intro x y₁ y₂ θ hy₁ hy₂
    exact Ws14K7flatKit.integrand_pointwise_flat D k₀ n hk hDW (u₀ + 2) (cP + P₂.centralExponent + 2 * s + n + 1)
      a₀ W a ha s hy₁ hy₂

  have h0 : ∀ᵐ y₁ : ℝ, y₁ ≠ 0 := Ws14K7flatKit.ae_ne_zero
  have hstep : (∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ x : ℝ,
        ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
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
      ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), ∫ t : ℝ,
        (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ - 1 / y₂ - a * t * y₁ : ℝ)) : ℂ)))) := by
    refine integral_congr_ae ?_
    filter_upwards [h0] with y₁ hy₁
    exact setIntegral_congr_fun measurableSet_Ioi (fun y₂ hy₂ => hS1 s hs1 y₁ hy₁ y₂ hy₂)
  rw [hstep]

  have hJ : Integrable (fun q : ℝ × ℝ × ℝ =>
        (ArchR.quasiChar (u₀ + 2) a₀ (q.2.1 * q.2.2)⁻¹ * (((|(q.2.1 * q.2.2)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ q.2.2 * ((|q.2.2| : ℝ) : ℂ)) *
          (((|q.2.1 * q.2.2| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (q.2.2 : ℂ)) ^ n *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * q.2.2 ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2))) *
          ((q.2.2 ^ 2 * (|q.2.1 * q.2.2| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / q.2.1 ^ 2 + 1 / q.2.2 ^ 2))) : ℂ) * ((|q.2.1| : ℝ) : ℂ)) *
          (W q.1 * D.W (ArchR.diagOne (a * q.1 * q.2.1 / q.2.2)) * (((|q.1| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((q.1 ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * q.1) ^ 2 * q.2.1 ^ 2))) : ℂ) * (((1 / q.2.1 - 1 / q.2.2 - a * q.1 * q.2.1 : ℝ)) : ℂ)))))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi 0)))) := by
    refine (hC s hsc 1 (-1) (-1)).congr (ae_of_all _ fun q => ?_)
    push_cast
    ring
  rw [Ws23K7mt.iterated_eq_prod (fun t y₁ y₂ =>
        (ArchR.quasiChar (u₀ + 2) a₀ (y₁ * y₂)⁻¹ * (((|(y₁ * y₂)⁻¹| ^ 2)⁻¹ : ℝ) : ℂ) *
          (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
          (((|y₁ * y₂| : ℝ) : ℂ) * (-Complex.I * (a : ℂ)) ^ n * (-Complex.I * (y₂ : ℂ)) ^ n *
            ((1 / 2 : ℂ) * ((Real.pi * a ^ 2 * y₂ ^ 2 : ℝ) : ℂ) ^ (-((cP + P₂.centralExponent + 2 * s + n + 1) / 2)) *
              Complex.Gamma ((cP + P₂.centralExponent + 2 * s + n + 1) / 2))) *
          ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ)) *
        (((Real.exp (-(Real.pi * (1 / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ)) *
          (W t * D.W (ArchR.diagOne (a * t * y₁ / y₂)) * (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ) *
            ((Real.exp (-(Real.pi * ((a * t) ^ 2 * y₁ ^ 2))) : ℂ) * (((1 / y₁ - 1 / y₂ - a * t * y₁ : ℝ)) : ℂ))))) hJ]

  rw [hS2 s hs2]
  have hL1 : Complex.Gammaℝ (s + 1 / 2 + (ν₁ + (u + (k : ℂ) / 2))) * Complex.Gammaℝ (s + 1 / 2 + (ν₁ + (u + (k : ℂ) / 2)) + 1) =
      Complex.Gammaℂ (s + 1 / 2 + ((ν₁ + u) + ((k : ℂ)) / 2)) := by
    rw [Complex.Gammaℝ_mul_Gammaℝ_add_one]; ring_nf
  have hL2 : Complex.Gammaℝ (s + 1 / 2 + (ν₂ + (u + (k : ℂ) / 2))) * Complex.Gammaℝ (s + 1 / 2 + (ν₂ + (u + (k : ℂ) / 2)) + 1) =
      Complex.Gammaℂ (s + 1 / 2 + ((ν₂ + u) + ((k : ℂ)) / 2)) := by
    rw [Complex.Gammaℝ_mul_Gammaℝ_add_one]; ring_nf
  have hsgn : ((-1 : ℂ) ^ (a₀ + 1).val) = (-1 : ℂ) ^ (a₀.val + 1) := by
    rcases Ws23K7kit2.zmod2_any a₀ 0 with h | h
    · rw [h]
      have h1 : ((0 : ZMod 2) + 1).val = 1 := by decide
      have h2 : (0 : ZMod 2).val = 0 := by decide
      rw [h1, h2]
    · rw [h]
      have h1 : ((0 : ZMod 2) + 1 + 1).val = 0 := by decide
      have h2 : ((0 : ZMod 2) + 1).val = 1 := by decide
      rw [h1, h2]; norm_num
  rw [hL1, hL2, hsgn]
  push_cast
  ring

end Ws48K7flatDiscCore

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
    (hPw1 : ∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ ∧ a₁ ≠ a₂)
    (hk₀ : 1 ≤ k₀)
    (n : ℕ) (hn : (n : ℤ) = k₀ - 1)
    (par₀ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (u : ℂ) (k : ℕ) (hk : 1 ≤ k) (hP₂eq : P₂ = RealArchParam.discrete u k hk)
    (hk0k : k₀ = (k : ℤ) + 1) (hnk : n = k)
    (ρ : ℂ)
    (hρ : (∀ τ : ℝ, 0 < τ →
        D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (u + (k : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0)) :
    ∃ σ₁ : ℝ, ∀ s : ℂ, σ₁ < s.re →
            (∫ e : Fin 2 → Fin 2 → ℝ,
              ArchR.quasiChar (uR w₀ h₀ + 2) (aR w₀ h₀) (Matrix.of e).det *
                  (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
                ((∫ t : ℝ, Wr par₀ default t * D.W (ArchR.diagOne ((a : ℝ) * t) * (Matrix.of e)⁻¹) *
                    (((|t| : ℝ) : ℂ) ^ (s - 1 / 2)) * (((t ^ 2)⁻¹ : ℝ) : ℂ)) *
                 (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (P.centralExponent + P₂.centralExponent + 2 * s) *
                    godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)))
              = (((-1 : ℂ) ^ ((aR w₀ h₀).val + 1) * ((Real.pi : ℂ) / 2)) * ρ) * (((twistedGammaR K (archOfParamR K P) uR aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (archOfParamR K P) (archOfParamC K P) uR aR uC kC).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by

  obtain ⟨ν₁, ν₂, e₁, e₂, hP, hne⟩ := hPw1
  have hPc : P.centralExponent = ν₁ + ν₂ := by rw [hP]; rfl
  have hPs : P.centralSign = e₁ + e₂ := by rw [hP]; rfl
  have he : e₁ + e₂ = 1 := Ws23K7kit2.zmod2_sum_one_of_ne hne
  have ha' : ((a : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ha
  have ha1' : ((a : ℚ) : ℝ) = -1 := by rw [ha1]; push_cast; ring
  have hkn : k₀ = (n : ℤ) + 1 := by rw [hnk]; exact hk0k

  obtain ⟨wC, hC, hall, hkne, hP₂'⟩ : ∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
      ∃ hkz : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hkz) := by
    rcases hP₂ with ⟨w₁, w₂, h₁, h₂, -, -, -, -, hpr⟩ | ⟨wC, hC, hall, hbr⟩
    · exfalso; rw [hP₂eq] at hpr; cases hpr
    · rcases hbr with ⟨hkz, hd⟩ | ⟨-, hpr⟩
      · exact ⟨wC, hC, hall, hkz, hd⟩
      · exfalso; rw [hP₂eq] at hpr; cases hpr
  have hinj : u = uC wC hC ∧ k = (kC wC hC).natAbs := by
    rw [hP₂eq] at hP₂'
    injection hP₂' with h1 h2
    exact ⟨h1, h2⟩

  have hreal : (default : InfinitePlace ℚ).IsReal := IsTotallyReal.isReal _
  set Wf : ℝ → ℂ := fun t => Wr par₀ default t with hWf
  have hWc : ContinuousOn Wf {t : ℝ | t ≠ 0} :=
    Ws23K7kit2.continuousOn_Wr (WA par₀) (hWAc par₀) Wf (hWAt par₀)
  have hMel : ∀ b : ZMod 2, ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      MellinConvergent (fun t : ℝ => (Wf t + (-1 : ℂ) ^ b.val * Wf (-t)) / (t : ℂ)) s ∧
        mellin (fun t : ℝ => (Wf t + (-1 : ℂ) ^ b.val * Wf (-t)) / (t : ℂ)) s
          = ((RealArchParam.principal ν₁ e₁ ν₂ e₂).twist 0 b).archFactor s := by
    intro b
    have hb : b = par₀ ∨ b = par₀ + P.centralSign := by rw [hPs, he]; exact Ws23K7kit2.zmod2_any b par₀
    obtain ⟨s₀, hs₀⟩ := hWr4 par₀ default hreal b hb
    refine ⟨s₀, fun s hs => ?_⟩
    have := hs₀ s hs
    rw [← hP]
    simp only [hWf, Complex.ofReal_neg]
    exact this
  have hK9 := fun b t ht => LanglandsTunnell.add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_eq_archFactor
    ν₁ ν₂ e₁ e₂ Wf hWc hMel b t ht
  have hRA9 := LanglandsTunnell.Converse.prod_map_GammaR_twistedGammaR_archOfParamR_principal_one_real_one_complex
    K w₀ wC h₀ hC hall uR aR uC kC P ν₁ ν₂ e₁ e₂ hP

  obtain ⟨σf, hfr⟩ := LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_conjBlockHarmonic_colHarmonic_gaussian3
    K _hdeg μ _hμ _hns uR aR uC kC huR huC ω hω E hE a ha ha1 aInf haInf psiInf hpsiInf ν_add hν_add ν_mul P _hP₁ kw Wr WA hkw1 hkw2 hWr1 hWr2 hWr3 hWr4 hWAN hWAZ hWAK hWAt hWAc w₀R hw₀R w₀ h₀ P₂ hP₂ D k₀ hDW hDE hDnz hk₀min par₀ 1 n 0 (Or.inl rfl) (-1) (Or.inr rfl) S (by rw [hS]; funext M; push_cast; ring)

  obtain ⟨σ₂, hcore⟩ := Ws48K7flatDiscCore.core_flat_disc D k₀ n hkn hDW u k hk hP₂eq hnk ρ hρ Wf hWc
    ν₁ ν₂ e₁ e₂ hne hK9 (uR w₀ h₀) P.centralExponent hPc (aR w₀ h₀) ((a : ℚ) : ℝ) ha' ha1'
  refine ⟨max σf σ₂, fun s hs => ?_⟩
  have h := hcore s (lt_of_le_of_lt (le_max_right _ _) hs)
  simp only [hWf] at h
  rw [Complex.ofReal_ratCast] at h
  obtain ⟨hR, hC'⟩ := hRA9 s
  rw [hfr s (lt_of_le_of_lt (le_max_left _ _) hs), h, hR, hC', ← hinj.1, ← hinj.2]

end S_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_discrete_profile
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_unfoldedTorusPair_eq_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_discrete_profile (solution)
