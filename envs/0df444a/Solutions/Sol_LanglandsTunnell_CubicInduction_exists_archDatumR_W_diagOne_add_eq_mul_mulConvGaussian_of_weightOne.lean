-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_archDatumR_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3ba13d67-90cd-5996-9ea7-cdf72a3b40e5

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
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_discrete_profile_solves_whittaker_ode
import Theorems.Thm_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
import Theorems.Thm_LanglandsTunnell_mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero
import Theorems.Thm_LanglandsTunnell_add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_eq_archFactor
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_sq_mul_sq_eq_one_and_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_raising_lowering_splitTorus_of_archWeightChar_of_unipotent
import Theorems.Thm_LanglandsTunnell_exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne
import Theorems.Thm_LanglandsTunnell_RealArchParam_eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire
import Mathlib.Analysis.MellinTransform
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_archDatumR_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOne

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws1K5

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

theorem neg_one_pow_val_mul_self (c : ZMod 2) : (-1 : ℂ) ^ c.val * (-1 : ℂ) ^ c.val = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

theorem neg_one_pow_val_succ_mul (c : ZMod 2) : (-1 : ℂ) ^ (c + 1).val * (-1 : ℂ) ^ c.val = -1 := by
  rcases zmod2_cases c with rfl | rfl
  · have h1 : ((0 : ZMod 2) + 1).val = 1 := by decide
    have h2 : (0 : ZMod 2).val = 0 := by decide
    rw [h1, h2]; norm_num
  · have h1 : ((1 : ZMod 2) + 1).val = 0 := by decide
    have h2 : (1 : ZMod 2).val = 1 := by decide
    rw [h1, h2]; norm_num

theorem eq_add_one_of_ne {b c : ZMod 2} (h : b ≠ c) : b = c + 1 := by
  rcases zmod2_cases b with rfl | rfl <;> rcases zmod2_cases c with rfl | rfl
  · exact absurd rfl h
  · decide
  · decide
  · exact absurd rfl h

theorem continuousOn_sqrt_cpow (e : ℂ) :
    ContinuousOn (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ) ^ e) (Set.Ioi 0) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.cpow
  · exact (Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousAt
  · exact continuousAt_const
  · rw [Complex.ofReal_mem_slitPlane]; exact Real.sqrt_pos.2 ht

theorem lowering_elem (y : ℝ) (hy : 0 < y) :
    2 * (y : ℂ) * deriv (fun y : ℝ => (((y ^ (1 / 2 : ℝ) * (2 * y ^ (((0 : ℕ) : ℝ) / 2) * Real.exp (-(2 * Real.pi * y)))) : ℝ) : ℂ)) y
      + (4 * (Real.pi : ℂ) * (y : ℂ) - ((1 : ℤ) : ℂ)) *
        (((y ^ (1 / 2 : ℝ) * (2 * y ^ (((0 : ℕ) : ℝ) / 2) * Real.exp (-(2 * Real.pi * y)))) : ℝ) : ℂ) = 0 := by
  have hfun : (fun y : ℝ => (((y ^ (1 / 2 : ℝ) * (2 * y ^ (((0 : ℕ) : ℝ) / 2) * Real.exp (-(2 * Real.pi * y)))) : ℝ) : ℂ)) =
      fun y : ℝ => (((2 * (y ^ (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * y)))) : ℝ) : ℂ) := by
    funext y; simp [Real.rpow_zero]; ring
  have h1 : HasDerivAt (fun y : ℝ => y ^ (1 / 2 : ℝ)) ((1 / 2 : ℝ) * y ^ ((1 / 2 : ℝ) - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(2 * Real.pi * y))) (Real.exp (-(2 * Real.pi * y)) * (-(2 * Real.pi))) y := by
    have : HasDerivAt (fun y : ℝ => -(2 * Real.pi * y)) (-(2 * Real.pi)) y := by
      have h__af := ((hasDerivAt_id y).const_mul (2 * Real.pi)).neg
      simp at h__af
      exact h__af
    exact (Real.hasDerivAt_exp _).comp y this
  have h3 : HasDerivAt (fun y : ℝ => 2 * (y ^ (1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * y))))
      (2 * ((1 / 2 : ℝ) * y ^ ((1 / 2 : ℝ) - 1) * Real.exp (-(2 * Real.pi * y)) +
        y ^ (1 / 2 : ℝ) * (Real.exp (-(2 * Real.pi * y)) * (-(2 * Real.pi))))) y :=
    (h1.mul h2).const_mul 2
  have h4 := h3.ofReal_comp
  rw [hfun, h4.deriv]
  have hhalf : y * y ^ ((1 / 2 : ℝ) - 1) = y ^ (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num, Real.rpow_neg hy.le]
    have : y ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) = y := by
      rw [← Real.rpow_add hy]; norm_num
    field_simp
    linarith [this]
  push_cast
  simp only [zero_div, Real.rpow_zero, Complex.ofReal_one, mul_one]
  have hc : ((y : ℝ) : ℂ) * ((y ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ) = ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hhalf]
  linear_combination (2 * Complex.exp (-(2 * (Real.pi : ℂ) * (y : ℂ)))) * hc

section Frame
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion NumberField.TateGlobal AutomorphicForm LanglandsTunnell.Converse IsDedekindDomain

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in

theorem exists_unit_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (t : ℝ) :
    ∃ x : (w.Completion)ˣ, ‖(x : w.Completion)‖ = Real.exp t ∧
      extensionEmbedding w (x : w.Completion) = (Real.exp t : ℂ) := by
  set y : w.Completion := (ringEquivRealOfIsReal hw).symm (Real.exp t) with hy
  have hey : extensionEmbeddingOfIsReal hw y = Real.exp t := by
    rw [← ringEquivRealOfIsReal_apply, hy, RingEquiv.apply_symm_apply]
  have hey' : extensionEmbedding w y = (Real.exp t : ℂ) := by
    rw [← extensionEmbeddingOfIsReal_apply hw, hey]
  have hnorm : ‖y‖ = Real.exp t := by
    have := (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) y
    rw [← this, hey', Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact (Real.exp_pos t).ne' hnorm.symm
  exact ⟨Units.mk0 y hy0, hnorm, hey'⟩

theorem re_eq_zero_of_isArchCompAt_of_isReal {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (huμ : IsUnitaryChar (𝓞 K) K μ)
    {w : InfinitePlace K} (hw : w.IsReal) {u : ℂ} {a : ℤ} (h : IsArchCompAt K μ w u a) : u.re = 0 := by
  obtain ⟨x, hxn, hxe⟩ := exists_unit_of_isReal (K := K) hw 1
  have h1 : ‖((archLocalChar μ w x : ℂˣ) : ℂ)‖ = 1 := huμ _
  rw [h x, hxn, hxe, div_self (by exact_mod_cast (Real.exp_pos 1).ne'), one_zpow, mul_one,
    Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le), Complex.norm_exp,
    Real.exp_eq_one_iff] at h1
  have hm : (w.mult : ℝ) ≠ 0 := mult_coe_ne_zero
  simp only [Complex.ofReal_one, one_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] at h1
  rcases mul_eq_zero.mp h1 with h' | h'
  · exact absurd h' hm
  · exact h'

end Frame

open LanglandsTunnell.Converse in
theorem coe_unipotentGL2 (x : ℝ) :
    ((AutomorphicForm.unipotentGL2 x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = ArchR.unip x := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem coe_splitTorusGL2_log_half (y : ℝ) (hy : 0 < y) :
    ((AutomorphicForm.splitTorusGL2 (Real.log y / 2) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1 * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := by
  have h1 : Real.exp (Real.log y / 2) = Real.sqrt y := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy]; ring_nf
  ext i j; fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.splitTorusGL2, h1, Real.exp_neg]

open LanglandsTunnell.Converse in
theorem splitTorus_mul_diagonal (y : ℝ) :
    (!![1 * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.diagonal ![(-1 : ℝ), 1] =
      !![(-1) * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal]

open LanglandsTunnell.Converse MeasureTheory in

theorem zeta_unfold (P : RealArchParam) (D : ArchDatumR P) (a : ZMod 2) (s : ℂ) (hs : D.zeta_abscissa < s.re) :
    MellinConvergent
        (fun t : ℝ => (D.W (ArchR.diagOne t) + (-1 : ℂ) ^ a.val * D.W (ArchR.diagOne (-t))) / (t : ℂ)) s ∧
      mellin (fun t : ℝ => (D.W (ArchR.diagOne t) + (-1 : ℂ) ^ a.val * D.W (ArchR.diagOne (-t))) / (t : ℂ)) s
        = (P.twist 0 a).archFactor s * D.zetaEntire 1 0 a s := by
  classical
  set f : ℝ → ℂ := fun τ => D.W (ArchR.diagOne τ) with hf
  set F : ℝ → ℂ := fun t => (D.W (ArchR.diagOne t) + (-1 : ℂ) ^ a.val * D.W (ArchR.diagOne (-t))) / (t : ℂ) with hF
  have hsgn_neg : ∀ y : ℝ, 0 < y → ArchR.quasiChar 0 a (-y) = (-1 : ℂ) ^ a.val := by
    intro y hy
    simp only [ArchR.quasiChar, Complex.cpow_zero, one_mul, Left.sign_neg, sign_pos hy, SignType.coe_neg,
      SignType.coe_one]
    rcases Nat.lt_or_ge a.val 1 with h | h
    · have : a = 0 := by
        have : a.val = 0 := by omega
        exact (ZMod.val_eq_zero a).1 this
      simp [this]
    · have ha1 : a.val = 1 := by have := a.val_lt; omega
      have : a ≠ 0 := by intro h0; rw [h0, ZMod.val_zero] at ha1; exact absurd ha1 (by norm_num)
      simp [this, ha1]
  have hsgn_pos : ∀ y : ℝ, 0 < y → ArchR.quasiChar 0 a y = 1 := by
    intro y hy
    simp only [ArchR.quasiChar, Complex.cpow_zero, one_mul, sign_pos hy, SignType.coe_one]
    split_ifs <;> simp
  have hpos : ∀ y : ℝ, 0 < y →
      ArchR.zetaIntegrand D.W 1 0 a s y = (y : ℂ) ^ (s - 1) • (f y / (y : ℂ)) := by
    intro y hy
    simp only [ArchR.zetaIntegrand, hsgn_pos y hy, hf, Matrix.mul_one, abs_of_pos hy, smul_eq_mul, mul_one]
    rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.2 hy.ne'), Complex.cpow_one]
    field_simp
  have hneg : ∀ y : ℝ, 0 < y →
      ArchR.zetaIntegrand D.W 1 0 a s (-y) = (-1 : ℂ) ^ a.val * ((y : ℂ) ^ (s - 1) • (f (-y) / (y : ℂ))) := by
    intro y hy
    simp only [ArchR.zetaIntegrand, hsgn_neg y hy, hf, Matrix.mul_one, abs_neg, abs_of_pos hy, smul_eq_mul]
    rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.2 hy.ne'), Complex.cpow_one]
    field_simp
  have hFsplit : ∀ y : ℝ, 0 < y →
      (y : ℂ) ^ (s - 1) • F y = ArchR.zetaIntegrand D.W 1 0 a s y + ArchR.zetaIntegrand D.W 1 0 a s (-y) := by
    intro y hy
    rw [hpos y hy, hneg y hy]
    simp only [hF, hf, smul_eq_mul]
    ring
  have hI : Integrable (ArchR.zetaIntegrand D.W 1 0 a s) :=
    D.zeta_integrable 1 0 a s (by simp) (by simpa using hs)
  have hI' : Integrable (fun y : ℝ => ArchR.zetaIntegrand D.W 1 0 a s (-y)) := hI.comp_neg
  constructor
  ·
    show IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • F t) (Set.Ioi 0)
    exact (hI.integrableOn.add hI'.integrableOn).congr_fun (fun y hy => (hFsplit y hy).symm) measurableSet_Ioi
  ·
    have hz := D.zeta_eq 1 0 a s (by simp) (by simpa using hs)
    rw [← hz, ← integral_add_compl (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))) hI, Set.compl_Ioi,
      ← neg_zero, ← integral_comp_neg_Ioi 0, neg_zero, ← integral_add hI.integrableOn hI'.integrableOn]
    unfold mellin
    exact setIntegral_congr_fun measurableSet_Ioi fun y hy => hFsplit y hy

end Ws1K5

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
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
    (ha : a ≠ 0)
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
    (hk₀ : k₀ = 1)
    (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c₁ u₂ c₂) (hc : c₁ ≠ c₂) :
    ∃ ρ : ℂ, ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (u₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ)) := by
  classical
  obtain ⟨-, hparity⟩ := hk₀min.1 u₁ u₂ c₁ c₂ hP₂eq
  subst hk₀
  subst hP₂eq

  have hWcont : ContinuousOn (fun τ : ℝ => D.W (ArchR.diagOne τ)) {τ : ℝ | τ ≠ 0} := by
    have hc := D.smooth.continuousOn
    have hm : ContinuousOn (fun τ : ℝ => (fun i j : Fin 2 => ArchR.diagOne τ i j)) {τ : ℝ | τ ≠ 0} := by
      refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
      fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne] <;> fun_prop
    have hmaps : Set.MapsTo (fun τ : ℝ => (fun i j : Fin 2 => ArchR.diagOne τ i j)) {τ : ℝ | τ ≠ 0} ArchR.glSet := by
      intro τ hτ
      show (Matrix.of fun i j : Fin 2 => ArchR.diagOne τ i j).det ≠ 0
      have : (Matrix.of fun i j : Fin 2 => ArchR.diagOne τ i j) = ArchR.diagOne τ := by ext i j; rfl
      rw [this]; simp [ArchR.diagOne, Matrix.det_fin_two_of]; exact hτ
    have := hc.comp hm hmaps
    refine this.congr fun τ hτ => ?_
    show D.W (ArchR.diagOne τ) = ArchR.asPi D.W (fun i j : Fin 2 => ArchR.diagOne τ i j)
    simp only [ArchR.asPi]
    congr 1
  by_cases hu : u₁ = u₂
  ·

    subst hu
    have hneg : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0 := by
      intro τ hτ
      refine LanglandsTunnell.Converse.ArchDatumR.W_eq_zero_of_det_neg_of_principal_of_ne_of_archWeightChar_one_of_isCasimirEigen
        u₁ c₁ c₂ hc D hDW hDE _ ?_
      simp [ArchR.diagOne, Matrix.det_fin_two_of, hτ]

    have hν : (0 : ℂ) ^ 2 = 1 / 4 - (RealArchParam.principal u₁ c₁ u₁ c₂).laplaceEigenvalue := by
      simp [RealArchParam.laplaceEigenvalue]
    obtain ⟨-, -, -, hode⟩ :=
      LanglandsTunnell.Converse.ArchDatumR.laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen _ D 1 0 hν hDW hDE
    obtain ⟨hdiff, hdiff', hODE, hgr⟩ := hode 1 (Or.inl rfl)
    set f₀ : ℝ → ℂ := fun y : ℝ =>
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W x)
        !![1 * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] with hf₀
    have hWf : ∀ t : ℝ, 0 < t → D.W (ArchR.diagOne t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₁ + 1) * f₀ t := by
      intro t ht
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
      have hmat : ArchR.diagOne t = Real.sqrt t • !![1 * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [ArchR.diagOne, Matrix.smul_apply, Real.mul_self_sqrt ht.le, hs.ne']
      have hdet : (!![1 * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
        rw [Matrix.det_fin_two_of]; simp [hs.ne']
      have hf₀t : f₀ t = D.W !![1 * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] := by
        simp only [hf₀]
        rw [hdet, abs_one, Real.one_rpow, Complex.ofReal_one, one_mul]
      have hp : ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₁ + 1) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₁) * ((Real.sqrt t : ℝ) : ℂ) := by
        rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hs.ne'), Complex.cpow_one]
      have hsgn : (if (RealArchParam.principal u₁ c₁ u₁ c₂).centralSign = 0 then (1 : ℂ)
          else ((SignType.sign (Real.sqrt t) : ℝ) : ℂ)) = 1 := by
        split_ifs
        · rfl
        · rw [sign_pos hs]; simp
      rw [hmat, D.central_law _ _ hs.ne', hf₀t, ArchR.centralChar, ArchR.quasiChar, hsgn, mul_one, abs_of_pos hs,
        show (RealArchParam.principal u₁ c₁ u₁ c₂).centralExponent = u₁ + u₁ from rfl, hp]
    have hODE' : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f₀) y
            + (1 / 4 - (0 : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * ((1 : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f₀ y = 0 := by
      intro y hy
      have h := hODE y hy
      simp only [Int.cast_one, mul_one] at h
      exact h

    set φ : ℝ → ℂ := fun y : ℝ =>
      ((y ^ (1 / 2 : ℝ) * (2 * y ^ (((0 : ℕ) : ℝ) / 2) * Real.exp (-(2 * Real.pi * y))) : ℝ) : ℂ) with hφ
    obtain ⟨hφd, hφd', hφODE⟩ := LanglandsTunnell.discrete_profile_solves_whittaker_ode 0 1 0 (by norm_num) (by norm_num) φ
      (fun y => rfl)
    have hφgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖φ y‖ ≤ C * y ^ N := by
      refine ⟨2, 1 / 2 + ((0 : ℕ) : ℝ) / 2, fun y hy => ?_⟩
      have hy0 : 0 < y := lt_of_lt_of_le one_pos hy
      simp only [hφ, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      have hexp : Real.exp (-(2 * Real.pi * y)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
      calc y ^ (1 / 2 : ℝ) * (2 * y ^ (((0 : ℕ) : ℝ) / 2) * Real.exp (-(2 * Real.pi * y)))
          = 2 * (y ^ (1 / 2 : ℝ) * y ^ (((0 : ℕ) : ℝ) / 2)) * Real.exp (-(2 * Real.pi * y)) := by ring
        _ ≤ 2 * (y ^ (1 / 2 : ℝ) * y ^ (((0 : ℕ) : ℝ) / 2)) * 1 :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = 2 * y ^ (1 / 2 + ((0 : ℕ) : ℝ) / 2) := by rw [mul_one, ← Real.rpow_add hy0]
    have hφ1 : φ 1 ≠ 0 := by
      simp only [hφ, Real.one_rpow, one_mul, mul_one, ne_eq, Complex.ofReal_eq_zero]
      positivity
    obtain ⟨d₁, d₂, hd, hdep⟩ := LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
      0 1 f₀ φ hdiff hdiff' hODE' hgr hφd hφd' hφODE hφgr
    have hd₁ : d₁ ≠ 0 := by
      intro h0
      apply hd
      have h2 : d₂ = 0 := by
        have := hdep 1 one_pos
        rw [h0, zero_mul, zero_add] at this
        exact (mul_eq_zero.1 this).resolve_right hφ1
      rw [h0, h2]; rfl
    set lam : ℂ := -d₂ / d₁ with hlam
    have hf₀φ : ∀ y : ℝ, 0 < y → f₀ y = lam * φ y := by
      intro y hy
      have := hdep y hy
      simp only [hlam]
      field_simp
      linear_combination this

    by_cases hlam0 : lam = 0
    · refine ⟨0, fun b τ hτ => ?_⟩
      rw [hWf τ hτ, hf₀φ τ hτ, hlam0, hneg τ hτ]; simp

    set Wc : ℂ → ℂ := fun z => D.W (ArchR.diagOne z.re) with hWc
    have hlow : ∀ y : ℝ, 0 < y →
        2 * (y : ℂ) * deriv (fun y : ℝ => lam * φ y) y + (4 * (Real.pi : ℂ) * (y : ℂ) - ((1 : ℤ) : ℂ)) * (lam * φ y) = 0 := by
      intro y hy
      have hdφ : DifferentiableAt ℝ φ y := (hφd y hy).differentiableAt (Ioi_mem_nhds hy)
      rw [deriv_const_mul lam hdφ]
      have := Ws1K5.lowering_elem y hy
      simp only [hφ] at this ⊢
      linear_combination lam * this
    obtain ⟨-, ρ, hρ0, hMel⟩ := LanglandsTunnell.mellin_whittakerProfile_eq_GammaC_of_lowering_eq_zero (u₁ + u₁) 1 Wc
      (fun y => lam * φ y) (fun _ => 0)
      (fun t ht => by simp only [hWc, Complex.ofReal_re]; rw [hWf t ht, hf₀φ t ht])
      (fun t ht => by simp only [hWc, Complex.neg_re, Complex.ofReal_re]; rw [hneg t ht]; simp)
      (fun y hy => ((hφd y hy).differentiableAt (Ioi_mem_nhds hy)).differentiableWithinAt.const_mul lam)
      (differentiableOn_const 0)
      hlow
      (fun y hy => by simp)
      ⟨0, 0, fun y hy => by simp⟩
      ⟨1, one_pos, mul_ne_zero hlam0 hφ1⟩

    have hc₂ : c₂ = c₁ + 1 := Ws1K5.eq_add_one_of_ne (Ne.symm hc)
    have hAF : ∀ (b : ZMod 2) (s : ℂ),
        ((RealArchParam.principal u₁ c₁ u₁ c₂).twist 0 b).archFactor s = Complex.Gammaℂ (s + u₁) := by
      intro b s
      simp only [RealArchParam.twist, add_zero, RealArchParam.archFactor, RealArchParam.gammaR, RealArchParam.gammaC,
        Multiset.map_zero, Multiset.prod_zero, mul_one, Multiset.insert_eq_cons, Multiset.map_cons,
        Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton]
      rw [hc₂]
      rcases Ws1K5.zmod2_cases (c₁ + b) with h0 | h1
      · have h1' : c₁ + 1 + b = 1 := by rw [add_right_comm, h0, zero_add]
        rw [h0, h1', signShift_zero, signShift_one, add_zero, ← Complex.Gammaℝ_mul_Gammaℝ_add_one, add_assoc]
      · have h0' : c₁ + 1 + b = 0 := by rw [add_right_comm, h1]; decide
        rw [h1, h0', signShift_zero, signShift_one, add_zero, mul_comm, ← Complex.Gammaℝ_mul_Gammaℝ_add_one, add_assoc]

    set Wt : ℝ → ℂ := fun t => ρ * D.W (ArchR.diagOne t) with hWt
    have hWtc : ContinuousOn Wt {t : ℝ | t ≠ 0} := continuousOn_const.mul hWcont
    have hMel' : ∀ b : ZMod 2, ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        MellinConvergent (fun t : ℝ => (Wt t + (-1 : ℂ) ^ b.val * Wt (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (Wt t + (-1 : ℂ) ^ b.val * Wt (-t)) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ c₁ u₁ c₂).twist 0 b).archFactor s := by
      intro b
      refine ⟨-((u₁ + u₁) / 2 + (((1 : ℤ) : ℂ) - 1) / 2).re, fun s hs => ?_⟩
      obtain ⟨h1, h2⟩ := hMel b s hs
      have hfun : (fun t : ℝ => (ρ * Wc t + (-1 : ℂ) ^ b.val * (ρ * Wc (-t))) / (t : ℂ)) =
          fun t : ℝ => (Wt t + (-1 : ℂ) ^ b.val * Wt (-t)) / (t : ℂ) := by
        funext t; simp only [hWc, hWt, Complex.ofReal_re, Complex.neg_re]
      rw [hfun] at h1 h2
      refine ⟨h1, ?_⟩
      rw [h2, hAF]
      congr 1; push_cast; ring
    refine ⟨ρ⁻¹, fun b τ hτ => ?_⟩
    have hK9 := LanglandsTunnell.add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_eq_archFactor u₁ u₁ c₁ c₂ Wt hWtc hMel' b τ hτ
    simp only [hWt] at hK9
    have : D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) =
        ρ⁻¹ * (ρ * D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * (ρ * D.W (ArchR.diagOne (-τ)))) := by
      field_simp
    rw [this, hK9]; ring
  ·

    have hre : u₁.re = 0 ∧ u₂.re = 0 := by
      rcases hP₂ with ⟨w₁, w₂, h₁, h₂, -, -, -, -, hP⟩ | ⟨wC, hC, -, hP⟩
      · simp only [RealArchParam.principal.injEq] at hP
        obtain ⟨hu₁, -, hu₂, -⟩ := hP
        exact ⟨hu₁ ▸ Ws1K5.re_eq_zero_of_isArchCompAt_of_isReal hμ.2.2 h₁ (huR w₁ h₁),
          hu₂ ▸ Ws1K5.re_eq_zero_of_isArchCompAt_of_isReal hμ.2.2 h₂ (huR w₂ h₂)⟩
      · rcases hP with ⟨_, hP⟩ | ⟨-, hP⟩
        · exact absurd hP (by simp)
        · simp only [RealArchParam.principal.injEq] at hP
          obtain ⟨h0, -, h1, -⟩ := hP
          exact absurd (h0.trans h1.symm) hu
    have hsubre : (u₁ - u₂).re = 0 := by rw [Complex.sub_re, hre.1, hre.2, sub_zero]
    have htype : |(u₁ - u₂).re| < 1 := by rw [hsubre, abs_zero]; exact one_pos
    have hgen : ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → c₁ - c₂ ≠ ((p + 1 : ℤ) : ZMod 2) := by
      intro p hp heq
      have := congrArg Complex.re heq
      rw [hsubre, Complex.intCast_re] at this
      exact absurd (by exact_mod_cast this.symm) hp
    obtain ⟨κ, hκsq, hκ⟩ :=
      LanglandsTunnell.Converse.ArchDatumR.exists_sq_mul_sq_eq_one_and_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
        u₁ u₂ c₁ c₂ hc hu hgen htype D hDW hDE
    have hκ0 : κ ≠ 0 := by
      intro h0; rw [h0] at hκsq; simp at hκsq

    have hν : ((u₁ - u₂) / 2) ^ 2 = 1 / 4 - (RealArchParam.principal u₁ c₁ u₂ c₂).laplaceEigenvalue := by
      simp [RealArchParam.laplaceEigenvalue]
    obtain ⟨-, -, -, hode⟩ :=
      LanglandsTunnell.Converse.ArchDatumR.laws_and_torus_ode_of_archWeightChar_of_isCasimirEigen _ D 1 ((u₁ - u₂) / 2) hν hDW hDE
    obtain ⟨hdiff, hdiff', hODE, hgr⟩ := hode 1 (Or.inl rfl)
    set f₀ : ℝ → ℂ := fun y : ℝ =>
      (fun x : Matrix (Fin 2) (Fin 2) ℝ => (((|x.det| ^ (-(1 / 2 : ℝ)) : ℝ)) : ℂ) * D.W x)
        !![1 * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] with hf₀
    have hdet1 : ∀ t : ℝ, 0 < t → (!![1 * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
      intro t ht
      rw [Matrix.det_fin_two_of]; simp [(Real.sqrt_pos.2 ht).ne']
    have hf₀t : ∀ t : ℝ, 0 < t → f₀ t = D.W !![1 * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] := by
      intro t ht
      simp only [hf₀]
      rw [hdet1 t ht, abs_one, Real.one_rpow, Complex.ofReal_one, one_mul]
    have hcent : ∀ (t : ℝ) (ht : 0 < t) (M : Matrix (Fin 2) (Fin 2) ℝ),
        D.W (Real.sqrt t • M) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * D.W M := by
      intro t ht M
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
      have hp : ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂) * ((Real.sqrt t : ℝ) : ℂ) := by
        rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hs.ne'), Complex.cpow_one]
      have hsgn : (if (RealArchParam.principal u₁ c₁ u₂ c₂).centralSign = 0 then (1 : ℂ)
          else ((SignType.sign (Real.sqrt t) : ℝ) : ℂ)) = 1 := by
        split_ifs
        · rfl
        · rw [sign_pos hs]; simp
      rw [D.central_law _ _ hs.ne', ArchR.centralChar, ArchR.quasiChar, hsgn, mul_one, abs_of_pos hs,
        show (RealArchParam.principal u₁ c₁ u₂ c₂).centralExponent = u₁ + u₂ from rfl, hp]
    have hWf : ∀ t : ℝ, 0 < t → D.W (ArchR.diagOne t) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1) * f₀ t := by
      intro t ht
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
      have hmat : ArchR.diagOne t = Real.sqrt t • !![1 * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [ArchR.diagOne, Matrix.smul_apply, Real.mul_self_sqrt ht.le, hs.ne']
      rw [hmat, hcent t ht, hf₀t t ht]
    have hODE' : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f₀) y
            + (1 / 4 - ((u₁ - u₂) / 2) ^ 2 + 2 * (Real.pi : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2) * f₀ y = 0 := by
      intro y hy
      have h := hODE y hy
      simp only [Int.cast_one, mul_one, Complex.ofReal_one] at h
      exact h

    set F : GL (Fin 2) ℝ → ℂ := fun g => D.W (g : Matrix (Fin 2) (Fin 2) ℝ) with hF
    have hFs : ContDiffOn ℝ 1
        (fun e : Fin 2 → Fin 2 → ℝ =>
          F (if h : (Matrix.of e).det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of e) h else 1))
        {e | (Matrix.of e).det ≠ 0} := by
      refine (D.smooth.of_le (by simp)).congr fun e he => ?_
      have he' : (Matrix.of e).det ≠ 0 := he
      simp only [hF, dif_pos he', ArchR.asPi]
      rfl
    have hFψ : ∀ (x : ℝ) (m : GL (Fin 2) ℝ),
        F (AutomorphicForm.unipotentGL2 x * m) = Complex.exp (2 * Real.pi * Complex.I * x) * F m := by
      intro x m
      simp only [hF, Units.val_mul, Ws1K5.coe_unipotentGL2]
      exact D.unip_law x _
    have hFk : ∀ (r : rowIsometrySubgroup₀ ℝ) (m : GL (Fin 2) ℝ), F (m * r) = (archWeightCharℝ 1 r : ℂ) * F m :=
      fun r m => hDW r m
    obtain ⟨-, -, hLR⟩ := LanglandsTunnell.raising_lowering_splitTorus_of_archWeightChar_of_unipotent F 1 hFs hFψ hFk

    have hfT : ∀ y : ℝ, 0 < y → F (AutomorphicForm.splitTorusGL2 (Real.log y / 2)) = f₀ y := by
      intro y hy
      simp only [hF, Ws1K5.coe_splitTorusGL2_log_half y hy]
      exact (hf₀t y hy).symm
    have hderT : ∀ y : ℝ, 0 < y →
        deriv (fun y : ℝ => F (AutomorphicForm.splitTorusGL2 (Real.log y / 2))) y = deriv f₀ y := by
      intro y hy
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact hfT z hz

    set Wc : ℂ → ℂ := fun z => D.W (ArchR.diagOne z.re) with hWc
    have hWm : ∀ t : ℝ, 0 < t →
        κ⁻¹ * Wc (-(t : ℂ)) = ((Real.sqrt t : ℝ) : ℂ) ^ (u₁ + u₂ + 1)
          * (2 * (t : ℂ) * deriv f₀ t + (4 * (Real.pi : ℂ) * (t : ℂ) - 1) * f₀ t) := by
      intro t ht
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
      obtain ⟨-, h2, -, -⟩ := hLR t ht
      have hmat : ArchR.diagOne (-t) = Real.sqrt t • (!![1 * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] * Matrix.diagonal ![(-1 : ℝ), 1]) := by
        rw [Ws1K5.splitTorus_mul_diagonal]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [ArchR.diagOne, Matrix.smul_apply, Real.mul_self_sqrt ht.le, hs.ne']
      have hx : (!![1 * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
        rw [hdet1 t ht]; exact one_ne_zero
      have hrel := hκ _ hx
      simp only [hWc, Complex.neg_re, Complex.ofReal_re]
      rw [hmat, hcent t ht, hrel]

      have hflow : ∀ d : AutomorphicForm.ArchDir,
          LanglandsTunnell.Converse.ArchCasimir.matrixFlowDeriv d D.W !![1 * Real.sqrt t, 0; 0, (Real.sqrt t)⁻¹] =
            deriv (fun s : ℝ => F (AutomorphicForm.splitTorusGL2 (Real.log t / 2) * AutomorphicForm.archFlowMatrix d s)) 0 := by
        intro d
        simp only [LanglandsTunnell.Converse.ArchCasimir.matrixFlowDeriv, hF, Units.val_mul,
          Ws1K5.coe_splitTorusGL2_log_half t ht]
      rw [hflow, hflow, hflow, h2, hderT t ht, hfT t ht, Int.cast_one]
      first | (field_simp; ring) | field_simp

    by_cases hne : ∃ y : ℝ, 0 < y ∧ f₀ y ≠ 0
    swap
    · push_neg at hne
      refine ⟨0, fun b τ hτ => ?_⟩
      have h1 : D.W (ArchR.diagOne τ) = 0 := by rw [hWf τ hτ, hne τ hτ, mul_zero]
      have hd : deriv f₀ τ = 0 := by
        have : deriv f₀ τ = deriv (fun _ : ℝ => (0 : ℂ)) τ := by
          apply Filter.EventuallyEq.deriv_eq
          filter_upwards [Ioi_mem_nhds hτ] with z hz
          exact hne z hz
        rw [this, deriv_const]
      have h2 : D.W (ArchR.diagOne (-τ)) = 0 := by
        have := hWm τ hτ
        simp only [hWc, Complex.neg_re, Complex.ofReal_re, hd, hne τ hτ, mul_zero, add_zero] at this
        exact (mul_eq_zero.1 this).resolve_left (inv_ne_zero hκ0)
      rw [h1, h2]; simp

    have hcdisj : κ⁻¹ = u₁ - u₂ ∨ κ⁻¹ = u₂ - u₁ := by
      have h : (κ⁻¹ - (u₁ - u₂)) * (κ⁻¹ - (u₂ - u₁)) = 0 := by
        have hki : κ⁻¹ * κ = 1 := inv_mul_cancel₀ hκ0
        have : κ⁻¹ ^ 2 = (u₁ - u₂) ^ 2 := by
          linear_combination (-κ⁻¹ ^ 2) * hκsq + ((u₁ - u₂) ^ 2 * (κ⁻¹ * κ + 1)) * hki
        linear_combination this
      rcases mul_eq_zero.1 h with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (sub_eq_zero.1 h)
    obtain ⟨P', hP', ρ, hρ0, hMel⟩ :=
      LanglandsTunnell.exists_mellin_whittakerProfile_eq_archFactor_of_whittaker_ode_weightOne u₁ u₂ c₁ c₂ hc hu Wc f₀ κ⁻¹
        hcdisj hdiff hdiff' hODE' hgr hne
        (fun t ht => by simp only [hWc, Complex.ofReal_re]; exact hWf t ht) hWm

    have hfun : ∀ b : ZMod 2, (fun t : ℝ => (ρ * Wc t + (-1 : ℂ) ^ b.val * (ρ * Wc (-t))) / (t : ℂ)) =
        fun t : ℝ => ρ • ((D.W (ArchR.diagOne t) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-t))) / (t : ℂ)) := by
      intro b; funext t; simp only [hWc, Complex.ofReal_re, Complex.neg_re, smul_eq_mul]; ring
    have hP'eq : P' = RealArchParam.principal u₁ c₁ u₂ c₂ := by
      refine LanglandsTunnell.RealArchParam.eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire u₁ u₂ c₁ c₂ hc hu htype
        P' hP' ρ⁻¹ (inv_ne_zero hρ0) (D.zetaEntire 1 0 0) (D.zetaEntire_differentiable 1 0 0)
        (max (max (-u₁.re) (-u₂.re)) D.zeta_abscissa) fun s hs => ?_
      have hs1 : max (-u₁.re) (-u₂.re) < s.re := lt_of_le_of_lt (le_max_left _ _) hs
      have hs2 : D.zeta_abscissa < s.re := lt_of_le_of_lt (le_max_right _ _) hs
      have h1 := (hMel 0 s hs1).2
      rw [hfun 0, mellin_const_smul] at h1
      have h2 := (Ws1K5.zeta_unfold _ D 0 s hs2).2
      rw [h2, smul_eq_mul] at h1
      rw [← h1, ← mul_assoc, inv_mul_cancel₀ hρ0, one_mul]
    subst hP'eq

    set Wt : ℝ → ℂ := fun t => ρ * D.W (ArchR.diagOne t) with hWt
    have hWtc : ContinuousOn Wt {t : ℝ | t ≠ 0} := continuousOn_const.mul hWcont
    have hMel' : ∀ b : ZMod 2, ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
        MellinConvergent (fun t : ℝ => (Wt t + (-1 : ℂ) ^ b.val * Wt (-t)) / (t : ℂ)) s ∧
          mellin (fun t : ℝ => (Wt t + (-1 : ℂ) ^ b.val * Wt (-t)) / (t : ℂ)) s
            = ((RealArchParam.principal u₁ c₁ u₂ c₂).twist 0 b).archFactor s := by
      intro b
      refine ⟨max (-u₁.re) (-u₂.re), fun s hs => ?_⟩
      have hfun' : (fun t : ℝ => (ρ * Wc t + (-1 : ℂ) ^ b.val * (ρ * Wc (-t))) / (t : ℂ)) =
          fun t : ℝ => (Wt t + (-1 : ℂ) ^ b.val * Wt (-t)) / (t : ℂ) := by
        funext t; simp only [hWc, hWt, Complex.ofReal_re, Complex.neg_re]
      have h := hMel b s hs
      rw [hfun'] at h
      exact h
    refine ⟨ρ⁻¹, fun b τ hτ => ?_⟩
    have hK9 := LanglandsTunnell.add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_eq_archFactor u₁ u₂ c₁ c₂ Wt hWtc hMel' b τ hτ
    simp only [hWt] at hK9
    have : D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) =
        ρ⁻¹ * (ρ * D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * (ρ * D.W (ArchR.diagOne (-τ)))) := by
      field_simp
    rw [this, hK9]; ring

end S_LanglandsTunnell_CubicInduction_exists_archDatumR_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOne
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_archDatumR_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOne (solution)
