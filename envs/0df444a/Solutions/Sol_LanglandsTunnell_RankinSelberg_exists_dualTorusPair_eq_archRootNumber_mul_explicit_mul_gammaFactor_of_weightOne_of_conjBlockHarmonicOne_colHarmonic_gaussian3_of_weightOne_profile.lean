-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/4d5300a8-c647-50c4-a15e-5aad7821317e

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

import Theorems.Thm_LanglandsTunnell_RankinSelberg_dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3
import Theorems.Thm_LanglandsTunnell_Converse_integral_dualConfig_conjBlock_eq_two_pi_mul_integral_iwasawa_of_archWeightChar
import Theorems.Thm_LanglandsTunnell_Converse_integrable_dualConfig_iwasawaIntegrand_conjBlock
import Theorems.Thm_LanglandsTunnell_Converse_dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_conjBlock_of_re_gt
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_conjBlock_of_mulConvGaussian_sheets
import Theorems.Thm_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_conjBlock_eq_mul_prod_GammaR_of_twoSheetProfile
import Theorems.Thm_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_three_real
import Theorems.Thm_LanglandsTunnell_Converse_prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_one_real_one_complex
import Theorems.Thm_LanglandsTunnell_add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_eq_archFactor
import Mathlib.Analysis.MellinTransform
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

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

namespace Ws14K7dual
theorem re_bound (z : ℂ) : -‖z‖ ≤ z.re := (abs_le.1 (Complex.abs_re_le_norm z)).1
theorem re_le (z : ℂ) : z.re ≤ ‖z‖ := (abs_le.1 (Complex.abs_re_le_norm z)).2

theorem signEpsilon_pair {e₁ e₂ : ZMod 2} (hne : e₁ ≠ e₂) (b : ZMod 2) :
    signEpsilon (e₁ + b) * signEpsilon (e₂ + b) = Complex.I := by
  rcases Ws23K7kit2.zmod2_or_of_ne hne b with h0 | h0
  · have h2 : e₂ = b + 1 := by rw [← h0]; exact Ws23K7kit2.zmod2_eq_add_one_of_ne' hne
    rw [h0, h2, CharTwo.add_self_eq_zero, add_right_comm, CharTwo.add_self_eq_zero, zero_add, signEpsilon_zero,
      signEpsilon_one, one_mul]
  · have h2 : e₁ = b + 1 := by rw [← h0]; exact Ws23K7kit2.zmod2_eq_add_one_of_ne hne
    rw [h0, h2, CharTwo.add_self_eq_zero, add_right_comm, CharTwo.add_self_eq_zero, zero_add, signEpsilon_zero,
      signEpsilon_one, mul_one]
end Ws14K7dual

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
    (hk1 : k₀ = 1) (hn0 : n = 0)
    (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c₁ u₂ c₂) (hc : c₁ ≠ c₂)
    (ρ : ℂ)
    (hρ : ∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (u₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (u₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ))) :
    ∃ σ₂ : ℝ, ∀ s : ℂ, σ₂ < s.re →
            (∫ a₂ in Set.Ioi (0 : ℝ), ∫ a₁ : ℝ,
              if ha : a₁ ≠ 0 ∧ 0 < a₂ then
                let q : GL (Fin 2) ℝ := AutomorphicForm.SiegelCoordinates.upperUnit a₁ 0 a₂ ha.1 ha.2.ne'
                (((((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) * WA par₀ (w₀R * RSCarrier.transposeInv q)) * dualWhittakerFn3 (jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S) (archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) q)))) * (((|(Matrix.GeneralLinearGroup.det q : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2))) *
                  (((a₁ ^ 2)⁻¹ : ℝ) : ℂ)
              else 0)
              = ((archRootNumber K (archOfParamR K P) (archOfParamC K P) uR aR uC kC * (-1 : ℂ) ^ (P.centralSign).val * (-1 : ℂ) ^ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).card) * (((-1 : ℂ) ^ ((aR w₀ h₀).val + 1) * ((Real.pi : ℂ) / 2)) * ρ)) * (((twistedGammaR K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => -uR w hw) aR).map
                    fun x => Complex.Gammaℝ (s + 1 / 2 + x)).prod *
                  ((twistedGammaC K (fun w hw => (archOfParamR K P w hw).dual) (fun w hw => (archOfParamC K P w hw).dual)
                    (fun w hw => -uR w hw) aR (fun w hw => -uC w hw) (fun w hw => -kC w hw)).map
                    fun x => Complex.Gammaℂ (s + 1 / 2 + x)).prod) := by
  have hk : k₀ = (n : ℤ) + 1 := by omega
  obtain ⟨ν₁, ν₂, e₁, e₂, hP, hne⟩ := hPw1
  have hPc : P.centralExponent = ν₁ + ν₂ := by rw [hP]; rfl
  have hPs : P.centralSign = e₁ + e₂ := by rw [hP]; rfl
  have he : e₁ + e₂ = 1 := Ws23K7kit2.zmod2_sum_one_of_ne hne
  have ha' : ((a : ℚ) : ℝ) ≠ 0 := by exact_mod_cast ha
  have ha1' : ((a : ℚ) : ℝ) = -1 := by rw [ha1]; push_cast; ring
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

  have hkw : kw par₀ default = 1 := by
    have h := hkw1 par₀ default hreal ν₁ ν₂ e₁ e₂ hP
    have h1 : signShift (e₁ + par₀) + signShift (e₂ + par₀) = 1 := by
      rcases Ws23K7kit2.zmod2_or_of_ne hne par₀ with h0 | h0
      · have h2 : e₂ = par₀ + 1 := by rw [← h0]; exact Ws23K7kit2.zmod2_eq_add_one_of_ne' hne
        rw [h0, h2, CharTwo.add_self_eq_zero, add_right_comm, CharTwo.add_self_eq_zero, zero_add, signShift_zero,
          signShift_one, zero_add]
      · have h2 : e₁ = par₀ + 1 := by rw [← h0]; exact Ws23K7kit2.zmod2_eq_add_one_of_ne hne
        rw [h0, h2, CharTwo.add_self_eq_zero, add_right_comm, CharTwo.add_self_eq_zero, zero_add, signShift_zero,
          signShift_one, add_zero]
    rw [h1] at h
    exact_mod_cast h

  obtain ⟨σb, hB⟩ := LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_conjBlock_of_mulConvGaussian_sheets
    ν₁ ν₂ e₁ e₂ Wf hWc hK9 D ((a : ℚ) : ℝ) ha' (uR w₀ h₀) P.centralExponent (aR w₀ h₀) P.centralSign n
  obtain ⟨σe, hEv⟩ := LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_conjBlock_eq_mul_prod_GammaR_of_twoSheetProfile
    ν₁ ν₂ e₁ e₂ hne Wf hWc hK9 u₁ u₂ c₁ c₂ hc D hP₂eq ρ hρ ((a : ℚ) : ℝ) ha1' (uR w₀ h₀) P.centralExponent hPc (aR w₀ h₀) P.centralSign hPs n hn0
  have b₅ := Ws14K7dual.re_bound P.centralExponent
  have b₆ := Ws14K7dual.re_bound P₂.centralExponent
  have b₅' := Ws14K7dual.re_le P.centralExponent
  have b₆' := Ws14K7dual.re_le P₂.centralExponent
  have n₅ := norm_nonneg P.centralExponent
  have n₆ := norm_nonneg P₂.centralExponent
  refine ⟨max (max σb σe) (‖P.centralExponent‖ + ‖P₂.centralExponent‖ + 2), fun s hs => ?_⟩
  have hsb : σb < s.re := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hse : σe < s.re := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hsN : ‖P.centralExponent‖ + ‖P₂.centralExponent‖ + 2 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hw : -1 < (2 * s - P.centralExponent - P₂.centralExponent + n).re := by
    subst hn0
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re,
      zero_mul, sub_zero, Nat.cast_zero, Complex.zero_re, add_zero]
    linarith

  rw [LanglandsTunnell.RankinSelberg.dualTorusPair_eq_setIntegral_dualConfig_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3
    K _hdeg μ _hμ _hns uR aR uC kC huR huC ω hω E hE a ha ha1 aInf haInf psiInf hpsiInf ν_add hν_add ν_mul P _hP₁ kw Wr WA hkw1 hkw2 hWr1 hWr2 hWr3 hWr4 hWAN hWAZ hWAK hWAt hWAc w₀R hw₀R w₀ h₀ P₂ hP₂ D k₀ hDW hDE hDnz hk₀min ⟨ν₁, ν₂, e₁, e₂, hP, hne⟩ hk₀ n hn par₀ S hS s]

  have hKK := LanglandsTunnell.Converse.dualTorusPair_iwasawa_eq_const_mul_integral_torusTriple_conjBlock_of_re_gt D Wf ((a : ℚ) : ℝ) (uR w₀ h₀) P.centralExponent (aR w₀ h₀) P.centralSign
    (kw par₀ default) n s hw
    (fun a₁ ha₁ a₂ ha₂ => LanglandsTunnell.Converse.integrable_dualConfig_iwasawaIntegrand_conjBlock D ((a : ℚ) : ℝ) ha' (uR w₀ h₀ + 2) (aR w₀ h₀) a₁ a₂ ha₁ ha₂ n)
    (hB s hsb).1
  simp only [Complex.ofReal_ratCast] at hKK
  refine Eq.trans ?_ (hKK.trans ?_)
  · refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro a₂ _ha₂
    beta_reduce
    refine integral_congr_ae (ae_of_all _ fun a₁ => ?_)
    beta_reduce
    by_cases hq : a₁ ≠ 0 ∧ 0 < a₂
    · rw [dif_pos hq, dif_pos hq]
      have hI := LanglandsTunnell.Converse.integral_dualConfig_conjBlock_eq_two_pi_mul_integral_iwasawa_of_archWeightChar D k₀ n hk hDW ((a : ℚ) : ℝ) ha' (uR w₀ h₀ + 2) (aR w₀ h₀) a₁ a₂ hq.1 hq.2
        (LanglandsTunnell.Converse.integrable_dualConfig_iwasawaIntegrand_conjBlock D ((a : ℚ) : ℝ) ha' (uR w₀ h₀ + 2) (aR w₀ h₀) a₁ a₂ hq.1 hq.2 n)
      simp only [Complex.ofReal_ratCast] at hI
      rw [hI]
      simp only [hWf]
      push_cast
      ring
    · rw [dif_neg hq, dif_neg hq]
  ·
    have hE := hEv s hse
    simp only [Complex.ofReal_ratCast] at hE
    have hv : (e₁ + e₂).val = 1 := by rw [he]; rfl
    have hI3 : Complex.I * (Complex.I * Complex.I) = -Complex.I := by rw [Complex.I_mul_I]; ring
    have h2π : ((2 * Real.pi : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by push_cast; ring
    rcases hP₂ with ⟨w₁, w₂, h₁, h₂, h01, h02, h12, hall, hP₂'⟩ | ⟨wC, hCx, hall, hbr⟩
    · have hinj : u₁ = uR w₁ h₁ ∧ c₁ = aR w₁ h₁ ∧ u₂ = uR w₂ h₂ ∧ c₂ = aR w₂ h₂ := by
        rw [hP₂eq] at hP₂'
        injection hP₂' with i1 i2 i3 i4
        exact ⟨i1, i2, i3, i4⟩
      obtain ⟨hR, hC, hEps⟩ := LanglandsTunnell.Converse.prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_three_real
        K w₀ w₁ w₂ h₀ h₁ h₂ h01 h02 h12 hall uR aR uC kC P ν₁ ν₂ e₁ e₂ hP s
      rw [hR, hC, hEps, mul_one, hkw, ← hinj.1, ← hinj.2.1, ← hinj.2.2.1, ← hinj.2.2.2,
        Ws14K7dual.signEpsilon_pair hne (aR w₀ h₀), Ws14K7dual.signEpsilon_pair hne c₁, Ws14K7dual.signEpsilon_pair hne c₂,
        hv, zpow_one, h2π, hI3]
      linear_combination ((Real.pi : ℂ) * Complex.I) * hE
    · rcases hbr with ⟨hkne, hd⟩ | ⟨hk0, hpr⟩
      · exfalso; rw [hP₂eq] at hd; cases hd
      · have hinj : u₁ = uC wC hCx ∧ c₁ = 0 ∧ u₂ = uC wC hCx ∧ c₂ = 1 := by
          rw [hP₂eq] at hpr
          injection hpr with i1 i2 i3 i4
          exact ⟨i1, i2, i3, i4⟩
        obtain ⟨hR, hC, hEps⟩ := LanglandsTunnell.Converse.prod_map_GammaR_twistedGammaR_dual_and_archRootNumber_one_real_one_complex
          K w₀ wC h₀ hCx hall uR aR uC kC P ν₁ ν₂ e₁ e₂ hP s
        rw [hR, hC, hEps, hkw, Ws14K7dual.signEpsilon_pair hne (aR w₀ h₀), hv, zpow_one, h2π, hk0] at ⊢
        rw [hinj.1, hinj.2.1, hinj.2.2.1, hinj.2.2.2] at hE
        simp only [add_zero] at hE
        simp only [Int.natAbs_zero, Nat.cast_zero, zero_div, add_zero, pow_zero, one_mul, mul_one]
        have hL1 := RealArchParam.Gammaℝ_signShift_mul (s + 1 / 2 + (-ν₁ + -uC wC hCx)) e₁
        have hL2 := RealArchParam.Gammaℝ_signShift_mul (s + 1 / 2 + (-ν₂ + -uC wC hCx)) e₂
        rw [← hL1, ← hL2]
        ring_nf
        ring_nf at hE
        linear_combination ((Real.pi : ℂ) * Complex.I) * hE

end S_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_exists_dualTorusPair_eq_archRootNumber_mul_explicit_mul_gammaFactor_of_weightOne_of_conjBlockHarmonicOne_colHarmonic_gaussian3_of_weightOne_profile (solution)
