-- Prove2me | solution 1 for LanglandsTunnell.archOccursInClassOf_archWeightChar_zero_archCasimirAt_apply_mul_J_eq_neg_one_pow_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/ac728f32-0a94-54ef-822a-f6d6412c5e23

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_LanglandsTunnell_Converse_continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq
import Theorems.Thm_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot
import Theorems.Thm_AutomorphicForm_exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq
import Theorems.Thm_AutomorphicForm_exists_forall_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_of_mem_archCutSubmodule_of_coversModCentre
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_archOccursInClassOf_archWeightChar_zero_archCasimirAt_apply_mul_J_eq_neg_one_pow_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace Ws47
namespace SIGN

theorem whittakerCoefficient_translate (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (h g : AdelicGL2 (𝓞 ℚ) ℚ) :
    whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ (fun y => φ (y * h)) 1 g = whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ φ 1 (g * h) := by
  letI := (productionPinsGeneral ℚ).nS
  simp only [whittakerCoefficient, mul_assoc]

theorem whittakerIntegrand_integrable (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : Continuous φ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    MeasureTheory.Integrable
      (fun x : AdeleRing (𝓞 ℚ) ℚ => φ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x)))
      (productionPinsGeneral ℚ).ν := by
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 ℚ) ℚ
  have hcont : Continuous (fun x : AdeleRing (𝓞 ℚ) ℚ => φ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x))) :=
    (hφ.comp (AutomorphicForm.continuous_unipotentGL2.mul continuous_const)).mul
      (hψ.comp ((continuous_const.mul continuous_id).neg))
  obtain ⟨C, hC, hsub⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset ℚ
  show MeasureTheory.Integrable _ (ProbabilityTheory.cond (NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ) (adelicBox ℚ))
  rw [ProbabilityTheory.cond]
  refine MeasureTheory.Integrable.smul_measure ?_ (ENNReal.inv_ne_top.2 (NumberField.AdelicBox.adelicAddHaar_adelicBox_pos ℚ).ne')
  exact (hcont.continuousOn.integrableOn_compact hC).mono_set hsub

theorem whittakerCoefficient_add_smul (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : Continuous ψ)
    (φ₁ φ₂ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (h₁ : Continuous φ₁) (h₂ : Continuous φ₂) (ε : ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ (fun y => φ₁ y + ε * φ₂ y) 1 g
      = whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ φ₁ 1 g + ε * whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ φ₂ 1 g := by
  letI := (productionPinsGeneral ℚ).nS
  have h₁' := whittakerIntegrand_integrable ψ hψ φ₁ h₁ g
  have h₂' := whittakerIntegrand_integrable ψ hψ φ₂ h₂ g
  simp only [whittakerCoefficient]
  have hfun : (fun x : AdeleRing (𝓞 ℚ) ℚ => (φ₁ (unipotentGL2 x * g) + ε * φ₂ (unipotentGL2 x * g))
        * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x)))
      = fun x => φ₁ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x))
          + ε * (φ₂ (unipotentGL2 x * g) * ψ (-(algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) 1 * x))) := by
    funext x; ring
  rw [hfun, MeasureTheory.integral_add h₁' (h₂'.const_mul ε), MeasureTheory.integral_const_mul]

theorem exists_archTypeFamily_mem (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ) :
    ∃ tys : ArchTypeFamily ℚ, φ ∈ archCutSubmodule ℚ tys := by
  refine ⟨ArchTypeFamily.ofChar ℚ fun w' => (Subsingleton.elim Rat.infinitePlace w') ▸
    ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))), ?_⟩
  rw [mem_archCutSubmodule_ofChar_iff]
  intro w'
  obtain rfl : Rat.infinitePlace = w' := Subsingleton.elim _ _
  exact hφ

private theorem _root_.Ws47.SIGN.mem_isotypicCuspSubmodule (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Ψ : HeckeEigensystem ℚ ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Ψ φ) :
    φ ∈ isotypicCuspSubmodule ℚ (productionPinsGeneral ℚ) ξ N S Ψ := by
  exact hφ.mem_isotypicCuspSubmodule

p2m_export "Ws47.SIGN" "mem_isotypicCuspSubmodule"

theorem exists_occ_std_typed
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hWF : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
          (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
              (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                archW (fun _ _ => P) archC dR dC g * z))
    (hWT : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ)))
    (hDE : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchCasimir.IsCasimirEigen (dR w hw))
    (hnv : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dR w hw).W g ≠ 0)
    (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)))
    (htype : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1))
    (hP0 : (RealArchParam.centralExponent P).re = 0)
    (Θ : HeckeEigensystem ℚ ℂ) (R₁ : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Θ.toRawCentral) (hR₁ : Continuous R₁.toFun)
    (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) (z : ℂ)
    (hne : ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) R₁.toFun 1 g ≠ 0)
    (hfib : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) R₁.toFun 1 g =
        (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          archW (fun _ _ => P) archC dR dC g * z) :
    ∃ n : ℤ, ArchOccursInClassOf ℚ (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) Θ
      (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ ∧
        IsArchSmoothAt Rat.isReal_infinitePlace φ ∧ archCasimirAt Rat.isReal_infinitePlace φ = (laplaceEigenvalue P) • φ) := by
  obtain ⟨hWc, hWfin, hWs, hWΩ⟩ :=
    LanglandsTunnell.Converse.continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen ℚ
      (fun _ _ => P) archC dR dC Rat.infinitePlace Rat.isReal_infinitePlace (hDE _ _)
  exact LanglandsTunnell.exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq ℚ
    (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num)
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat Θ Rat.infinitePlace Rat.isReal_infinitePlace
    P (archW (fun _ _ => P) archC dR dC) hWc hWfin hWs hWΩ ⟨Θ, TranslateSpanOccurrence.agrees_refl Θ, R₁, hR₁, g₀, hne, z, hfib⟩

theorem occurs_window_of_isIsotypic_general
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hc : 0 < c) (hd₁ : 0 < d₁)
    (Φ Θ : HeckeEigensystem ℚ ℂ) (hΘ : Θ.AgreesAwayFromFinite Φ)
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hx : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ Θ.level S Θ x) (hx0 : x ≠ 0)
    (Q : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) → Prop) (hQ : Q x) :
    ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ Q := by
  classical

  have h12 := AutomorphicForm.isIsotypicCuspFormAt_centreCutSiegelSetAmple_of_isIsotypicCuspFormAt_of_coversModCentre ℚ
    (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num)
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat ξ Θ.level S Θ x hx c u d₁ d₂ 1 le_rfl hc hd₁ T
  have e : (⋃ y ∈ T, (· * y) '' centreCutSiegelSetAmple ℚ c u d₁ d₂ 1) = ⋃ y ∈ T, (· * y) '' centreCutSiegelSet ℚ c u d₁ d₂ := by
    rw [AutomorphicForm.WindowedSiegel.centreCutSiegelSetAmple_eq_of_subsingleton (F := ℚ) le_rfl]
  rw [e] at h12
  obtain ⟨Ψ', R, -, ha, hb, hRfun, -, -⟩ :=
    AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot ℚ
      (productionPinsOf ℚ (⋃ y ∈ T, (· * y) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
      ξ Θ.level Θ.level_ne_bot S Θ x h12 hx0
  have hag : Ψ'.AgreesAwayFromFinite Φ :=
    TranslateSpanOccurrence.agrees_trans ⟨∅, fun v _ => ⟨ha v, hb v⟩⟩ hΘ
  refine ⟨Ψ', hag, R, ?_, ?_⟩
  · show Continuous R.toFun
    rw [hRfun]; exact hx.continuous
  · rw [hRfun]; exact hQ

end Ws47.SIGN

noncomputable section

namespace Ws47
namespace SIGN

namespace JS

section ConvLinear

open MeasureTheory

variable {K : Type} [Field K] [NumberField K]

private theorem cv_integrable_conv_integrand {φ α : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (hαc : Continuous α)
    (hαs : HasCompactSupport α) (g : AdelicGL2 (𝓞 K) K) :
    letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
    Integrable (fun y => φ (g * y) * α y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  refine ((hφ.comp (continuous_const.mul continuous_id)).mul hαc).integrable_of_hasCompactSupport (hαs.mono ?_)
  intro y hy
  simp only [Function.mem_support] at hy ⊢
  intro h0
  exact hy (by show φ (g * y) * α y = 0; rw [h0, mul_zero])

private theorem cv_rightConv_add_right {φ α₁ α₂ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (hα₁c : Continuous α₁)
    (hα₁s : HasCompactSupport α₁) (hα₂c : Continuous α₂) (hα₂s : HasCompactSupport α₂) :
    rightConv K φ (α₁ + α₂) = rightConv K φ α₁ + rightConv K φ α₂ := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  funext g
  show (∫ y, φ (g * y) * (α₁ + α₂) y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
    (∫ y, φ (g * y) * α₁ y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) +
      ∫ y, φ (g * y) * α₂ y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  rw [← integral_add (cv_integrable_conv_integrand hφ hα₁c hα₁s g) (cv_integrable_conv_integrand hφ hα₂c hα₂s g)]
  congr 1
  funext y
  rw [Pi.add_apply, mul_add]

private theorem cv_rightConv_smul_right (φ α : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) :
    rightConv K φ (c • α) = c • rightConv K φ α := by
  letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  funext g
  show (∫ y, φ (g * y) * (c • α) y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) =
    c * ∫ y, φ (g * y) * α y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)
  rw [← integral_const_mul]
  congr 1
  funext y
  rw [Pi.smul_apply, smul_eq_mul]
  ring

end ConvLinear

section ArchCut

variable {K : Type} [Field K] [NumberField K]

private theorem mem_archCutSubmodule_ofChar_of_forall
    (χ : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion →* ℂˣ) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (h : ∀ w : InfinitePlace K, f ∈ archTypeSubmoduleAt K w (ArchRepAt.ofChar K (χ w))) :
    f ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ) := by
  show f ∈ ⨅ w : InfinitePlace K, ⨆ _ : Fin 1, archTypeSubmoduleAt K w (ArchRepAt.ofChar K (χ w))
  simp only [iSup_const, Submodule.mem_iInf]
  exact h

private theorem forall_of_mem_archCutSubmodule_ofChar
    (χ : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion →* ℂˣ) {f : AdelicGL2 (𝓞 K) K → ℂ}
    (h : f ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ)) (w : InfinitePlace K) :
    f ∈ archTypeSubmoduleAt K w (ArchRepAt.ofChar K (χ w)) := by
  have h' : f ∈ ⨅ w : InfinitePlace K, ⨆ _ : Fin 1, archTypeSubmoduleAt K w (ArchRepAt.ofChar K (χ w)) := h
  simp only [iSup_const, Submodule.mem_iInf] at h'
  exact h' w

private theorem rightConv_mem_archCutSubmodule_ofChar
    (χ : ∀ w : InfinitePlace K, rowIsometrySubgroup₀ w.Completion →* ℂˣ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    {t : AdelicGL2 (𝓞 K) K → ℂ} (ht : IsArchBiFinite K (ArchTypeFamily.ofChar K χ) t) :
    rightConv K φ t ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χ) :=
  mem_archCutSubmodule_ofChar_of_forall χ fun w =>
    rightConv_mem_archTypeSubmoduleAt_ofChar K w (χ w) φ t (forall_of_mem_archCutSubmodule_ofChar χ ht.1 w)

end ArchCut

end JS

namespace JS
namespace ReproducingClosure

p2m_open "AutomorphicForm NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicLevel IsDedekindDomain Filter Topology"
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

private theorem mem_of_tendsto_of_finiteDimensional {X : Type} (E : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ E]
    (L : Submodule ℂ (X → ℂ)) (hLE : L ≤ E) (u : ℕ → X → ℂ) (hu : ∀ n, u n ∈ L) (f : X → ℂ)
    (hlim : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (f x))) : f ∈ L := by
  haveI : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLE
  have ht : Tendsto u atTop (𝓝 f) := tendsto_pi_nhds.2 hlim
  exact L.closed_of_finiteDimensional.mem_of_tendsto ht (Eventually.of_forall hu)

private theorem hasCompactSupport_const_smul {X : Type} [TopologicalSpace X] (c : ℂ) {f : X → ℂ}
    (hf : HasCompactSupport f) : HasCompactSupport (c • f) :=
  hf.comp_left (g := fun z : ℂ => c * z) (mul_zero c)

private theorem isArchTestFactor_add {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (ha : IsArchTestFactor K fa)
    (hb : IsArchTestFactor K fb) : IsArchTestFactor K (fa + fb) := by
  obtain ⟨⟨Φa, hΦa, hfa⟩, hsa⟩ := ha
  obtain ⟨⟨Φb, hΦb, hfb⟩, hsb⟩ := hb
  refine ⟨⟨Φa + Φb, hΦa.add hΦb, fun g => ?_⟩, hsa.add hsb⟩
  simp only [Pi.add_apply, hfa g, hfb g]

private theorem isArchTestFactor_smul (c : ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (ha : IsArchTestFactor K fa) : IsArchTestFactor K (c • fa) := by
  obtain ⟨⟨Φa, hΦa, hfa⟩, hsa⟩ := ha
  refine ⟨⟨c • Φa, hΦa.const_smul c, fun g => ?_⟩, hasCompactSupport_const_smul c hsa⟩
  simp only [Pi.smul_apply, hfa g]

section

variable (Q : (GL (Fin 2) (InfiniteAdeleRing K) → ℂ) → Prop) (hQ0 : Q 0)
  (hQadd : ∀ {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}, Q fa → Q fb → Q (fa + fb))
  (hQsmul : ∀ (c : ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}, Q fa → Q (c • fa))

include hQ0 hQadd hQsmul in

private def typedTestFactors : Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing K) → ℂ) where
  carrier := {fa | IsArchTestFactor K fa ∧ Q fa}
  zero_mem' := ⟨isArchTestFactor_zero K, hQ0⟩
  add_mem' := fun ha hb => ⟨isArchTestFactor_add ha.1 hb.1, hQadd ha.2 hb.2⟩
  smul_mem' := fun c _ ha => ⟨isArchTestFactor_smul c ha.1, hQsmul c ha.2⟩

include hQ0 hQadd hQsmul in
private theorem mem_typedTestFactors {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} :
    fa ∈ typedTestFactors Q hQ0 hQadd hQsmul ↔ IsArchTestFactor K fa ∧ Q fa :=
  Iff.rfl

end

private def tensor (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) :
    AdelicGL2 (𝓞 K) K → ℂ :=
  fun g => fa (glArch (𝓞 K) K g) * ff (glFin (𝓞 K) K g)

private theorem tensor_add (fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) :
    tensor (fa + fb) ff = tensor fa ff + tensor fb ff := by
  funext g
  simp only [tensor, Pi.add_apply]
  ring

private theorem tensor_smul (c : ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ) : tensor (c • fa) ff = c • tensor fa ff := by
  funext g
  simp only [tensor, Pi.smul_apply, smul_eq_mul]
  ring

private theorem isFactorizableTestFn_tensor {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (hfa : IsArchTestFactor K fa) (hff : IsFinTestFactor K ff) :
    IsFactorizableTestFn K (tensor fa ff) :=
  ⟨fa, ff, hfa, hff, fun _ => rfl⟩

section

variable (Q : (GL (Fin 2) (InfiniteAdeleRing K) → ℂ) → Prop) (hQ0 : Q 0)
  (hQadd : ∀ {fa fb : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}, Q fa → Q fb → Q (fa + fb))
  (hQsmul : ∀ (c : ℂ) {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}, Q fa → Q (c • fa))
  (f : AdelicGL2 (𝓞 K) K → ℂ) {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (hff : IsFinTestFactor K ff)
  (hadd : ∀ γ₁ γ₂ : AdelicGL2 (𝓞 K) K → ℂ, Continuous γ₁ → HasCompactSupport γ₁ → Continuous γ₂ →
    HasCompactSupport γ₂ → rightConv K f (γ₁ + γ₂) = rightConv K f γ₁ + rightConv K f γ₂)
  (hsmul : ∀ (γ : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ), rightConv K f (c • γ) = c • rightConv K f γ)

include Q hQ0 hQadd hQsmul f hff hadd

private theorem rightConv_tensor_add (a b : typedTestFactors Q hQ0 hQadd hQsmul) :
    rightConv K f (tensor ((a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) + (b : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)) ff)
      = rightConv K f (tensor a ff) + rightConv K f (tensor b ff) := by
  have h1 := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _
    (isFactorizableTestFn_tensor ((mem_typedTestFactors Q hQ0 hQadd hQsmul).1 a.2).1 hff)
  have h2 := continuous_and_hasCompactSupport_of_isFactorizableTestFn K _
    (isFactorizableTestFn_tensor ((mem_typedTestFactors Q hQ0 hQadd hQsmul).1 b.2).1 hff)
  rw [tensor_add, hadd _ _ h1.1 h1.2 h2.1 h2.2]

private def convMap : typedTestFactors Q hQ0 hQadd hQsmul →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) where
  toFun a := rightConv K f (tensor (a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) ff)
  map_add' a b := by
    show rightConv K f (tensor ((a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        + (b : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)) ff) = rightConv K f (tensor a ff) + rightConv K f (tensor b ff)
    exact rightConv_tensor_add Q hQ0 hQadd hQsmul f hff hadd a b
  map_smul' c a := by
    show rightConv K f (tensor (c • (a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)) ff)
      = c • rightConv K f (tensor (a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) ff)
    rw [tensor_smul, hsmul]

private theorem convMap_apply (a : typedTestFactors Q hQ0 hQadd hQsmul) :
    convMap Q hQ0 hQadd hQsmul f hff hadd hsmul a
      = rightConv K f (tensor (a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) ff) :=
  rfl

include hsmul in
private theorem exists_isFactorizableTestFn_rightConv_eq (E : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    [FiniteDimensional ℂ E]
    (hmem : ∀ a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K a → Q a → rightConv K f (tensor a ff) ∈ E)
    (fa : ℕ → GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : ∀ n, IsArchTestFactor K (fa n)) (hfaQ : ∀ n, Q (fa n))
    (hlim : ∀ g : AdelicGL2 (𝓞 K) K, Tendsto (fun n => rightConv K f (tensor (fa n) ff) g) atTop (𝓝 (f g))) :
    ∃ a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K a ∧ Q a ∧ rightConv K f (tensor a ff) = f := by
  set L := LinearMap.range (convMap Q hQ0 hQadd hQsmul f hff hadd hsmul) with hL
  have hLE : L ≤ E := by
    intro x hx
    obtain ⟨a, ha⟩ := LinearMap.mem_range.1 hx
    rw [← ha, convMap_apply]
    obtain ⟨ha1, ha2⟩ := (mem_typedTestFactors Q hQ0 hQadd hQsmul).1 a.2
    exact hmem _ ha1 ha2
  have hfL : f ∈ L :=
    mem_of_tendsto_of_finiteDimensional E L hLE (fun n => rightConv K f (tensor (fa n) ff))
      (fun n => ⟨⟨fa n, (mem_typedTestFactors Q hQ0 hQadd hQsmul).2 ⟨hfa n, hfaQ n⟩⟩, rfl⟩) f hlim
  obtain ⟨a, ha⟩ := LinearMap.mem_range.1 hfL
  obtain ⟨ha1, ha2⟩ := (mem_typedTestFactors Q hQ0 hQadd hQsmul).1 a.2
  exact ⟨(a : GL (Fin 2) (InfiniteAdeleRing K) → ℂ), ha1, ha2, ha⟩

end

end JS.ReproducingClosure

namespace JS

section WtFam

variable {w : InfinitePlace ℚ} (hw : w.IsReal)

private def wtFam (m : ℤ) : ∀ w' : InfinitePlace ℚ, rowIsometrySubgroup₀ w'.Completion →* ℂˣ :=
  fun w' => (Subsingleton.elim w w') ▸ archWeightCharAt hw m

private theorem mem_archCutSubmodule_wtFam_iff (m : ℤ) (f : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    f ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ (wtFam hw m)) ↔
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw m) f := by
  rw [mem_archCutSubmodule_ofChar_iff]
  constructor
  · intro h
    exact h w
  · intro h w'
    obtain rfl : w = w' := Subsingleton.elim w w'
    exact h

end WtFam

private theorem exists_finset_dvd_level (Φ : HeckeEigensystem ℚ ℂ) : ∃ SK : Finset (HeightOneSpectrum (𝓞 ℚ)),
    ∀ p : HeightOneSpectrum (𝓞 ℚ), p.asIdeal ∣ Φ.level → p ∈ SK := by
  have hfin : {p : HeightOneSpectrum (𝓞 ℚ) | p.asIdeal ∣ Φ.level}.Finite := Ideal.finite_factors Φ.level_ne_bot
  exact ⟨hfin.toFinset, fun p hp => hfin.mem_toFinset.2 hp⟩

private theorem ringHom_eq_id (f : 𝓞 ℚ →+* 𝓞 ℚ) : f = RingHom.id (𝓞 ℚ) := by
  have h : (Rat.ringOfIntegersEquiv.toRingHom.comp f).comp Rat.ringOfIntegersEquiv.symm.toRingHom
      = Rat.ringOfIntegersEquiv.toRingHom.comp Rat.ringOfIntegersEquiv.symm.toRingHom := Subsingleton.elim _ _
  ext x
  have hx := congrArg (fun g : ℤ →+* ℤ => g (Rat.ringOfIntegersEquiv x)) h
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
    at hx
  simpa using Rat.ringOfIntegersEquiv.injective hx

private theorem ideal_map_self (f : 𝓞 ℚ →+* 𝓞 ℚ) (N : Ideal (𝓞 ℚ)) : Ideal.map f N = N := by
  rw [ringHom_eq_id f, Ideal.map_id]

private theorem exists_reproducing_window_tys
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Ψ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Ψ.toRawCentral)
    (hR : Continuous R.toFun)
    (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (harch : R.toFun ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ)) :
    ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, α x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ,
          glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Ψ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k) ∧
      rightConv ℚ R.toFun α = R.toFun := by
  classical
  let tys := ArchTypeFamily.ofChar ℚ χ
  let E : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :=
    isotypicCuspSubmodule ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
          (adelicBox ℚ))
        R.centralChar Ψ.level R.exceptionalSet Ψ ⊓ archCutSubmodule ℚ tys
  haveI : FiniteDimensional ℂ E :=
    AutomorphicForm.finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule ℚ c u d₁ d₂ T hd hcov
      R.centralChar Ψ.level Ψ.level_ne_bot R.exceptionalSet tys Ψ
  have hiso := R.isIsotypicCuspFormAt hR
  obtain ⟨SK, hNS⟩ := exists_finset_dvd_level Ψ
  obtain ⟨ff, fa, hff, hffs, hfa, hbi, hlim⟩ :=
    AutomorphicForm.exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
      ℚ ℚ Ψ.level SK hNS tys R.toFun hR
      (by rw [ideal_map_self]; exact fun g k hk => hiso.level_invariant g k hk) harch
  rw [ideal_map_self] at hffs hbi
  obtain ⟨a, ha, -, hrepro⟩ := ReproducingClosure.exists_isFactorizableTestFn_rightConv_eq
    (K := ℚ)
    (fun a => IsArchBiFinite ℚ tys (ReproducingClosure.tensor a ff))
    (by
      show IsArchBiFinite ℚ tys (ReproducingClosure.tensor 0 ff)
      have h0 : ReproducingClosure.tensor (0 : GL (Fin 2) (InfiniteAdeleRing ℚ) → ℂ) ff = 0 :=
        funext fun g => by simp [ReproducingClosure.tensor]
      rw [h0]
      exact isArchBiFinite_zero ℚ tys)
    (fun {fa'} {fb'} ha hb => by
      show IsArchBiFinite ℚ tys (ReproducingClosure.tensor (fa' + fb') ff)
      rw [ReproducingClosure.tensor_add fa' fb' ff]
      exact ⟨(archCutSubmodule ℚ tys).add_mem ha.1 hb.1, (archDualCutSubmodule ℚ tys).add_mem ha.2 hb.2⟩)
    (fun c' {fa'} ha => by
      show IsArchBiFinite ℚ tys (ReproducingClosure.tensor (c' • fa') ff)
      rw [ReproducingClosure.tensor_smul c' fa' ff]
      exact ⟨(archCutSubmodule ℚ tys).smul_mem c' ha.1, (archDualCutSubmodule ℚ tys).smul_mem c' ha.2⟩)
    R.toFun hff
    (fun γ₁ γ₂ h₁c h₁s h₂c h₂s => cv_rightConv_add_right hR h₁c h₁s h₂c h₂s)
    (fun γ c' => cv_rightConv_smul_right R.toFun γ c')
    E
    (fun a ha hQa => by
      have hfact : IsFactorizableTestFn ℚ (ReproducingClosure.tensor a ff) :=
        ReproducingClosure.isFactorizableTestFn_tensor ha hff
      have hsupp : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, ReproducingClosure.tensor a ff x ≠ 0 → ∃ a' k : AdelicGL2 (𝓞 ℚ) ℚ,
          glFin (𝓞 ℚ) ℚ a' = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Ψ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a' * k :=
        fun x hx => hffs x (right_ne_zero_of_mul hx)
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · exact (AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
          c u d₁ d₂ T hd hcov Ψ R hR _ hfact hsupp).mem_isotypicCuspSubmodule
      · exact rightConv_mem_archCutSubmodule_ofChar χ R.toFun hQa)
    fa hfa (fun k => (hbi k).isArchBiFinite) (fun g => hlim g)
  exact ⟨ReproducingClosure.tensor a ff, ReproducingClosure.isFactorizableTestFn_tensor ha hff,
    fun x hx => hffs x (right_ne_zero_of_mul hx), hrepro⟩

end JS

theorem isIsotypicCuspFormAt_congr' {pins : CarrierPins ℚ} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 ℚ)}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Ψ Ψ' : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (hab : ∀ v, v ∉ S → Ψ.a v = Ψ'.a v ∧ Ψ.b v = Ψ'.b v) (h : IsIsotypicCuspFormAt ℚ pins ξ N S Ψ φ) :
    IsIsotypicCuspFormAt ℚ pins ξ N S Ψ' φ where
  smoothCusp := h.smoothCusp
  continuous := h.continuous
  level_invariant := h.level_invariant
  hecke_eigen := fun v hv => (hab v hv).1 ▸ h.hecke_eigen v hv
  central_eigen := fun v hv g => by
    rw [h.central_eigen v hv g, HeckeEigensystem.toRawCentral_b, HeckeEigensystem.toRawCentral_b, (hab v hv).2]

theorem isIsotypicCuspFormAt_zero_of {pins : CarrierPins ℚ} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 ℚ)}
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {Ψ : HeckeEigensystem ℚ ℂ} {φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ}
    (h : IsIsotypicCuspFormAt ℚ pins ξ N S Ψ φ) :
    IsIsotypicCuspFormAt ℚ pins ξ N S Ψ (fun _ => 0) where
  smoothCusp := isSmoothCuspAutomorphicFnAt_zero ℚ pins ξ
  continuous := continuous_const
  level_invariant := fun _ _ _ => rfl
  hecke_eigen := fun v hv => by
    obtain ⟨reps, hsys, -⟩ := h.hecke_eigen v hv
    exact ⟨reps, hsys, fun g => by simp [SmoothCusp.heckeCosetSum]⟩
  central_eigen := fun v hv g => by simp

theorem exists_ofChar_mem (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ) :
    ∃ χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ, φ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
  refine ⟨fun w' => (Subsingleton.elim Rat.infinitePlace w') ▸
    ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))), ?_⟩
  rw [mem_archCutSubmodule_ofChar_iff]
  intro w'
  obtain rfl : Rat.infinitePlace = w' := Subsingleton.elim _ _
  exact hφ

theorem isIsotypicCuspFormAt_Jsym (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Ψ : HeckeEigensystem ℚ ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Ψ φ)
    (χ : ∀ w : InfinitePlace ℚ, rowIsometrySubgroup₀ w.Completion →* ℂˣ) (hcut : φ ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ)) (ε : ℂ) :
    IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Ψ
      (fun g => φ g + ε * φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)) := by
  classical
  by_cases h0 : φ = 0
  · subst h0
    convert hφ using 1
    funext g; simp

  obtain ⟨Ψ', R, hlev, ha, hb, hRfun, hRcc, hRS⟩ :=
    AutomorphicForm.IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot ℚ (productionPinsGeneral ℚ) ξ N hN
      S Ψ φ hφ h0
  have hR : Continuous R.toFun := by rw [hRfun]; exact hφ.continuous
  have harch : R.toFun ∈ archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by rw [hRfun]; exact hcut

  obtain ⟨α, hα, hαs, hrep⟩ := JS.exists_reproducing_window_tys (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num)
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat Ψ' R hR χ harch
  have hrepφ : rightConv ℚ φ α = φ := by rw [← hRfun]; exact hrep

  have hJfin : glFin (𝓞 ℚ) ℚ (archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) = 1 := glFin_adelicArchGLIncl ℚ _
  have htrans : (fun g => φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J))
      = rightConv ℚ φ (fun y => α ((archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)⁻¹ * y)) := by
    funext g
    calc φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)
        = rightConv ℚ φ α (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) := by rw [hrepφ]
      _ = _ := AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply ℚ φ α g _
  have ht : IsFactorizableTestFn ℚ (fun y => α ((archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)⁻¹ * y)) :=
    AutomorphicForm.isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn ℚ α hα _
  have hts : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, (fun y => α ((archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)⁻¹ * y)) x ≠ 0 →
      ∃ a k : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ a = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Ψ'.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a * k := by
    intro y hy
    obtain ⟨a, k, ha1, hk, hak⟩ := hαs _ hy
    refine ⟨archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J * a, k, by rw [map_mul, hJfin, ha1, one_mul], hk, ?_⟩
    rw [mul_assoc, ← hak, mul_inv_cancel_left]

  have hJiso' := AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
    (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num)
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat Ψ' R hR _ ht hts
  rw [hRfun, hRcc, hRS, hlev, ← htrans] at hJiso'
  have hJiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Ψ
      (fun g => φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)) :=
    isIsotypicCuspFormAt_congr' (fun v _ => ⟨ha v, hb v⟩) hJiso'

  by_cases hs : (fun g => φ g + ε * φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)) = 0
  · rw [hs]
    exact isIsotypicCuspFormAt_zero_of hφ
  · have hmem : (fun g => φ g + ε * φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J))
        ∈ isotypicCuspSubmodule ℚ (productionPinsGeneral ℚ) ξ N S Ψ := by
      have hsum : (fun g => φ g + ε * φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J))
          = φ + ε • (fun g => φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)) := by
        funext g; simp [smul_eq_mul]
      rw [hsum]
      exact Submodule.add_mem _ hφ.mem_isotypicCuspSubmodule (Submodule.smul_mem _ ε hJiso.mem_isotypicCuspSubmodule)
    exact AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule ℚ _ _ _ ξ N S Ψ _ hmem hs

end Ws47.SIGN

end

namespace Ws47
namespace PROJK
open NumberField.AdelicVolume

theorem archComponent_glArch_adelicArchGLInclAt_self {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (κ : GL (Fin 2) w.Completion) :
    archComponent F w (glArch (𝓞 F) F (adelicArchGLInclAt F w κ)) = κ := by
  unfold adelicArchGLInclAt
  rw [MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_self]

theorem archComponent_glArch_adelicArchGLInclAt_of_ne {F : Type} [Field F] [NumberField F] {v w : InfinitePlace F}
    (hvw : v ≠ w) (κ : GL (Fin 2) w.Completion) :
    archComponent F v (glArch (𝓞 F) F (adelicArchGLInclAt F w κ)) = 1 := by
  unfold adelicArchGLInclAt
  rw [MonoidHom.comp_apply, glArch_adelicArchGLIncl, archComponent_archGLIncl_of_ne F hvw]

theorem mul_adelicArchGLInclAt_mem_centreCutSiegelSet {F : Type} [Field F] [NumberField F]
    {c u d₁ d₂ : ℝ} {w : InfinitePlace F} {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ centreCutSiegelSet F c u d₁ d₂)
    (κ : rowIsometrySubgroup₀ w.Completion) :
    g * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) ∈ centreCutSiegelSet F c u d₁ d₂ := by
  obtain ⟨hfin, hh, hx, hd⟩ := hg
  have hκ : IsRowIsometry (κ : GL (Fin 2) w.Completion) := rowIsometrySubgroup₀_le _ κ.2
  have hcomp : ∀ v : InfinitePlace F, IsRowIsometry (archComponent F v (glArch (𝓞 F) F (adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion)))) := by
    intro v
    by_cases hvw : v = w
    · subst hvw; rw [archComponent_glArch_adelicArchGLInclAt_self]; exact hκ
    · rw [archComponent_glArch_adelicArchGLInclAt_of_ne hvw]; exact isRowIsometry_one
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [map_mul, show glFin (𝓞 F) F (adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion)) = 1 from
      glFin_adelicArchGLIncl F _, mul_one]
    exact hfin
  · rw [map_mul, map_mul, localHeight_mul_rowIsometry _ (hcomp v)]
    exact hh v
  · rw [map_mul, map_mul, xWindowSq_mul_rowIsometry _ (hcomp v)]
    exact hx v
  · unfold archDetNorm
    rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul, (hcomp v).1, mul_one]
    exact hd v

theorem mul_adelicArchGLInclAt_mem_iUnion_image_mul_centreCutSiegelSet {F : Type} [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hT : ∀ x ∈ T, glArch (𝓞 F) F x = 1)
    (w : InfinitePlace F) {g : AdelicGL2 (𝓞 F) F}
    (hg : g ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (κ : rowIsometrySubgroup₀ w.Completion) :
    g * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂ := by
  simp only [Set.mem_iUnion, Set.mem_image] at hg ⊢
  obtain ⟨x, hxT, s, hs, rfl⟩ := hg
  refine ⟨x, hxT, s * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion),
    mul_adelicArchGLInclAt_mem_centreCutSiegelSet hs κ, ?_⟩

  have hcomm : adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) * x = x * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) := by
    refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
    · rw [map_mul, map_mul, hT x hxT, mul_one, one_mul]
    · rw [map_mul, map_mul, show glFin (𝓞 F) F (adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion)) = 1 from
        glFin_adelicArchGLIncl F _, mul_one, one_mul]
  show s * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) * x = s * x * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion)
  rw [mul_assoc, hcomm, ← mul_assoc]

end Ws47.PROJK

namespace Ws47
namespace SIGN

open NumberField.AdelicVolume

theorem dz_realComponent_eq_coe {w : InfinitePlace ℚ} (hw : w.IsReal) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    realComponent w hw g = ((archRealProjAt hw g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; rfl

theorem dz_archRealProjAt_adelicArchGLInclAt {w : InfinitePlace ℚ} (hw : w.IsReal) (k : GL (Fin 2) w.Completion) :
    archRealProjAt hw (adelicArchGLInclAt ℚ w k) = glEquivOfRingEquiv (ringEquivRealOfIsReal hw) k := by
  rw [← archRealGLAt_glEquivOfRingEquiv hw k, archRealProjAt_archRealGLAt]

theorem dz_glFin_adelicArchGLInclAt (w : InfinitePlace ℚ) (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 ℚ) ℚ (adelicArchGLInclAt ℚ w k) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem dz_glFin_archRealGLAt {w : InfinitePlace ℚ} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem dz_archRealGLAt_eq {w : InfinitePlace ℚ} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archRealGLAt hw m = adelicArchGLInclAt ℚ w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) := rfl

theorem dz_archWeightCharℝ_zero (r : rowIsometrySubgroup₀ ℝ) : ((archWeightCharℝ 0 r : ℂˣ) : ℂ) = 1 := by
  show ((((archWeightOneℝ r) ^ (0 : ℤ) : ℂˣ)) : ℂ) = 1
  rw [zpow_zero, Units.val_one]

theorem dz_char_zero_comp (κ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion) :
    ((((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace)
        (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) κ : ℂˣ) : ℂ) = 1 := by
  rw [MonoidHom.comp_apply, dz_archWeightCharℝ_zero]

theorem dz_coe_glEquivOfRingEquiv {K L : Type*} [NormedField K] [NormedField L] (e : K ≃+* L) (k : GL (Fin 2) K) :
    ((glEquivOfRingEquiv e k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) = e.toRingHom.mapMatrix (k : Matrix (Fin 2) (Fin 2) K) := by
  ext i j; rfl

theorem dz_prod_archDetNorm_mul_adelicArchGLInclAt (g : AdelicGL2 (𝓞 ℚ) ℚ) (k : GL (Fin 2) (Rat.infinitePlace).Completion)
    (hk : ‖((k : Matrix (Fin 2) (Fin 2) (Rat.infinitePlace).Completion)).det‖ = 1) :
    ∏ v : InfinitePlace ℚ, archDetNorm v (g * adelicArchGLInclAt ℚ Rat.infinitePlace k) ^ v.mult =
      ∏ v : InfinitePlace ℚ, archDetNorm v g ^ v.mult := by
  refine Finset.prod_congr rfl fun v _ => ?_
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  congr 1
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul, Ws47.PROJK.archComponent_glArch_adelicArchGLInclAt_self,
    hk, mul_one]

theorem dz_J_w_coe :
    ((glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace)
        (glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm UpperHalfPlane.J) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal ![(-1 : ℝ), 1] := by
  ext i j
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry, RingEquiv.apply_symm_apply, UpperHalfPlane.val_J]
  fin_cases i <;> fin_cases j <;> simp

theorem dz_norm_det_J_w :
    ‖(((glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm UpperHalfPlane.J :
        GL (Fin 2) (Rat.infinitePlace).Completion)) : Matrix (Fin 2) (Fin 2) (Rat.infinitePlace).Completion).det‖ = 1 := by
  rw [dz_coe_glEquivOfRingEquiv, ← RingHom.map_det, UpperHalfPlane.val_J, Matrix.det_fin_two_of]
  simp

theorem stdWindow_mul_archIncl_mem (g : AdelicGL2 (𝓞 ℚ) ℚ) (hg : g ∈ (productionPinsGeneral ℚ).D)
    (κ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion) :
    g * adelicArchGLInclAt ℚ Rat.infinitePlace (κ : GL (Fin 2) (Rat.infinitePlace).Completion) ∈ (productionPinsGeneral ℚ).D := by
  rw [productionPinsGeneral_D] at hg ⊢
  unfold classRepSiegelSet at hg ⊢
  refine Ws47.PROJK.mul_adelicArchGLInclAt_mem_iUnion_image_mul_centreCutSiegelSet _ _ _ _ _ (fun x hx => ?_)
    Rat.infinitePlace hg κ
  letI := Fintype.ofFinite (ClassGroup (𝓞 ℚ) ⧸ (classSq ℚ).range)
  rw [classRepTranslates, Finset.mem_map] at hx
  obtain ⟨C, -, rfl⟩ := hx
  exact glArch_classRepEmbedding ℚ C

theorem measurableSet_stdWindow :
    @MeasurableSet (AdelicGL2 (𝓞 ℚ) ℚ) (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 ℚ) ℚ) (productionPinsGeneral ℚ).D := by
  letI := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  rw [productionPinsGeneral_D]
  unfold classRepSiegelSet
  refine Finset.measurableSet_biUnion _ fun x _ => ?_
  have himage : (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2 = (· * x⁻¹) ⁻¹' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2 := by
    ext g
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨s, hs, rfl⟩; simpa using hs
    · intro h; exact ⟨g * x⁻¹, h, by simp⟩
  rw [himage]
  exact (measurableSet_centreCutSiegelSet (F := ℚ) _ _ _ _).preimage (continuous_mul_const _).measurable

theorem fibre_weight_zero_and_J
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hWF : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
          (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
              (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                archW (fun _ _ => P) archC dR dC g * z))
    (hWT : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ)))
    (hDE : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchCasimir.IsCasimirEigen (dR w hw))
    (hnv : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dR w hw).W g ≠ 0)
    (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)))
    (htype : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1))
    (hP0 : (RealArchParam.centralExponent P).re = 0)
    (u₁ u₂ : ℂ) (a₁ : ZMod 2) (hP : P = RealArchParam.principal u₁ a₁ u₂ a₁)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) (z : ℂ)
    (hfib : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
        (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          archW (fun _ _ => P) archC dR dC g * z) :
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ → ∀ κ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 (g * adelicArchGLInclAt ℚ Rat.infinitePlace (κ : GL (Fin 2) (Rat.infinitePlace).Completion))
        = (((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) κ : ℂ) * whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g) ∧
    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)
        = (-1 : ℂ) ^ a₁.val * whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g) := by
  classical
  subst hP
  set w : InfinitePlace ℚ := Rat.infinitePlace with hwdef
  have hw : w.IsReal := Rat.isReal_infinitePlace
  have haa : a₁ + a₁ = 0 := by fin_cases a₁ <;> decide

  have hDW0 : ∀ (w' : InfinitePlace ℚ) (hw' : w'.IsReal) (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      (dR w' hw').W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ 0 r : ℂ) * (dR w' hw').W (x : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro w' hw' r x
    have h := hWT w' hw' r x
    simp only [haa, ↓reduceIte] at h
    exact h
  have hgen' : ∀ p : ℤ, Odd p → u₁ - u₂ ≠ (p : ℂ) := by
    intro p hp heq
    have hp0 : p ≠ 0 := by rintro rfl; exact (by decide : ¬ Odd (0 : ℤ)) hp
    apply hgen u₁ u₂ a₁ a₁ rfl p hp0 heq
    rw [sub_self]
    obtain ⟨k, rfl⟩ := hp
    have : (2 * k + 1 + 1 : ℤ) = 2 * (k + 1) := by ring
    rw [this, Int.cast_mul, show ((2 : ℤ) : ZMod 2) = 0 by decide, zero_mul]
  have hpar : ∀ (w' : InfinitePlace ℚ) (hw' : w'.IsReal) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 →
      (dR w' hw').W (x * Matrix.diagonal ![(-1 : ℝ), 1]) = (-1 : ℂ) ^ a₁.val * (dR w' hw').W x := fun w' hw' x hx =>
    LanglandsTunnell.Converse.ArchDatumR.W_mul_diag_eq_neg_one_pow_mul_of_principal_of_archWeightChar_zero_of_isCasimirEigen
      u₁ u₂ a₁ hgen' (dR w' hw') (hDW0 w' hw') (hDE w' hw') x hx

  have harchWK : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (κ : rowIsometrySubgroup₀ w.Completion),
      archW (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₁) archC dR dC
          (g * adelicArchGLInclAt ℚ w (κ : GL (Fin 2) w.Completion)) =
        archW (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₁) archC dR dC g := by
    intro g κ
    unfold archW
    rw [Fintype.prod_subsingleton _ w, Fintype.prod_subsingleton _ w, dif_pos hw, dif_pos hw,
      dz_realComponent_eq_coe, dz_realComponent_eq_coe, map_mul, dz_archRealProjAt_adelicArchGLInclAt]
    have := hDW0 w hw (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw) κ)
      (archRealProjAt hw g)
    rw [dz_archWeightCharℝ_zero, one_mul] at this
    exact this
  have harchWJ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      archW (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₁) archC dR dC (g * archRealGLAt hw UpperHalfPlane.J) =
        (-1 : ℂ) ^ a₁.val * archW (fun _ _ => RealArchParam.principal u₁ a₁ u₂ a₁) archC dR dC g := by
    intro g
    unfold archW
    rw [Fintype.prod_subsingleton _ w, Fintype.prod_subsingleton _ w, dif_pos hw, dif_pos hw,
      dz_realComponent_eq_coe, dz_realComponent_eq_coe, map_mul, Units.val_mul, dz_archRealGLAt_eq,
      dz_archRealProjAt_adelicArchGLInclAt, dz_J_w_coe]
    refine hpar w hw _ ?_
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Units.isUnit _).ne_zero

  have hNK : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (κ : rowIsometrySubgroup₀ w.Completion),
      ∏ v : InfinitePlace ℚ, archDetNorm v (g * adelicArchGLInclAt ℚ w (κ : GL (Fin 2) w.Completion)) ^ v.mult =
        ∏ v : InfinitePlace ℚ, archDetNorm v g ^ v.mult := fun g κ =>
    dz_prod_archDetNorm_mul_adelicArchGLInclAt g _ (rowIsometrySubgroup₀_le _ κ.2).1
  have hNJ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ∏ v : InfinitePlace ℚ, archDetNorm v (g * archRealGLAt hw UpperHalfPlane.J) ^ v.mult =
        ∏ v : InfinitePlace ℚ, archDetNorm v g ^ v.mult := fun g => by
    rw [dz_archRealGLAt_eq]
    exact dz_prod_archDetNorm_mul_adelicArchGLInclAt g _ dz_norm_det_J_w

  have hfibK : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ), glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ → ∀ κ : rowIsometrySubgroup₀ w.Completion,
      glFin (𝓞 ℚ) ℚ (g * adelicArchGLInclAt ℚ w (κ : GL (Fin 2) w.Completion)) = glFin (𝓞 ℚ) ℚ g₀ := by
    intro g hg κ; rw [map_mul, dz_glFin_adelicArchGLInclAt, mul_one]; exact hg
  have hfibJ : ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ), glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
      glFin (𝓞 ℚ) ℚ (g * archRealGLAt hw UpperHalfPlane.J) = glFin (𝓞 ℚ) ℚ g₀ := by
    intro g hg; rw [map_mul, dz_glFin_archRealGLAt, mul_one]; exact hg
  refine ⟨fun g hg κ => ?_, fun g hg => ?_⟩
  · rw [hfib _ (hfibK g hg κ), hfib g hg, hNK g κ, harchWK g κ, dz_char_zero_comp, one_mul]
  · rw [hfib _ (hfibJ g hg), hfib g hg, hNJ g, harchWJ g]
    ring

theorem dz_archRealGLAt_J_mul_J :
    archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J = 1 := by
  rw [← map_mul]; convert map_one (archRealGLAt Rat.isReal_infinitePlace)
  ext i j; fin_cases i <;> fin_cases j <;> simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two]

theorem dz_isRowIsometry_J_w :
    IsRowIsometry (glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm UpperHalfPlane.J :
      GL (Fin 2) (Rat.infinitePlace).Completion) := by
  refine ⟨dz_norm_det_J_w, fun x y => ?_⟩
  simp only [glEquivOfRingEquiv_apply_entry, UpperHalfPlane.val_J, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, map_neg, map_one, map_zero, mul_neg, mul_one,
    mul_zero, add_zero, zero_add, norm_neg]

noncomputable def dz_conjJ (κ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion) : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion :=
  ⟨glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm UpperHalfPlane.J * (κ : GL (Fin 2) (Rat.infinitePlace).Completion) *
      glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm UpperHalfPlane.J, by
    obtain ⟨hd, hiso⟩ := (mem_rowIsometrySubgroup₀_iff _).mp κ.2
    refine (mem_rowIsometrySubgroup₀_iff _).mpr ⟨?_, (dz_isRowIsometry_J_w.mul hiso).mul dz_isRowIsometry_J_w⟩
    have hJ : (((glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm UpperHalfPlane.J :
        GL (Fin 2) (Rat.infinitePlace).Completion)) : Matrix (Fin 2) (Fin 2) (Rat.infinitePlace).Completion).det = -1 := by
      rw [dz_coe_glEquivOfRingEquiv, ← RingHom.map_det, UpperHalfPlane.val_J, Matrix.det_fin_two_of]
      simp
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hJ, hd]
    norm_num⟩

theorem dz_coe_conjJ (κ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion) :
    ((dz_conjJ κ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion) : GL (Fin 2) (Rat.infinitePlace).Completion) =
      glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm UpperHalfPlane.J * (κ : GL (Fin 2) (Rat.infinitePlace).Completion) *
        glEquivOfRingEquiv (ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm UpperHalfPlane.J := rfl

theorem hasArchCharacterAt₀_Jsym (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ) (ε : ℂ) :
    HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) (fun g => φ g + ε * φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)) := by
  intro κ g
  have hJJ := dz_archRealGLAt_J_mul_J

  have hswap : adelicArchGLInclAt ℚ Rat.infinitePlace (κ : GL (Fin 2) (Rat.infinitePlace).Completion) *
      archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J =
        archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J *
          adelicArchGLInclAt ℚ Rat.infinitePlace ((dz_conjJ κ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion) :
            GL (Fin 2) (Rat.infinitePlace).Completion) := by
    rw [dz_coe_conjJ, map_mul, map_mul, ← dz_archRealGLAt_eq, ← mul_assoc, ← mul_assoc, hJJ, one_mul]
  simp only
  rw [dz_char_zero_comp, one_mul, mul_assoc g, hswap, ← mul_assoc, hφ (dz_conjJ κ) (g * archRealGLAt _ UpperHalfPlane.J), hφ κ g,
    dz_char_zero_comp, dz_char_zero_comp, one_mul, one_mul]

end Ws47.SIGN

namespace Ws47
namespace SIGN

theorem whittakerCoefficient_window_eq_general (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    whittakerCoefficient ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) ψ φ 1 g = whittakerCoefficient ℚ (productionPinsGeneral ℚ) ψ φ 1 g := by
  rfl

theorem archRealGLAt_J_mul_J : archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J = 1 := by
  rw [← map_mul]; convert map_one (archRealGLAt Rat.isReal_infinitePlace)
  ext i j; fin_cases i <;> fin_cases j <;> simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two]

end Ws47.SIGN

open Ws47.SIGN in
theorem solution
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Φ : HeckeEigensystem ℚ ℂ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (hWF : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => ∃ g₀ : AdelicGL2 (𝓞 ℚ) ℚ,
          (∃ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ ∧
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g ≠ 0) ∧
          ∃ z : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
            whittakerCoefficient ℚ
              (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
              (NumberField.StandardAddChar.stdAddChar ℚ) φ 1 g =
              (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
                archW (fun _ _ => P) archC dR dC g * z))
    (hWT : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        (dR w hw).W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1) r : ℂ) * (dR w hw).W (x : Matrix (Fin 2) (Fin 2) ℝ)))
    (hDE : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchCasimir.IsCasimirEigen (dR w hw))
    (hnv : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ g : GL (Fin 2) ℝ, (dR w hw).W g ≠ 0)
    (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)))
    (htype : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1))
    (hP0 : (RealArchParam.centralExponent P).re = 0)
    (u₁ u₂ : ℂ) (a₁ : ZMod 2) (hP : P = RealArchParam.principal u₁ a₁ u₂ a₁) :
    ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
      (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ ∧
        IsArchSmoothAt Rat.isReal_infinitePlace φ ∧
        archCasimirAt Rat.isReal_infinitePlace φ = (laplaceEigenvalue P) • φ ∧
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ g) := by
  classical

  obtain ⟨Θ, hΘΦ, R', hR'gen, g₀, ⟨g₁, hg₁, hne⟩, z, hfib⟩ := hWF

  obtain ⟨R₁, hR₁⟩ := AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
    c u d₁ d₂ T hc hd₁ hd hcov Θ.toRawCentral R' hR'gen
  have hR₁c : Continuous R₁.toFun := by rw [hR₁]; exact hR'gen
  have hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R₁.centralChar Θ.level R₁.exceptionalSet Θ R₁.toFun :=
    R₁.isIsotypicCuspFormAt hR₁c

  have hfib₁ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) R₁.toFun 1 g =
        (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          archW (fun _ _ => P) archC dR dC g * z := by
    intro g hg; rw [hR₁, ← whittakerCoefficient_window_eq_general c u d₁ d₂ T]; exact hfib g hg
  have hne₁ : whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) R₁.toFun 1 g₁ ≠ 0 := by
    rw [hR₁, ← whittakerCoefficient_window_eq_general c u d₁ d₂ T]; exact hne
  obtain ⟨hwt₁, hJ₁⟩ := fibre_weight_zero_and_J c u d₁ d₂ T hc hd₁ hd hcov Φ P archC dR dC
    ⟨Θ, hΘΦ, R', hR'gen, g₀, ⟨g₁, hg₁, hne⟩, z, hfib⟩ hWT hDE hnv hgen htype hP0 u₁ u₂ a₁ hP R₁.toFun g₀ z hfib₁

  obtain ⟨φ₀, hφ₀iso, hφ₀wt, hφ₀W⟩ :=
    AutomorphicForm.exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq
      ℚ (productionPinsGeneral ℚ).D Rat.infinitePlace Rat.isReal_infinitePlace (fun g hg κ => stdWindow_mul_archIncl_mem g hg κ) measurableSet_stdWindow
      R₁.centralChar Θ.level R₁.exceptionalSet Θ R₁.toFun hiso 0 (NumberField.StandardAddChar.stdAddChar ℚ)
      (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar ℚ).continuous
      {g | glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀} (fun g hg κ => hwt₁ g hg κ)
  have hφ₀W' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) φ₀ 1 g
        = whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) R₁.toFun 1 g :=
    fun g hg => hφ₀W g hg
  have hφ₀iso' : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R₁.centralChar Θ.level R₁.exceptionalSet Θ φ₀ := hφ₀iso

  set x : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun g => φ₀ g + (-1 : ℂ) ^ a₁.val * φ₀ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) with hx
  obtain ⟨χ₀, hφ₀cut⟩ := exists_ofChar_mem φ₀ hφ₀wt
  have hxiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R₁.centralChar Θ.level R₁.exceptionalSet Θ x :=
    isIsotypicCuspFormAt_Jsym _ _ Θ.level_ne_bot _ _ φ₀ hφ₀iso' χ₀ hφ₀cut _
  have hxwt : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 0).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) x := hasArchCharacterAt₀_Jsym φ₀ hφ₀wt _
  have hJJ := archRealGLAt_J_mul_J
  have hεε : ((-1 : ℂ) ^ a₁.val) * ((-1 : ℂ) ^ a₁.val) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hxJ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, x (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * x g := by
    intro g
    show φ₀ (g * archRealGLAt _ UpperHalfPlane.J) + (-1 : ℂ) ^ a₁.val * φ₀ (g * archRealGLAt _ UpperHalfPlane.J * archRealGLAt _ UpperHalfPlane.J)
        = (-1 : ℂ) ^ a₁.val * (φ₀ g + (-1 : ℂ) ^ a₁.val * φ₀ (g * archRealGLAt _ UpperHalfPlane.J))
    rw [mul_assoc g, hJJ, mul_one]
    linear_combination (-(φ₀ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J))) * hεε

  have hψc : Continuous (NumberField.StandardAddChar.stdAddChar ℚ) :=
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar ℚ).continuous
  have hφ₀c : Continuous φ₀ := hφ₀iso'.continuous
  have hxW : whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) x 1 g₁
      = 2 * whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) R₁.toFun 1 g₁ := by
    rw [hx, whittakerCoefficient_add_smul _ hψc φ₀ (fun y => φ₀ (y * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J)) hφ₀c
      (hφ₀c.comp (continuous_mul_const _)) _ g₁, whittakerCoefficient_translate, hφ₀W' g₁ hg₁,
      hφ₀W' (g₁ * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) (show glFin (𝓞 ℚ) ℚ (g₁ * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) = glFin (𝓞 ℚ) ℚ g₀ by
        rw [map_mul, show glFin (𝓞 ℚ) ℚ (archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) = 1 from glFin_adelicArchGLIncl ℚ _, mul_one]; exact hg₁),
      hJ₁ g₁ hg₁, ← mul_assoc, hεε, one_mul, two_mul]
  have hx0 : x ≠ 0 := by
    intro h0
    apply hne₁
    have : whittakerCoefficient ℚ (productionPinsGeneral ℚ) (NumberField.StandardAddChar.stdAddChar ℚ) x 1 g₁ = 0 := by
      rw [h0]; simp [whittakerCoefficient]
    rw [hxW] at this
    simpa using this

  obtain ⟨lam, huniq, hvec⟩ :=
    AutomorphicForm.exists_forall_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_of_mem_archCutSubmodule_of_coversModCentre
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num)
      (AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat) Θ Rat.infinitePlace Rat.isReal_infinitePlace
  obtain ⟨tys, hxtys⟩ := exists_archTypeFamily_mem x hxwt
  obtain ⟨hxs, -, -, hxC⟩ := hvec Θ (AutomorphicForm.TranslateSpanOccurrence.agrees_refl Θ) R₁ hR₁c R₁.exceptionalSet tys x hx0
    (mem_isotypicCuspSubmodule _ _ _ _ x hxiso) hxtys

  obtain ⟨n₀, hn₀⟩ := exists_occ_std_typed c u d₁ d₂ T hc hd₁ hd hcov Φ P archC dR dC
    ⟨Θ, hΘΦ, R', hR'gen, g₀, ⟨g₁, hg₁, hne⟩, z, hfib⟩ hWT hDE hnv hgen htype hP0 Θ R₁ hR₁c g₀ z ⟨g₁, hg₁, hne₁⟩ hfib₁
  have hlam : laplaceEigenvalue P = lam := huniq n₀ _ hn₀

  exact occurs_window_of_isIsotypic_general c u d₁ d₂ T hc hd₁ Φ Θ hΘΦ R₁.centralChar R₁.exceptionalSet x hxiso hx0 _
    ⟨hxwt, hxs, by rw [hlam]; exact hxC, hxJ⟩

end S_LanglandsTunnell_archOccursInClassOf_archWeightChar_zero_archCasimirAt_apply_mul_J_eq_neg_one_pow_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
end P2MW
export P2MW.S_LanglandsTunnell_archOccursInClassOf_archWeightChar_zero_archCasimirAt_apply_mul_J_eq_neg_one_pow_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen (solution)
