-- Prove2me | solution 1 for LanglandsTunnell.exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b229f95e-333f-50a0-9ef6-d6c3d7d958c4

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
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Theorems.Thm_LanglandsTunnell_archOccursInClassOf_archWeightChar_zero_archCasimirAt_apply_mul_J_eq_neg_one_pow_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_exists_finset_norm_b_eq_absNorm_of_whittakerCoefficient_fibre_eq_archW_of_re_centralExponent_eq_zero
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_centralChar_eq_of_agreesAwayFromFinite
import Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
import Theorems.Thm_AutomorphicForm_exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_AutomorphicForm_finiteDimensional_isotypicCuspSubmodule_inf_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_LanglandsTunnell_Converse_continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq
import Theorems.Thm_LanglandsTunnell_exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_archOccursInClassOf_archCasimirAt_iff_of_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
import Theorems.Thm_AutomorphicForm_archOccursInClassOf_lower_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_twist_W_eq_abs_det_rpow_mul
import Theorems.Thm_AutomorphicForm_eq_stdAddChar_of_isGlobalAddChar_of_apply_infinitePlace_eq_exp
import Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_sq_mul_sq_eq_one_and_W_mul_diag_eq_mul_lower_of_principal_of_ne_of_ne_of_archWeightChar_one_of_isCasimirEigen
import Theorems.Thm_LanglandsTunnell_isArchSmoothAt_whittakerCoefficient_and_archDerivAt_comm
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_LanglandsTunnell_RealArchParam_eq_of_archFactor_twist_mul_eq_archFactor_twist_mul_entire
import Theorems.Thm_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot
import Theorems.Thm_AutomorphicForm_exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq
import Theorems.Thm_AutomorphicForm_exists_forall_archCasimirAt_eq_smul_of_mem_isotypicCuspSubmodule_of_mem_archCutSubmodule_of_coversModCentre
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_WhittakerModelMultiplicityOne
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq
import Theorems.Thm_LanglandsTunnell_exists_mem_isCuspConstituent_isIsotypicCuspFormAt_whittakerCoefficient_diagOne_ne_zero_J_rigid_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_exists_irreducible_admissible_isotypicAt
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_localSpaceAt_cyclic_finite_fixed_smooth_of_hasMultiplicityOneAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_LanglandsTunnell_exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar LanglandsTunnell.isScalarTower_fixFldDetKer_fixFldQuatH_L LanglandsTunnell.isScalarTower_rat_fixFldSylowH_fixFldQuatH LanglandsTunnell.detKer_normal LanglandsTunnell.isScalarTower_rat_fixFldDetKer_fixFldQuatH LanglandsTunnell.algebra_fixFldDetKer_fixFldQuatH LanglandsTunnell.isScalarTower_fixFldSylowH_fixFldQuatH_L LanglandsTunnell.algebra_fixFldSylowH_fixFldQuatH LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.mem_inducedSectionSubmodule_iff"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

noncomputable section

namespace P2M
namespace WPlusSelect

open NumberField IsDedekindDomain MeasureTheory
p2m_open "AutomorphicForm~det_centralScalar"

section Measure

attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem isProbabilityMeasure_productionPinsOf_ν (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) :
    IsProbabilityMeasure (productionPinsOf F D U gen (AdelicBox.adelicBox F)).ν :=
  AdelicBox.isProbabilityMeasure_cond_adelicBox F

theorem ae_mem_adelicBox_productionPinsOf_ν (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) :
    ∀ᵐ x ∂(productionPinsOf F D U gen (AdelicBox.adelicBox F)).ν, x ∈ AdelicBox.adelicBox F :=
  ProbabilityTheory.ae_cond_mem (AdelicBox.measurableSet_adelicBox F)

theorem isProbabilityMeasure_productionPinsGeneral_ν (F : Type) [Field F] [NumberField F] :
    IsProbabilityMeasure (productionPinsGeneral F).ν := by
  unfold productionPinsGeneral productionPinsGeneralOf
  exact isProbabilityMeasure_productionPinsOf_ν F _ _ _

theorem ae_mem_adelicBox_productionPinsGeneral_ν (F : Type) [Field F] [NumberField F] :
    ∀ᵐ x ∂(productionPinsGeneral F).ν, x ∈ AdelicBox.adelicBox F := by
  unfold productionPinsGeneral productionPinsGeneralOf
  exact ae_mem_adelicBox_productionPinsOf_ν F _ _ _

end Measure

theorem continuous_unipotentGL2_mul
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    Continuous fun x : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
      AutomorphicForm.unipotentGL2 x * g :=
  AutomorphicForm.continuous_unipotentGL2.mul continuous_const

theorem continuous_whittakerIntegrand
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hφ : Continuous φ) (α : ℚ)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    Continuous fun x : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
      φ (AutomorphicForm.unipotentGL2 x * g) *
        NumberField.StandardAddChar.psiQ
          (-(algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) α * x)) :=
  (hφ.comp (continuous_unipotentGL2_mul g)).mul
    (NumberField.StandardAddChar.continuous_psiQ.comp ((continuous_const.mul continuous_id).neg))

theorem whittakerCoefficientIntegrable_productionPinsGeneral_of_continuous
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hφ : Continuous φ) (α : ℚ)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    AutomorphicForm.WhittakerCoefficientIntegrable ℚ (AutomorphicForm.productionPinsGeneral ℚ)
      NumberField.StandardAddChar.psiQ φ α g := by
  have hprob := isProbabilityMeasure_productionPinsGeneral_ν ℚ
  have hae := ae_mem_adelicBox_productionPinsGeneral_ν ℚ
  unfold AutomorphicForm.WhittakerCoefficientIntegrable
  letI : MeasurableSpace (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :=
    (AutomorphicForm.productionPinsGeneral ℚ).nS
  haveI : BorelSpace (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) :=
    NumberField.AdelicHaar.borelSpace_adeleBorel (NumberField.RingOfIntegers ℚ) ℚ
  haveI := hprob
  obtain ⟨K, hK, hbox⟩ := NumberField.AdelicBox.exists_isCompact_adelicBox_subset ℚ
  have hcont := continuous_whittakerIntegrand φ hφ α g
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine (MeasureTheory.integrable_const C).mono' hcont.aestronglyMeasurable ?_
  filter_upwards [hae] with x hx
  exact hC x (hbox hx)

theorem continuous_of_mem_cuspKFiniteSubmodule (F : Type) [Field F] [NumberField F]
    (pins : AutomorphicForm.CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F → ℂ}
    (hφ : φ ∈ AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule F pins ξ) : Continuous φ := by
  unfold AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule at hφ
  induction hφ using Submodule.span_induction with
  | mem ψ hψ => exact hψ.2.1
  | zero => exact continuous_const
  | add a b _ _ ha hb => exact ha.add hb
  | smul c a _ ha => exact ha.const_smul c

theorem continuous_of_mem_of_isCuspSubrep (F : Type) [Field F] [NumberField F]
    (pins : AutomorphicForm.CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {V : Submodule ℂ (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F → ℂ)}
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspSubrep F pins ξ V)
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F → ℂ} (hφ : φ ∈ V) : Continuous φ :=
  continuous_of_mem_cuspKFiniteSubmodule F pins ξ (hV.le hφ)

theorem globalPoints_unipotentGL2 (β : ℚ) :
    AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ (AutomorphicForm.unipotentGL2 β) =
      AutomorphicForm.unipotentGL2
        (algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) β) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.globalPoints, Matrix.GeneralLinearGroup.map, AutomorphicForm.unipotentGL2]

theorem apply_globalPoints_mul_eq_of_mem_cuspKFiniteSubmodule (F : Type) [Field F] [NumberField F]
    (pins : AutomorphicForm.CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F → ℂ}
    (hφ : φ ∈ AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule F pins ξ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers F) F) :
    φ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers F) F γ * g) = φ g := by
  unfold AutomorphicForm.CuspidalConstituent.cuspKFiniteSubmodule at hφ
  induction hφ using Submodule.span_induction generalizing g with
  | mem ψ hψ =>
    have h1 := (hψ.1 1).1.1
    letI := pins.mS
    have h2 := ((AutomorphicForm.lsXiMemberAt_iff _ _ pins.μ pins.Z ξ pins.D _).1 h1).1.left_invariant γ g
    simpa [AutomorphicForm.CuspidalConstituent.rightTranslate] using h2
  | zero => rfl
  | add a b _ _ ha hb => simp only [Pi.add_apply, ha g, hb g]
  | smul c a _ ha => simp only [Pi.smul_apply, ha g]

theorem apply_unipotentGL2_algebraMap_mul_eq_of_isCuspSubrep
    (pins : AutomorphicForm.CarrierPins ℚ) (ξ : pins.Z →* ℂˣ)
    {V : Submodule ℂ (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)}
    (hV : AutomorphicForm.CuspidalConstituent.IsCuspSubrep ℚ pins ξ V)
    {φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ} (hφ : φ ∈ V) (β : ℚ)
    (z : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    φ (AutomorphicForm.unipotentGL2
        (algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) β) * z) = φ z := by
  rw [← globalPoints_unipotentGL2]
  exact apply_globalPoints_mul_eq_of_mem_cuspKFiniteSubmodule ℚ pins ξ (hV.le hφ) _ z

theorem eq_of_glArch_eq_of_glFin_eq
    {x y : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ}
    (h₁ : NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ x =
      NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ y)
    (h₂ : NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ x =
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ y) : x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (NumberField.InfiniteAdeleRing ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (NumberField.InfiniteAdeleRing ℚ)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ) =>
      (m : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) i j) h₂
  exact Prod.ext h₁' h₂'

theorem eq_of_forall_finComponent_eq
    (a b : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ))
    (h : ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      NumberField.AdelicLevel.finComponent (NumberField.RingOfIntegers ℚ) ℚ w a =
        NumberField.AdelicLevel.finComponent (NumberField.RingOfIntegers ℚ) ℚ w b) :
    a = b := by
  apply Units.ext
  ext i j w
  exact congrArg
    (fun m : GL (Fin 2) (w.adicCompletion ℚ) => (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ)) i j)
    (h w)

theorem finEmbed_localEmbed_mul_comm
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
    (hv : NumberField.AdelicLevel.finComponent (NumberField.RingOfIntegers ℚ) ℚ v
      (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h) = 1)
    (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g) * h =
      h * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g) := by
  apply eq_of_glArch_eq_of_glFin_eq
  · simp only [map_mul, AdelicDock.glArch_finEmbed, one_mul, mul_one]
  · simp only [map_mul, AdelicDock.glFin_finEmbed]
    apply eq_of_forall_finComponent_eq
    intro w
    by_cases hw : w = v
    · subst hw
      simp only [map_mul, AdelicDock.finComponent_localEmbed_self, hv, one_mul, mul_one]
    · simp only [map_mul, AdelicDock.finComponent_localEmbed_of_ne (NumberField.RingOfIntegers ℚ) ℚ v g hw,
        one_mul, mul_one]

theorem exists_finComponent_eq_one_and_eq_finEmbed_localEmbed_mul
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    ∃ (hv : GL (Fin 2) (v.adicCompletion ℚ))
      (h' : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      NumberField.AdelicLevel.finComponent (NumberField.RingOfIntegers ℚ) ℚ v
          (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h') = 1 ∧
        h = AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
          (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v hv) * h' := by
  refine ⟨NumberField.AdelicLevel.finComponent (NumberField.RingOfIntegers ℚ) ℚ v
      (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h),
    (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
      (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v
        (NumberField.AdelicLevel.finComponent (NumberField.RingOfIntegers ℚ) ℚ v
          (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h))))⁻¹ * h, ?_, ?_⟩
  · simp only [map_mul, map_inv, AdelicDock.glFin_finEmbed, AdelicDock.finComponent_localEmbed_self,
      inv_mul_cancel]
  · exact (mul_inv_cancel_left _ _).symm

def singlePlaceAdeleAt (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (x : v.adicCompletion ℚ) : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ :=
  ((0 : NumberField.InfiniteAdeleRing ℚ), AdelicDock.splice (NumberField.RingOfIntegers ℚ) ℚ v 0 x)

theorem splice_zero_zero_eq_zero (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    AdelicDock.splice (NumberField.RingOfIntegers ℚ) ℚ v 0 0 = 0 := by
  ext u
  by_cases hu : u = v
  · subst hu
    rw [AdelicDock.splice_apply_self]
    rfl
  · rw [AdelicDock.splice_apply_of_ne (NumberField.RingOfIntegers ℚ) ℚ v 0 0 hu]

theorem splice_one_one_eq_one (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    AdelicDock.splice (NumberField.RingOfIntegers ℚ) ℚ v 1 1 = 1 := by
  ext u
  by_cases hu : u = v
  · subst hu
    rw [AdelicDock.splice_apply_self]
    rfl
  · rw [AdelicDock.splice_apply_of_ne (NumberField.RingOfIntegers ℚ) ℚ v 1 1 hu]

theorem finEmbed_localEmbed_unipotentGL2
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (x : v.adicCompletion ℚ) :
    AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v (AutomorphicForm.unipotentGL2 x)) =
      AutomorphicForm.unipotentGL2 (singlePlaceAdeleAt v x) := by
  apply Units.ext
  rw [AdelicDock.coe_finEmbed, AdelicDock.coe_localEmbed, AutomorphicForm.unipotentGL2_coe,
    AutomorphicForm.unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AdelicDock.finMat, AdelicDock.localMat, splice_zero_zero_eq_zero, splice_one_one_eq_one,
      singlePlaceAdeleAt, Matrix.one_apply] <;> rfl

theorem psiQ_singlePlaceAdeleAt
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (x : v.adicCompletion ℚ) :
    NumberField.StandardAddChar.psiQ (singlePlaceAdeleAt v x) = NumberField.StandardAddChar.psiV v x := by
  rw [NumberField.StandardAddChar.psiQ_apply]
  show NumberField.StandardAddChar.psiArch 0 *
      NumberField.StandardAddChar.psiFin (AdelicDock.splice (NumberField.RingOfIntegers ℚ) ℚ v 0 x) =
    NumberField.StandardAddChar.psiV v x
  rw [AddChar.map_zero_eq_one, one_mul, NumberField.StandardAddChar.psiFin_apply,
    finprod_eq_single
      (fun u => NumberField.StandardAddChar.psiV u (AdelicDock.splice (NumberField.RingOfIntegers ℚ) ℚ v 0 x u)) v]
  · simp
  · intro u hu
    show NumberField.StandardAddChar.psiV u (AdelicDock.splice (NumberField.RingOfIntegers ℚ) ℚ v 0 x u) = 1
    rw [AdelicDock.splice_apply_of_ne (NumberField.RingOfIntegers ℚ) ℚ v 0 x hu]
    exact AddChar.map_zero_eq_one _

section Range

theorem injective_of_forall_eq_bot_or_eq_top_of_ne_zero
    {G : Type*} [Group G] {X : Type*} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ G X)
    (hirr : ∀ T : Submodule ℂ X, (∀ (g : G) (x : X), x ∈ T → π g x ∈ T) → T = ⊥ ∨ T = ⊤)
    (Λ : X →ₗ[ℂ] (G → ℂ))
    (hΛ : ∀ (g : G) (x : X), Λ (π g x) = fun g' => Λ x (g' * g))
    (hne : Λ ≠ 0) :
    Function.Injective Λ := by
  have hinv : ∀ (g : G) (x : X), x ∈ LinearMap.ker Λ → π g x ∈ LinearMap.ker Λ := by
    intro g x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hΛ g x]
    funext g'
    simp only [hx, Pi.zero_apply]
  rcases hirr (LinearMap.ker Λ) hinv with hbot | htop
  · exact LinearMap.ker_eq_bot.mp hbot
  · exact absurd (LinearMap.ker_eq_top.mp htop) hne

theorem mul_right_mem_range_of_equivariant
    {G : Type*} [Group G] {X : Type*} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ G X) (Λ : X →ₗ[ℂ] (G → ℂ))
    (hΛ : ∀ (g : G) (x : X), Λ (π g x) = fun g' => Λ x (g' * g)) :
    ∀ W ∈ LinearMap.range Λ, ∀ k : G, (fun g => W (g * k)) ∈ LinearMap.range Λ := by
  rintro W ⟨x, rfl⟩ k
  exact ⟨π k x, hΛ k x⟩

theorem exists_isOpen_forall_eq_of_mem_range_of_equivariant
    {G : Type*} [Group G] [TopologicalSpace G] {X : Type*} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ G X)
    (hsm : ∀ x : X, ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, π u x = x)
    (Λ : X →ₗ[ℂ] (G → ℂ))
    (hΛ : ∀ (g : G) (x : X), Λ (π g x) = fun g' => Λ x (g' * g)) :
    ∀ W ∈ LinearMap.range Λ, ∃ K : Subgroup G, IsOpen (K : Set G) ∧
      ∀ k ∈ K, (fun g => W (g * k)) = W := by
  rintro W ⟨x, rfl⟩
  obtain ⟨U, hU, hfix⟩ := hsm x
  refine ⟨U, hU, fun k hk => ?_⟩
  rw [← hΛ k x, hfix k hk]

theorem eq_bot_or_eq_range_of_le_range_of_equivariant
    {G : Type*} [Group G] {X : Type*} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ G X)
    (hirr : ∀ T : Submodule ℂ X, (∀ (g : G) (x : X), x ∈ T → π g x ∈ T) → T = ⊥ ∨ T = ⊤)
    (Λ : X →ₗ[ℂ] (G → ℂ))
    (hΛ : ∀ (g : G) (x : X), Λ (π g x) = fun g' => Λ x (g' * g)) :
    ∀ T : Submodule ℂ (G → ℂ), T ≤ LinearMap.range Λ →
      (∀ W ∈ T, ∀ k : G, (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = LinearMap.range Λ := by
  intro T hTle hTstab
  have hinv : ∀ (g : G) (x : X), x ∈ T.comap Λ → π g x ∈ T.comap Λ := by
    intro g x hx
    rw [Submodule.mem_comap] at hx ⊢
    rw [hΛ g x]
    exact hTstab _ hx g
  rcases hirr (T.comap Λ) hinv with hbot | htop
  · left
    rw [eq_bot_iff]
    intro W hW
    obtain ⟨x, rfl⟩ := hTle hW
    have hx : x ∈ T.comap Λ := Submodule.mem_comap.mpr hW
    rw [hbot, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact Submodule.zero_mem ⊥
  · right
    refine le_antisymm hTle ?_
    rintro W ⟨x, rfl⟩
    have hx : x ∈ T.comap Λ := by rw [htop]; exact Submodule.mem_top
    exact Submodule.mem_comap.mp hx

theorem finiteDimensional_of_le_range_of_forall_eq_of_injective
    {G : Type*} [Group G] [TopologicalSpace G] {X : Type*} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ G X)
    (hadm : ∀ U : Subgroup G, IsOpen (U : Set G) →
      ∃ T : Submodule ℂ X, FiniteDimensional ℂ T ∧ ∀ x : X, (∀ u ∈ U, π u x = x) → x ∈ T)
    (Λ : X →ₗ[ℂ] (G → ℂ))
    (hΛ : ∀ (g : G) (x : X), Λ (π g x) = fun g' => Λ x (g' * g))
    (hinj : Function.Injective Λ) :
    ∀ K : Subgroup G, IsOpen (K : Set G) → ∀ T : Submodule ℂ (G → ℂ), T ≤ LinearMap.range Λ →
      (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T := by
  intro K hK T hTle hTfix
  obtain ⟨TX, hTXfd, hTX⟩ := hadm K hK
  have hle : T ≤ TX.map Λ := by
    intro W hW
    obtain ⟨x, rfl⟩ := hTle hW
    refine Submodule.mem_map.mpr ⟨x, hTX x fun k hk => hinj ?_, rfl⟩
    rw [hΛ k x]
    exact hTfix _ hW k hk
  haveI : FiniteDimensional ℂ TX := hTXfd
  exact Submodule.finiteDimensional_of_le hle

theorem exists_forall_eq_mul_apply_one_of_forall_mem_span_of_apply_one_eq_zero
    {G : Type*} [Monoid G] {A : Type*} (u : A → G) (χ : A → ℂ) (S : Submodule ℂ (G → ℂ))
    (hS : ∀ W ∈ S, W 1 = 0 → W ∈ Submodule.span ℂ
      {V : G → ℂ | ∃ U ∈ S, ∃ x : A, V = (fun g => U (g * u x)) - χ x • U})
    (ℓ : (G → ℂ) →ₗ[ℂ] ℂ)
    (hℓ : ∀ W ∈ S, ∀ x : A, ℓ (fun g => W (g * u x)) = χ x * ℓ W) :
    ∃ c : ℂ, ∀ W ∈ S, ℓ W = c * W 1 := by
  have hker : Submodule.span ℂ
      {V : G → ℂ | ∃ U ∈ S, ∃ x : A, V = (fun g => U (g * u x)) - χ x • U} ≤ LinearMap.ker ℓ := by
    rw [Submodule.span_le]
    rintro V ⟨U, hU, x, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, hℓ U hU x, sub_self]
  by_cases h : ∃ W₀ ∈ S, W₀ 1 ≠ 0
  · obtain ⟨W₀, hW₀, hne⟩ := h
    refine ⟨ℓ W₀ / W₀ 1, fun W hW => ?_⟩
    have hmem : W - (W 1 / W₀ 1) • W₀ ∈ S := S.sub_mem hW (S.smul_mem _ hW₀)
    have hval : (W - (W 1 / W₀ 1) • W₀) 1 = 0 := by
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, mul_div_assoc, div_self hne,
        mul_one, sub_self]
    have hW' := hker (hS _ hmem hval)
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hW'
    rw [hW']
    ring
  · refine ⟨0, fun W hW => ?_⟩
    have hW1 : W 1 = 0 := by
      by_contra hne
      exact h ⟨W, hW, hne⟩
    have hW' := hker (hS W hW hW1)
    rw [LinearMap.mem_ker] at hW'
    rw [hW', zero_mul]

theorem exists_forall_eq_smul_of_injective_of_forall_mem_span
    {G : Type*} [Group G] {X : Type*} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ G X) {A : Type*} (u : A → G) (χ : A → ℂ)
    (Λ₀ Λ' : X →ₗ[ℂ] (G → ℂ))
    (h₀ : ∀ (g : G) (x : X), Λ₀ (π g x) = fun g' => Λ₀ x (g' * g))
    (h' : ∀ (g : G) (x : X), Λ' (π g x) = fun g' => Λ' x (g' * g))
    (hinj : Function.Injective Λ₀)
    (hlaw : ∀ (x : X) (a : A) (g : G), Λ' x (u a * g) = χ a * Λ' x g)
    (hJ : ∀ W ∈ LinearMap.range Λ₀, W 1 = 0 → W ∈ Submodule.span ℂ
      {V : G → ℂ | ∃ U ∈ LinearMap.range Λ₀, ∃ a : A, V = (fun g => U (g * u a)) - χ a • U}) :
    ∃ c : ℂ, ∀ x : X, Λ' x = c • Λ₀ x := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective Λ₀ (LinearMap.ker_eq_bot.mpr hinj)
  have hrΛ : ∀ x : X, r (Λ₀ x) = x := fun x => LinearMap.congr_fun hr x
  set ℓ : (G → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj (1 : G)).comp (Λ'.comp r) with hℓdef
  have hℓ : ∀ x : X, ℓ (Λ₀ x) = Λ' x 1 := by
    intro x
    simp only [hℓdef, LinearMap.comp_apply, LinearMap.proj_apply, hrΛ]
  have hequiv : ∀ W ∈ LinearMap.range Λ₀, ∀ a : A, ℓ (fun g => W (g * u a)) = χ a * ℓ W := by
    rintro W ⟨x, rfl⟩ a
    rw [← h₀ (u a) x, hℓ, hℓ, h' (u a) x]
    show Λ' x (1 * u a) = χ a * Λ' x 1
    have hx1 := hlaw x a 1
    rw [mul_one] at hx1
    rw [one_mul, hx1]
  obtain ⟨c, hc⟩ := exists_forall_eq_mul_apply_one_of_forall_mem_span_of_apply_one_eq_zero u χ
    (LinearMap.range Λ₀) hJ ℓ hequiv
  refine ⟨c, fun x => ?_⟩
  funext g
  have h1 : Λ' x g = ℓ (Λ₀ (π g x)) := by
    rw [hℓ, h' g x]
    show Λ' x g = Λ' x (1 * g)
    rw [one_mul]
  have h2 : (Λ₀ (π g x)) 1 = Λ₀ x g := by
    rw [h₀ g x]
    show Λ₀ x (1 * g) = Λ₀ x g
    rw [one_mul]
  rw [Pi.smul_apply, smul_eq_mul, h1, hc _ (LinearMap.mem_range_self Λ₀ _), h2]

end Range

theorem localFnAt_mul_right
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
    (g k : GL (Fin 2) (v.adicCompletion ℚ)) :
    AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v (fun y => φ (y * h)) (g * k) =
      AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v
        (fun y => φ (y * (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
          (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v k) * h))) g := by
  simp only [AutomorphicForm.WhittakerModel.localFnAt, AutomorphicForm.whittakerCoefficient, map_mul,
    mul_assoc]

theorem mul_right_mem_localSpaceAt
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (W : GL (Fin 2) (v.adicCompletion ℚ) → ℂ)
    (hW : W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ v φ)
    (k : GL (Fin 2) (v.adicCompletion ℚ)) :
    (fun g => W (g * k)) ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ v φ := by
  induction hW using Submodule.span_induction with
  | mem W hWmem =>
    obtain ⟨h, rfl⟩ := hWmem
    refine Submodule.subset_span ⟨AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
      (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v k) * h, ?_⟩
    funext g
    exact localFnAt_mul_right pins ψ v φ h g k
  | zero =>
    exact (AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ v φ).zero_mem
  | add W₁ W₂ _ _ h₁ h₂ =>
    exact (AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ v φ).add_mem h₁ h₂
  | smul c W _ h₁ =>
    exact (AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ v φ).smul_mem c h₁

theorem localFnAt_unipotentGL2_mul
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (hφ : ∀ (β : ℚ) (y : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      φ (AutomorphicForm.unipotentGL2
        (algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) β) * y) = φ y)
    (x : v.adicCompletion ℚ) (g : GL (Fin 2) (v.adicCompletion ℚ)) :
    AutomorphicForm.WhittakerModel.localFnAt ℚ (AutomorphicForm.productionPinsGeneral ℚ)
        NumberField.StandardAddChar.psiQ v φ (AutomorphicForm.unipotentGL2 x * g) =
      NumberField.StandardAddChar.psiV v x *
        AutomorphicForm.WhittakerModel.localFnAt ℚ (AutomorphicForm.productionPinsGeneral ℚ)
          NumberField.StandardAddChar.psiQ v φ g := by
  simp only [AutomorphicForm.WhittakerModel.localFnAt]
  rw [map_mul, map_mul, finEmbed_localEmbed_unipotentGL2]
  have key :
      AutomorphicForm.whittakerCoefficient ℚ (AutomorphicForm.productionPinsGeneral ℚ)
          NumberField.StandardAddChar.psiQ φ 1
          (AutomorphicForm.unipotentGL2 (singlePlaceAdeleAt v x) *
            AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
              (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g)) =
        NumberField.StandardAddChar.psiQ
            (algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) 1 *
              singlePlaceAdeleAt v x) *
          AutomorphicForm.whittakerCoefficient ℚ (AutomorphicForm.productionPinsGeneral ℚ)
            NumberField.StandardAddChar.psiQ φ 1
            (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
              (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g)) :=
    AutomorphicForm.whittakerCoefficient_unipotentGL2_mul ℚ _ _ _ NumberField.StandardAddChar.psiQ
      (fun q => NumberField.StandardAddChar.psiQ_algebraMap q) φ
      (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g))
      (fun β u => by rw [AutomorphicForm.unipotentGL2_add, mul_assoc, hφ]) 1 (singlePlaceAdeleAt v x)
  rw [key, map_one, one_mul, psiQ_singlePlaceAdeleAt]

theorem localFnAt_add
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (φ₁ φ₂ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (h₁ : ∀ g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      AutomorphicForm.WhittakerCoefficientIntegrable ℚ pins ψ φ₁ 1 g)
    (h₂ : ∀ g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      AutomorphicForm.WhittakerCoefficientIntegrable ℚ pins ψ φ₂ 1 g) :
    AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v (φ₁ + φ₂) =
      AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v φ₁ +
        AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v φ₂ := by
  funext g
  simp only [AutomorphicForm.WhittakerModel.localFnAt, AutomorphicForm.whittakerCoefficient, Pi.add_apply,
    add_mul]
  exact MeasureTheory.integral_add
    (h₁ (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
      (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g)))
    (h₂ (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
      (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g)))

theorem localFnAt_smul
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (c : ℂ) (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) :
    AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v (c • φ) =
      c • AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v φ := by
  funext g
  simp only [AutomorphicForm.WhittakerModel.localFnAt, AutomorphicForm.whittakerCoefficient, Pi.smul_apply,
    smul_eq_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul c _

theorem localFnAt_zero'
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v (0 : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) = 0 :=
  AutomorphicForm.WhittakerModel.localFnAt_zero pins ψ v

theorem whittakerCoefficientIntegrable_finset_sum
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    {ι : Type*} (s : Finset ι)
    (φs : ι → AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (h : ∀ i ∈ s, ∀ g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      AutomorphicForm.WhittakerCoefficientIntegrable ℚ pins ψ (φs i) 1 g)
    (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ) :
    AutomorphicForm.WhittakerCoefficientIntegrable ℚ pins ψ (∑ i ∈ s, φs i) 1 g := by
  unfold AutomorphicForm.WhittakerCoefficientIntegrable at h ⊢
  letI : MeasurableSpace (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) := pins.nS
  have hfun : (fun x : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ =>
      (∑ i ∈ s, φs i) (AutomorphicForm.unipotentGL2 x * g) *
        ψ (-(algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) 1 * x))) =
      fun x => ∑ i ∈ s, (φs i (AutomorphicForm.unipotentGL2 x * g) *
        ψ (-(algebraMap ℚ (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) 1 * x))) := by
    funext x
    rw [Finset.sum_apply, Finset.sum_mul]
  rw [hfun]
  exact MeasureTheory.integrable_finsetSum s (fun i hi => h i hi g)

theorem localFnAt_finset_sum
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {ι : Type*} (s : Finset ι)
    (φs : ι → AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ)
    (h : ∀ i ∈ s, ∀ g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      AutomorphicForm.WhittakerCoefficientIntegrable ℚ pins ψ (φs i) 1 g) :
    AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v (∑ i ∈ s, φs i) =
      ∑ i ∈ s, AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v (φs i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact localFnAt_zero' pins ψ v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have ha' : ∀ g, AutomorphicForm.WhittakerCoefficientIntegrable ℚ pins ψ (φs a) 1 g :=
      h a (Finset.mem_insert_self a s)
    have hs' : ∀ i ∈ s, ∀ g, AutomorphicForm.WhittakerCoefficientIntegrable ℚ pins ψ (φs i) 1 g :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    rw [localFnAt_add pins ψ v (φs a) (∑ i ∈ s, φs i) ha'
      (whittakerCoefficientIntegrable_finset_sum pins ψ s φs hs'), ih hs']

def restrictedWhittakerMap
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (f : X →ₗ[ℂ] (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ))
    (h' : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
    (hint : ∀ (y : X) (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      AutomorphicForm.WhittakerCoefficientIntegrable ℚ pins ψ (fun z => f y (z * h')) 1 g) :
    X →ₗ[ℂ] (GL (Fin 2) (v.adicCompletion ℚ) → ℂ) where
  toFun y := AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v (fun z => f y (z * h'))
  map_add' y₁ y₂ := by
    have hl : (fun z => f (y₁ + y₂) (z * h')) = (fun z => f y₁ (z * h')) + (fun z => f y₂ (z * h')) := by
      funext z
      simp only [map_add, Pi.add_apply]
    rw [hl]
    exact localFnAt_add pins ψ v _ _ (hint y₁) (hint y₂)
  map_smul' c y := by
    have hl : (fun z => f (c • y) (z * h')) = c • (fun z => f y (z * h')) := by
      funext z
      simp only [map_smul, Pi.smul_apply]
    rw [hl, RingHom.id_apply]
    exact localFnAt_smul pins ψ v c _

theorem restrictedWhittakerMap_apply
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (f : X →ₗ[ℂ] (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ))
    (h' : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
    (hint : ∀ (y : X) (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      AutomorphicForm.WhittakerCoefficientIntegrable ℚ pins ψ (fun z => f y (z * h')) 1 g)
    (y : X) :
    restrictedWhittakerMap pins ψ v f h' hint y =
      AutomorphicForm.WhittakerModel.localFnAt ℚ pins ψ v (fun z => f y (z * h')) :=
  rfl

theorem restrictedWhittakerMap_equivariant
    (pins : AutomorphicForm.CarrierPins ℚ)
    (ψ : AddChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) ℂ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    (π : GL (Fin 2) (v.adicCompletion ℚ) → X →ₗ[ℂ] X)
    (f : X →ₗ[ℂ] (AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ))
    (hf : ∀ (g : GL (Fin 2) (v.adicCompletion ℚ)) (y : X),
      f (π g y) = fun z => f y (z * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g)))
    (h' : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ)
    (hv : NumberField.AdelicLevel.finComponent (NumberField.RingOfIntegers ℚ) ℚ v
      (NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h') = 1)
    (hint : ∀ (y : X) (g : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      AutomorphicForm.WhittakerCoefficientIntegrable ℚ pins ψ (fun z => f y (z * h')) 1 g)
    (g : GL (Fin 2) (v.adicCompletion ℚ)) (y : X) :
    restrictedWhittakerMap pins ψ v f h' hint (π g y) =
      fun g' => restrictedWhittakerMap pins ψ v f h' hint y (g' * g) := by
  funext g'
  rw [restrictedWhittakerMap_apply, restrictedWhittakerMap_apply, localFnAt_mul_right]
  have hl : (fun z => f (π g y) (z * h')) =
      fun z => f y (z * (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g) * h')) := by
    funext z
    rw [hf g y]
    show f y (z * h' * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g)) =
      f y (z * (AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ
        (AdelicDock.localEmbed (NumberField.RingOfIntegers ℚ) ℚ v g) * h'))
    rw [mul_assoc, finEmbed_localEmbed_mul_comm v h' hv g]
  rw [hl]

open AutomorphicForm.CuspidalConstituent AutomorphicForm.WhittakerModel NumberField.StandardAddChar

theorem multiplicityOne (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V) (p : HeightOneSpectrum (𝓞 ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφV : φ ∈ V) :
    WhittakerModel.HasMultiplicityOneAt ℚ (productionPinsGeneral ℚ) psiQ φ p (psiV p) := by
  intro ℓ hℓ
  classical

  set S := localSpaceAt ℚ (productionPinsGeneral ℚ) psiQ p φ with hSdef
  have hSstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ S :=
    mul_right_mem_localSpaceAt (productionPinsGeneral ℚ) psiQ p φ

  by_cases hS0 : S = ⊥
  · refine ⟨0, fun W hW => ?_⟩
    rw [hS0, Submodule.mem_bot] at hW
    rw [hW, map_zero, Pi.zero_apply, mul_zero]

  have hsub : CuspidalConstituent.IsCuspSubrep ℚ (productionPinsGeneral ℚ) ξ V := hV.1
  have hcontV : ∀ y ∈ V, Continuous y := fun y hy =>
    continuous_of_mem_of_isCuspSubrep ℚ (productionPinsGeneral ℚ) ξ hsub hy
  have hratV : ∀ y ∈ V, ∀ (β : ℚ) (z : AdelicGL2 (𝓞 ℚ) ℚ),
      y (unipotentGL2 (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) β) * z) = y z := fun y hy β z =>
    apply_unipotentGL2_algebraMap_mul_eq_of_isCuspSubrep (productionPinsGeneral ℚ) ξ hsub hy β z
  have hintV : ∀ y ∈ V, ∀ (h' g : AdelicGL2 (𝓞 ℚ) ℚ),
      WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) psiQ (fun z => y (z * h')) 1 g :=
    fun y hy h' g => whittakerCoefficientIntegrable_productionPinsGeneral_of_continuous _
      (CuspidalConstituent.continuous_rightTranslate ℚ (hcontV y hy) h') 1 g

  obtain ⟨X, _, _, π, hsm, -, hirr, hadm, hdec⟩ :=
    CuspidalConstituent.IsCuspConstituent.exists_irreducible_admissible_isotypicAt ξ V hV p
  obtain ⟨n, x, f, hf, hφeq⟩ := hdec φ hφV
  have hfV : ∀ (i : Fin n) (y : X), f i y ∈ V := fun i y => (hf i).1 y
  have hf' : ∀ (i : Fin n) (g : GL (Fin 2) (p.adicCompletion ℚ)) (y : X),
      f i (π g y) = fun z => f i y (z * AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p g)) :=
    fun i g y => (hf i).2 g y
  have hintf : ∀ (i : Fin n) (h' : AdelicGL2 (𝓞 ℚ) ℚ) (y : X) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) psiQ (fun z => f i y (z * h')) 1 g :=
    fun i h' y g => hintV _ (hfV i y) h' g

  let Λ : Fin n → AdelicGL2 (𝓞 ℚ) ℚ → (X →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)) :=
    fun i h' => restrictedWhittakerMap (productionPinsGeneral ℚ) psiQ p (f i) h' (hintf i h')
  have hΛapply : ∀ i h' y, Λ i h' y = localFnAt ℚ (productionPinsGeneral ℚ) psiQ p (fun z => f i y (z * h')) :=
    fun _ _ _ => rfl
  have hΛequiv : ∀ (i : Fin n) (h' : AdelicGL2 (𝓞 ℚ) ℚ),
      AdelicLevel.finComponent (𝓞 ℚ) ℚ p (AdelicLevel.glFin (𝓞 ℚ) ℚ h') = 1 →
      ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)) (y : X), Λ i h' (π g y) = fun g' => Λ i h' y (g' * g) :=
    fun i h' hh' g y => restrictedWhittakerMap_equivariant (productionPinsGeneral ℚ) psiQ p
      (fun g => (π g : X →ₗ[ℂ] X)) (f i) (hf' i) h' hh' (hintf i h') g y
  have hΛlaw : ∀ (i : Fin n) (h' : AdelicGL2 (𝓞 ℚ) ℚ) (y : X) (xx : p.adicCompletion ℚ)
      (g : GL (Fin 2) (p.adicCompletion ℚ)), Λ i h' y (unipotentGL2 xx * g) = psiV p xx * Λ i h' y g := by
    intro i h' y xx g
    rw [hΛapply]
    exact localFnAt_unipotentGL2_mul p (fun z => f i y (z * h'))
      (fun β z => by
        show f i y (unipotentGL2 _ * z * h') = f i y (z * h')
        rw [mul_assoc, hratV _ (hfV i y)]) xx g

  have hgen : ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, ∃ (k : GL (Fin 2) (p.adicCompletion ℚ)) (h' : AdelicGL2 (𝓞 ℚ) ℚ),
      AdelicLevel.finComponent (𝓞 ℚ) ℚ p (AdelicLevel.glFin (𝓞 ℚ) ℚ h') = 1 ∧
      localFnAt ℚ (productionPinsGeneral ℚ) psiQ p (fun z => φ (z * h)) = ∑ i, Λ i h' (π k (x i)) := by
    intro h
    obtain ⟨k, h', hk, rfl⟩ := exists_finComponent_eq_one_and_eq_finEmbed_localEmbed_mul p h
    refine ⟨k, h', hk, ?_⟩
    have hφfun : (fun z => φ (z * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p k) * h'))) =
        ∑ i, (fun z => f i (π k (x i)) (z * h')) := by
      funext z
      rw [Finset.sum_apply, hφeq, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hf' i k (x i)]
      show f i (x i) (z * (AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p k) * h')) =
        f i (x i) (z * h' * AdelicDock.finEmbed (𝓞 ℚ) ℚ (AdelicDock.localEmbed (𝓞 ℚ) ℚ p k))
      rw [mul_assoc, finEmbed_localEmbed_mul_comm p h' hk k]
    rw [hφfun, localFnAt_finset_sum (productionPinsGeneral ℚ) psiQ p Finset.univ
      (fun i => fun z => f i (π k (x i)) (z * h')) (fun i _ g => hintf i h' (π k (x i)) g)]
    exact Finset.sum_congr rfl fun i _ => (hΛapply i h' _).symm

  have hex : ∃ (i : Fin n) (h' : AdelicGL2 (𝓞 ℚ) ℚ),
      AdelicLevel.finComponent (𝓞 ℚ) ℚ p (AdelicLevel.glFin (𝓞 ℚ) ℚ h') = 1 ∧ Λ i h' ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hS0
    rw [hSdef]
    unfold localSpaceAt
    rw [Submodule.span_eq_bot]
    rintro W ⟨h, rfl⟩
    obtain ⟨k, h', hk, hW⟩ := hgen h
    rw [hW]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hnone i h' hk, LinearMap.zero_apply]
  obtain ⟨i₀, h₀, hh₀, hne⟩ := hex

  set e : X →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) := Λ i₀ h₀ with hedef
  have heequiv : ∀ (g : GL (Fin 2) (p.adicCompletion ℚ)) (y : X), e (π g y) = fun g' => e y (g' * g) :=
    hΛequiv i₀ h₀ hh₀
  have hinj : Function.Injective e := injective_of_forall_eq_bot_or_eq_top_of_ne_zero π hirr e heequiv hne
  set M : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) := LinearMap.range e with hMdef
  have hMstab : ∀ W ∈ M, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ M :=
    mul_right_mem_range_of_equivariant π e heequiv
  have hMsm : ∀ W ∈ M, ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W :=
    exists_isOpen_forall_eq_of_mem_range_of_equivariant π hsm e heequiv
  have hMlaw : ∀ W ∈ M, ∀ (xx : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (unipotentGL2 xx * g) = psiV p xx * W g := by
    rintro W ⟨y, rfl⟩ xx g
    exact hΛlaw i₀ h₀ y xx g
  have hMirr : ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ M →
      (∀ W ∈ T, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = M :=
    eq_bot_or_eq_range_of_le_range_of_equivariant π hirr e heequiv
  have hMadm : ∀ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ M →
        (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T :=
    finiteDimensional_of_le_range_of_forall_eq_of_injective π hadm e heequiv hinj

  have hJ := AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible
    p M hMstab hMsm hMlaw hMirr hMadm

  have hΛM : ∀ (i : Fin n) (h' : AdelicGL2 (𝓞 ℚ) ℚ),
      AdelicLevel.finComponent (𝓞 ℚ) ℚ p (AdelicLevel.glFin (𝓞 ℚ) ℚ h') = 1 → ∀ y : X, Λ i h' y ∈ M := by
    intro i h' hh' y
    obtain ⟨c, hc⟩ := exists_forall_eq_smul_of_injective_of_forall_mem_span π unipotentGL2
      (fun xx => psiV p xx) e (Λ i h') heequiv (hΛequiv i h' hh') hinj (fun y a g => hΛlaw i h' y a g) hJ
    rw [hc y]
    exact M.smul_mem c (LinearMap.mem_range_self e y)

  have hSM : S ≤ M := by
    rw [hSdef]
    unfold localSpaceAt
    rw [Submodule.span_le]
    rintro W ⟨h, rfl⟩
    obtain ⟨k, h', hk, hW⟩ := hgen h
    rw [SetLike.mem_coe, hW]
    exact M.sum_mem fun i _ => hΛM i h' hk _

  have hSsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W :=
    fun W hW => hMsm W (hSM hW)
  have hSlaw : ∀ W ∈ S, ∀ (xx : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (unipotentGL2 xx * g) = psiV p xx * W g := fun W hW => hMlaw W (hSM hW)
  have hSirr : ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = S := by
    intro T hTS hTstab
    rcases hMirr T (hTS.trans hSM) hTstab with hbot | htop
    · exact Or.inl hbot
    · refine Or.inr (le_antisymm hTS ?_)
      rw [htop]
      exact hSM
  have hSadm : ∀ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
        (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T :=
    fun K hK T hTS hfix => hMadm K hK T (hTS.trans hSM) hfix

  have hJS := AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible
    p S hSstab hSsm hSlaw hSirr hSadm

  have hkerD : ∀ D ∈ Submodule.span ℂ
      {D : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
        D = (fun g => U (g * unipotentGL2 x)) - psiV p x • U}, ℓ D = 0 := by
    intro D hD
    induction hD using Submodule.span_induction with
    | mem D hD =>
      obtain ⟨U, hU, x, rfl⟩ := hD
      rw [map_sub, map_smul, hℓ U hU x, smul_eq_mul, sub_self]
    | zero => exact map_zero ℓ
    | add D₁ D₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
    | smul c D _ h₁ => rw [map_smul, h₁, smul_zero]
  have hker : ∀ W ∈ S, W 1 = 0 → ℓ W = 0 := fun W hW h1 => hkerD W (hJS W hW h1)

  by_cases hev : ∀ W ∈ S, W 1 = 0
  · exact ⟨0, fun W hW => by rw [hker W hW (hev W hW), zero_mul]⟩
  · push Not at hev
    obtain ⟨W₁, hW₁, hW₁1⟩ := hev
    refine ⟨ℓ W₁ / W₁ 1, fun W hW => ?_⟩
    have hdS : W - (W 1 / W₁ 1) • W₁ ∈ S := S.sub_mem hW (S.smul_mem _ hW₁)
    have hd1 : (W - (W 1 / W₁ 1) • W₁) 1 = 0 := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [div_mul_cancel₀ _ hW₁1, sub_self]
    have h0 := hker _ hdS hd1
    rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
    rw [h0]
    field_simp

end P2M.WPlusSelect

end

set_option autoImplicit false

p2m_open "IsDedekindDomain NumberField AutomorphicForm~det_centralScalar LanglandsTunnell LanglandsTunnell.Converse"
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace Ws47
namespace PIN

theorem exists_finset_norm_twist_b_eq_one
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
    (Θ : HeckeEigensystem ℚ ℂ) (hΘ : Θ.AgreesAwayFromFinite Φ) :
    ∃ S₁ : Finset (HeightOneSpectrum (𝓞 ℚ)), ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S₁ →
      ‖(Θ.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).b p‖ = 1 := by
  classical
  obtain ⟨S₀, hS₀⟩ :=
    LanglandsTunnell.exists_finset_norm_b_eq_absNorm_of_whittakerCoefficient_fibre_eq_archW_of_re_centralExponent_eq_zero
      c u d₁ d₂ T hd hcov Φ P archC dR dC hWF hP0
  obtain ⟨S₂, hS₂⟩ := hΘ
  refine ⟨S₀ ∪ S₂, fun p hp => ?_⟩
  have hp0 : p ∉ S₀ := fun h => hp (Finset.mem_union_left _ h)
  have hp2 : p ∉ S₂ := fun h => hp (Finset.mem_union_right _ h)
  have hN : (0 : ℝ) < (Ideal.absNorm p.asIdeal : ℝ) :=
    Nat.cast_pos.2 (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 p.ne_bot))
  rw [HeckeEigensystem.twist_b, (hS₂ p hp2).2, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hN _), hS₀ p hp0, ← Real.rpow_natCast,
    ← Real.rpow_mul hN.le, show (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 by norm_num, Real.rpow_neg_one,
    inv_mul_cancel₀ hN.ne']

end Ws47.PIN

section
p2m_open "NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory"
p2m_open "AutomorphicForm~det_centralScalar AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"

end

namespace Ws47
namespace PIN
namespace L7

open NumberField.AdelicVolume MeasureTheory Matrix

theorem unipotentGL2_mul_centralScalar {F : Type} [Field F] [NumberField F]
    (x : AdeleRing (𝓞 F) F) (w : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    unipotentGL2 x * (centralScalar (𝓞 F) F w * g) = centralScalar (𝓞 F) F w * (unipotentGL2 x * g) := by
  rw [← mul_assoc, ← mul_assoc]
  congr 1
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, centralScalar_val, ← Matrix.scalar_apply]
  exact ((Matrix.scalar_commute (w : AdeleRing (𝓞 F) F) (Commute.all _) _).eq).symm

theorem whittakerCoefficient_centralScalar_mul {F : Type} [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : ∀ (zz : pins.Z) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F (zz : (AdeleRing (𝓞 F) F)ˣ) * g) = ((ξ zz : ℂˣ) : ℂ) * φ g)
    (zz : pins.Z) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ α (centralScalar (𝓞 F) F (zz : (AdeleRing (𝓞 F) F)ˣ) * g)
      = ((ξ zz : ℂˣ) : ℂ) * whittakerCoefficient F pins ψ φ α g := by
  letI := pins.nS
  simp only [whittakerCoefficient]
  simp_rw [unipotentGL2_mul_centralScalar, hφ, mul_assoc]
  exact integral_const_mul _ _

private theorem _root_.Ws47.PIN.L7.central_transform {F : Type} [Field F] [NumberField F] {pins : CarrierPins F}
    {Ψ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Ψ)
    (zz : pins.Z) (g : AdelicGL2 (𝓞 F) F) :
    R.toFun (centralScalar (𝓞 F) F (zz : (AdeleRing (𝓞 F) F)ˣ) * g) = ((R.centralChar zz : ℂˣ) : ℂ) * R.toFun g := by
  letI := pins.mS
  exact (((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z R.centralChar pins.D R.toFun).mp
    R.smoothCusp.1.1).1).central_transform zz g

p2m_export "Ws47.PIN.L7" "central_transform"

variable {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (w.Completion)ˣ)

noncomputable def archScalar (a : (w.Completion)ˣ) : AdelicGL2 (𝓞 ℚ) ℚ :=
  centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w a)

theorem glFin_archScalar : glFin (𝓞 ℚ) ℚ (archScalar a) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [archScalar, glFin_apply, centralScalar_val, Matrix.diagonal_apply, Units.val_one]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Matrix.one_apply_eq]
    exact archCentralUnit_snd w a
  · rw [if_neg h, Matrix.one_apply_ne h]
    rfl

theorem glFin_archScalar_mul (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    glFin (𝓞 ℚ) ℚ (archScalar a * g) = glFin (𝓞 ℚ) ℚ g := by
  rw [map_mul, glFin_archScalar, one_mul]

theorem archComponent_glArch_archScalar :
    ((archComponent ℚ w (glArch (𝓞 ℚ) ℚ (archScalar a)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) = Matrix.diagonal (fun _ => (a : w.Completion)) := by
  ext i j
  rw [archComponent_apply, glArch_apply, archScalar]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, Matrix.diagonal_apply_eq]
    exact archCentralUnit_fst_self w a
  · rw [centralScalar_apply_ne _ h, Matrix.diagonal_apply_ne _ h]
    rfl

include hw in
theorem realComponent_eq (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    realComponent w hw g = (ringEquivRealOfIsReal hw).toRingHom.mapMatrix
      ((archComponent ℚ w (glArch (𝓞 ℚ) ℚ g) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) := by
  ext i j; rfl

include hw in
theorem realComponent_archScalar_mul (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    realComponent w hw (archScalar a * g)
      = (ringEquivRealOfIsReal hw (a : w.Completion)) • realComponent w hw g := by
  rw [realComponent_eq, realComponent_eq, map_mul, map_mul, Units.val_mul, archComponent_glArch_archScalar,
    map_mul, Matrix.smul_eq_diagonal_mul]
  congr 1
  rw [RingHom.mapMatrix_apply, Matrix.diagonal_map (map_zero _)]
  rfl

include hw in
theorem prod_archDetNorm_archScalar_mul (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∏ v : InfinitePlace ℚ, archDetNorm v (archScalar a * g) ^ v.mult
      = (‖(a : w.Completion)‖ * ‖(a : w.Completion)‖) * ∏ v : InfinitePlace ℚ, archDetNorm v g ^ v.mult := by
  rw [Fintype.prod_subsingleton _ w, Fintype.prod_subsingleton _ w, NumberField.InfinitePlace.mult, if_pos hw,
    pow_one, pow_one, archScalar, archDetNorm_centralScalar_mul]

include hw in
theorem archW_archScalar_mul (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (ht : ringEquivRealOfIsReal hw (a : w.Completion) ≠ 0) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    archW (fun _ _ => P) archC dR dC (archScalar a * g)
      = ArchR.centralChar P (ringEquivRealOfIsReal hw (a : w.Completion)) *
          ((|ringEquivRealOfIsReal hw (a : w.Completion)| : ℝ) : ℂ) * archW (fun _ _ => P) archC dR dC g := by
  unfold archW
  rw [Fintype.prod_subsingleton _ w, Fintype.prod_subsingleton _ w, dif_pos hw, dif_pos hw,
    realComponent_archScalar_mul hw a g, (dR w hw).central_law _ _ ht]

theorem norm_centralChar_of_pos (P : RealArchParam) {t : ℝ} (ht : 0 < t) :
    ‖ArchR.centralChar P t‖ = t ^ (RealArchParam.centralExponent P).re := by
  unfold ArchR.centralChar ArchR.quasiChar
  rw [norm_mul, abs_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  split_ifs
  · rw [norm_one, mul_one]
  · rw [sign_pos ht, SignType.coe_one, Complex.ofReal_one, norm_one, mul_one]

theorem abs_mul_abs_mul_rpow (t X : ℝ) (hX : 0 ≤ X) :
    (|t| * |t| * X) ^ (-(1 / 2 : ℝ)) = |t|⁻¹ * X ^ (-(1 / 2 : ℝ)) := by
  rw [Real.mul_rpow (mul_nonneg (abs_nonneg t) (abs_nonneg t)) hX]
  congr 1
  rw [show |t| * |t| = |t| ^ (2 : ℝ) by rw [Real.rpow_two, sq], ← Real.rpow_mul (abs_nonneg t),
    show (2 : ℝ) * -(1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]

theorem prod_archDetNorm_nonneg (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    0 ≤ ∏ v : InfinitePlace ℚ, archDetNorm v g ^ v.mult :=
  Finset.prod_nonneg fun v _ => pow_nonneg (archDetNorm_pos v g).le _

theorem det_diagOne_adele (F : Type) [Field F] [NumberField F] (a : (AdeleRing (𝓞 F) F)ˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  ext
  show (Matrix.diagonal ![((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F), 1]).det
    = ((a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

theorem det_heckeGen_eq_uniformizerIdele (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v) = uniformizerIdele F v := by
  show Matrix.GeneralLinearGroup.det (diagOne (uniformizerIdele F v)) = uniformizerIdele F v
  exact det_diagOne_adele F _

include hw in

theorem centralChar_archCentralUnit_eq
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (Ψ : HeckeEigensystem ℚ ℂ)
    (R' : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
        (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Ψ)
    (P : RealArchParam) (archC : ∀ w : InfinitePlace ℚ, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ArchDatumR P)
    (dC : ∀ (w : InfinitePlace ℚ) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (g₀ g₁ : AdelicGL2 (𝓞 ℚ) ℚ) (z₀ : ℂ)
    (hg₁ : glFin (𝓞 ℚ) ℚ g₁ = glFin (𝓞 ℚ) ℚ g₀)
    (hW₁ : whittakerCoefficient ℚ
        (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        (NumberField.StandardAddChar.stdAddChar ℚ) R'.toFun 1 g₁ ≠ 0)
    (hfac : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ g = glFin (𝓞 ℚ) ℚ g₀ →
      whittakerCoefficient ℚ
        (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        (NumberField.StandardAddChar.stdAddChar ℚ) R'.toFun 1 g =
        (((∏ v : InfinitePlace ℚ, NumberField.AdelicVolume.archDetNorm v g ^ v.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
          archW (fun _ _ => P) archC dR dC g * z₀) :
    ((R'.centralChar ⟨archCentralUnit ℚ w a, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
      = ArchR.centralChar P (ringEquivRealOfIsReal hw (a : w.Completion)) := by
  set t : ℝ := ringEquivRealOfIsReal hw (a : w.Completion) with ht_def
  have ht : t ≠ 0 := by
    rw [ht_def, map_ne_zero_iff _ (ringEquivRealOfIsReal hw).injective]
    exact a.ne_zero
  have hta : ‖(a : w.Completion)‖ = |t| := by
    rw [ht_def, ← Real.norm_eq_abs, norm_ringEquivRealOfIsReal hw]
  have e1 := whittakerCoefficient_centralScalar_mul _ (NumberField.StandardAddChar.stdAddChar ℚ)
    (central_transform R') ⟨archCentralUnit ℚ w a, Subgroup.mem_top _⟩ 1 g₁
  have e2 := hfac (archScalar a * g₁) (by rw [glFin_archScalar_mul, hg₁])
  rw [prod_archDetNorm_archScalar_mul hw, archW_archScalar_mul hw a P archC dR dC ht, hta,
    abs_mul_abs_mul_rpow t _ (prod_archDetNorm_nonneg g₁)] at e2
  have e3 := hfac g₁ hg₁
  apply mul_right_cancel₀ hW₁
  rw [← e1, show centralScalar (𝓞 ℚ) ℚ
      ((⟨archCentralUnit ℚ w a, Subgroup.mem_top _⟩ :
        (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ)
          (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).Z) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g₁ = archScalar a * g₁ from rfl,
    e2, e3]
  have ht' : ((|t| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (abs_ne_zero.2 ht)
  push_cast
  field_simp
  ring

theorem centralChar_eq_isArchCompAt_rhs (P : RealArchParam) {w : InfinitePlace ℚ} (hw : w.IsReal)
    (a : (w.Completion)ˣ) :
    ArchR.centralChar P (ringEquivRealOfIsReal hw (a : w.Completion))
      = ((‖(a : w.Completion)‖ : ℂ) ^ ((w.mult : ℂ) * P.centralExponent)) *
        (extensionEmbedding w (a : w.Completion) / (‖(a : w.Completion)‖ : ℂ)) ^ (P.centralSign.val : ℤ) := by
  set t : ℝ := ringEquivRealOfIsReal hw (a : w.Completion) with ht_def
  have ht : t ≠ 0 := by
    rw [ht_def, map_ne_zero_iff _ (ringEquivRealOfIsReal hw).injective]
    exact a.ne_zero
  have ht' : ((|t| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (abs_ne_zero.2 ht)
  have hn : ‖(a : w.Completion)‖ = |t| := by
    rw [ht_def, ← Real.norm_eq_abs, norm_ringEquivRealOfIsReal hw]
  have he : (extensionEmbedding w (a : w.Completion) : ℂ) = (t : ℂ) :=
    (extensionEmbeddingOfIsReal_apply hw _).symm
  have hmult : w.mult = 1 := by rw [NumberField.InfinitePlace.mult, if_pos hw]
  rw [hn, he, hmult, Nat.cast_one, one_mul]
  unfold ArchR.centralChar ArchR.quasiChar
  congr 1
  have h01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  rcases h01 P.centralSign with h0 | h1
  · rw [h0, if_pos rfl, ZMod.val_zero, Int.ofNat_zero, zpow_zero]
  · rw [h1, if_neg (by decide), show (((1 : ZMod 2).val : ℕ) : ℤ) = 1 from rfl, zpow_one, eq_div_iff ht']
    exact_mod_cast sign_mul_abs t

end Ws47.PIN.L7

namespace Ws47
namespace PIN

theorem isArchCompAt_centralChar_of_classWitness
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
    (Θ : HeckeEigensystem ℚ ℂ) (hΘ : Θ.AgreesAwayFromFinite Φ)
    (R'' : SmoothCuspRealizationAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ.toRawCentral)
    (hR'' : Continuous R''.toFun) :
    IsArchCompAt ℚ (R''.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) Rat.infinitePlace
      P.centralExponent (P.centralSign.val : ℤ) := by

  obtain ⟨Θ', hΘ', R', hR', g₀, ⟨g₁, hg₁, hW₁⟩, z₀, hfac⟩ := hWF
  have hagree : Θ.AgreesAwayFromFinite Θ' :=
    TranslateSpanOccurrence.agrees_trans hΘ (TranslateSpanOccurrence.agrees_symm hΘ')
  have hcc : R''.centralChar = R'.centralChar :=
    AutomorphicForm.SmoothCuspRealizationAt.centralChar_eq_of_agreesAwayFromFinite ℚ _ Θ Θ' hagree R'' hR'' R' hR'
  intro x
  rw [archLocalChar_apply]
  have e1 : (R''.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) (AdelicVolume.archCentralUnit ℚ _ x)
      = R''.centralChar ⟨AdelicVolume.archCentralUnit ℚ _ x, Subgroup.mem_top _⟩ := rfl
  rw [e1, hcc, Ws47.PIN.L7.centralChar_archCentralUnit_eq Rat.isReal_infinitePlace x _ _ R' P archC dR dC g₀ g₁ z₀ hg₁ hW₁ hfac,
    Ws47.PIN.L7.centralChar_eq_isArchCompAt_rhs]

end Ws47.PIN

section
p2m_open "NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.AdelicBox"
p2m_open "AutomorphicForm~det_centralScalar AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open IsDedekindDomain
open scoped Classical

end

section
p2m_open "NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm~det_centralScalar AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain"

end

section
p2m_open "NumberField NumberField.InfinitePlace.NumberField IsDedekindDomain"

end

noncomputable section

namespace Ws47
namespace PIN
namespace L45S

open NumberField.TateGlobal NumberField.AdelicVolume Matrix
open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def nu (g : AdelicGL2 (𝓞 F) F) : ℝ := ideleNorm F (Matrix.GeneralLinearGroup.det g)

theorem nu_pos (g : AdelicGL2 (𝓞 F) F) : 0 < nu g := ideleNorm_pos _

theorem nu_mul (g h : AdelicGL2 (𝓞 F) F) : nu (g * h) = nu g * nu h := by
  simp only [nu, map_mul, ideleNorm_mul]

theorem archComponent_glArch_archRealGLAt_self {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent F w (glArch (𝓞 F) F (archRealGLAt hw m)) = glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  unfold archRealGLAt adelicArchGLInclAt
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_self]

theorem archComponent_glArch_archRealGLAt_of_ne {v w : InfinitePlace F} (hvw : v ≠ w) (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    archComponent F v (glArch (𝓞 F) F (archRealGLAt hw m)) = 1 := by
  unfold archRealGLAt adelicArchGLInclAt
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_of_ne F hvw]

omit [NumberField F] in
theorem norm_det_glEquivOfRingEquiv_symm {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    ‖((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det‖ = |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| := by
  have e : ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m : GL (Fin 2) w.Completion) :
      Matrix (Fin 2) (Fin 2) w.Completion) =
      ((ringEquivRealOfIsReal hw).symm.toRingHom).mapMatrix ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) := rfl
  rw [e, ← RingHom.map_det]
  have h := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det)
  rw [RingEquiv.apply_symm_apply] at h
  rw [show ((ringEquivRealOfIsReal hw).symm.toRingHom) ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
    (ringEquivRealOfIsReal hw).symm ((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det from rfl, ← h, Real.norm_eq_abs]

theorem archDetNorm_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) (v : InfinitePlace F) :
    archDetNorm v (archRealGLAt hw m) = if v = w then |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| else 1 := by
  unfold archDetNorm
  by_cases hvw : v = w
  · subst hvw
    rw [if_pos rfl, archComponent_glArch_archRealGLAt_self, norm_det_glEquivOfRingEquiv_symm]
  · rw [if_neg hvw, archComponent_glArch_archRealGLAt_of_ne hvw, Units.val_one, Matrix.det_one, norm_one]

theorem nu_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (m : GL (Fin 2) ℝ) :
    nu (archRealGLAt hw m : AdelicGL2 (𝓞 F) F) = |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| := by
  unfold nu
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F (archRealGLAt hw m)
    (by rw [show glFin (𝓞 F) F (archRealGLAt hw m) = 1 from glFin_adelicArchGLIncl F _]; exact Subgroup.one_mem _)]
  simp_rw [archDetNorm_archRealGLAt hw m]
  rw [Finset.prod_eq_single w]
  · rw [if_pos rfl, NumberField.InfinitePlace.mult, if_pos hw, pow_one]
  · intro v _ hvw
    rw [if_neg hvw, one_pow]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem nu_mul_archRealGLAt {w : InfinitePlace F} (hw : w.IsReal) (g : AdelicGL2 (𝓞 F) F) (m : GL (Fin 2) ℝ) :
    nu (g * archRealGLAt hw m) = nu g * |((m : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det| := by
  rw [nu_mul, nu_archRealGLAt]

theorem det_archFlowMatrix (d : ArchDir) (t : ℝ) :
    ((archFlowMatrix d t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  cases d
  · show ((splitTorusGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
    simp [splitTorusGL2, Matrix.det_fin_two_of, ← Real.exp_add]
  · show ((unipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
    simp [unipotentGL2, Matrix.det_fin_two_of]
  · show ((lowerUnipotentGL2 t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
    simp [lowerUnipotentGL2, Matrix.det_fin_two_of]

theorem nu_mul_archFlowAt {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) (g : AdelicGL2 (𝓞 F) F) :
    nu (g * archFlowAt hw d t) = nu g := by
  unfold archFlowAt
  rw [nu_mul_archRealGLAt, det_archFlowMatrix, abs_one, mul_one]

theorem nu_mul_adelicArchGLInclAt {w : InfinitePlace F} (hw : w.IsReal) (g : AdelicGL2 (𝓞 F) F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    nu (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)) = nu g := by
  rw [← archRealGLAt_glEquivOfRingEquiv hw, nu_mul_archRealGLAt]
  have hdet : (((k : GL (Fin 2) w.Completion)) : Matrix (Fin 2) (Fin 2) w.Completion).det = 1 :=
    ((mem_rowIsometrySubgroup₀_iff _).1 k.2).1
  have e : ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = (ringEquivRealOfIsReal hw).toRingHom.mapMatrix
        (((k : GL (Fin 2) w.Completion)) : Matrix (Fin 2) (Fin 2) w.Completion) := rfl
  rw [e, ← RingHom.map_det, hdet, map_one, abs_one, mul_one]

def twistFn (t : ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ := fun g => ((nu g ^ t : ℝ) : ℂ) * φ g

theorem hasArchCharacterAt₀_twistFn {w : InfinitePlace F} (hw : w.IsReal) (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (h : HasArchCharacterAt₀ F w χ φ) (t : ℝ) : HasArchCharacterAt₀ F w χ (twistFn t φ) := by
  intro k g
  simp only [twistFn, nu_mul_adelicArchGLInclAt hw, h k g]
  ring

theorem archDerivAt_twistFn {w : InfinitePlace F} (hw : w.IsReal) (d : ArchDir) (t : ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archDerivAt hw d (twistFn t φ) = twistFn t (archDerivAt hw d φ) := by
  funext g
  show deriv (fun s : ℝ => ((nu (g * archFlowAt hw d s) ^ t : ℝ) : ℂ) * φ (g * archFlowAt hw d s)) 0 =
    ((nu g ^ t : ℝ) : ℂ) * deriv (fun s : ℝ => φ (g * archFlowAt hw d s)) 0
  have e : (fun s : ℝ => ((nu (g * archFlowAt hw d s) ^ t : ℝ) : ℂ) * φ (g * archFlowAt hw d s)) =
      fun s => ((nu g ^ t : ℝ) : ℂ) * φ (g * archFlowAt hw d s) := by
    funext s; rw [nu_mul_archFlowAt]
  rw [e, deriv_const_mul_field]

theorem archCasimirAt_twistFn {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    archCasimirAt hw (twistFn t φ) = twistFn t (archCasimirAt hw φ) := by
  funext g
  simp only [archCasimirAt, archDerivAt_twistFn, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp only [twistFn, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem archCasimirAt_twistFn_of_eq {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ} {lam : ℂ}
    (h : archCasimirAt hw φ = lam • φ) : archCasimirAt hw (twistFn t φ) = lam • twistFn t φ := by
  rw [archCasimirAt_twistFn, h]
  funext g
  simp only [twistFn, Pi.smul_apply, smul_eq_mul]
  ring

theorem contDiff_det_of : ContDiff ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det) := by
  have h : (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det) = fun e => e 0 0 * e 1 1 - e 0 1 * e 1 0 := by
    funext e; simp [Matrix.det_fin_two]
  rw [h]
  have hp : ∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => e i j) := fun i j =>
    (contDiff_apply ℝ ℝ j).comp (contDiff_apply ℝ (Fin 2 → ℝ) i)
  exact ((hp 0 0).mul (hp 1 1)).sub ((hp 0 1).mul (hp 1 0))

theorem isArchSmoothAt_twistFn {w : InfinitePlace F} (hw : w.IsReal) (t : ℝ) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsArchSmoothAt hw φ) : IsArchSmoothAt hw (twistFn t φ) := by
  intro g
  have hform : ∀ e ∈ {e : Fin 2 → Fin 2 → ℝ | (Matrix.of e).det ≠ 0},
      ((nu (g * archRealLiftAt hw e) ^ t : ℝ) : ℂ) = (((nu g * ‖(Matrix.of e).det‖) ^ t : ℝ) : ℂ) := by
    intro e he
    rw [archRealLiftAt_of_det_ne_zero hw he, nu_mul_archRealGLAt, Real.norm_eq_abs]
    rfl
  have hreal : ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => (nu g * ‖(Matrix.of e).det‖) ^ t)
      {e | (Matrix.of e).det ≠ 0} := by
    intro e he
    have hne : (Matrix.of e).det ≠ 0 := he
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => ‖(Matrix.of e).det‖) e :=
      (contDiffAt_norm ℝ hne).comp e contDiff_det_of.contDiffAt
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => nu g * ‖(Matrix.of e).det‖) e := contDiffAt_const.mul h1
    have hne' : nu g * ‖(Matrix.of e).det‖ ≠ 0 := mul_ne_zero (nu_pos g).ne' (norm_ne_zero_iff.mpr hne)
    exact (h2.rpow_const_of_ne hne').contDiffWithinAt
  have hdet : ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 2 → Fin 2 → ℝ => ((nu (g * archRealLiftAt hw e) ^ t : ℝ) : ℂ))
      {e | (Matrix.of e).det ≠ 0} := by
    refine (Complex.ofRealCLM.contDiff.comp_contDiffOn hreal).congr fun e he => ?_
    simp only [Function.comp_apply, Complex.ofRealCLM_apply]
    exact hform e he
  exact hdet.mul (h g)

section Rat

variable {φ φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ} (t : ℝ)
  (hφ' : ∀ g, φ' g = ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * φ g)

include hφ' in
theorem eq_twistFn : φ' = twistFn t φ := funext hφ'

include hφ' in

theorem hasArchCharacterAt₀_of_twist (n : ℤ)
    (h : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map
      (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ) :
    ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ' := by
  intro w hw
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [eq_twistFn t hφ']
  exact hasArchCharacterAt₀_twistFn hw _ h t

include hφ' in

theorem isArchSmoothAt_of_twist (h : IsArchSmoothAt Rat.isReal_infinitePlace φ) :
    ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), IsArchSmoothAt hw φ' := by
  intro w hw
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [eq_twistFn t hφ']
  exact isArchSmoothAt_twistFn hw t h

include hφ' in

theorem archCasimirAt_of_twist (lam : ℂ) (h : archCasimirAt Rat.isReal_infinitePlace φ = lam • φ) :
    ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), archCasimirAt hw φ' = lam • φ' := by
  intro w hw
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [eq_twistFn t hφ']
  exact archCasimirAt_twistFn_of_eq hw t h

include hφ' in

theorem J_relation_of_twist (ε : ℂ)
    (h : ∀ g, φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) = ε * φ g) :
    ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∀ g, φ' (g * archRealGLAt hw UpperHalfPlane.J) = ε * φ' g := by
  intro w hw g
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [hφ', hφ', h g]
  have hJ : nu (g * archRealGLAt hw UpperHalfPlane.J) = nu g := by
    rw [nu_mul_archRealGLAt]
    simp [UpperHalfPlane.J, Matrix.det_fin_two_of]
  unfold nu at hJ
  rw [hJ]
  ring

include hφ' in

theorem lowering_of_twist
    (h : archDerivAt Rat.isReal_infinitePlace ArchDir.H φ
        - Complex.I • (archDerivAt Rat.isReal_infinitePlace ArchDir.E φ + archDerivAt Rat.isReal_infinitePlace ArchDir.Fm φ) = 0) :
    ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      archDerivAt hw ArchDir.H φ' - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ') = 0 := by
  intro w hw
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  rw [eq_twistFn t hφ', archDerivAt_twistFn, archDerivAt_twistFn, archDerivAt_twistFn]
  funext g
  have hg := congrFun h g
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul, twistFn] at hg ⊢
  rw [show ((nu g ^ t : ℝ) : ℂ) * archDerivAt hw ArchDir.H φ g -
      Complex.I * (((nu g ^ t : ℝ) : ℂ) * archDerivAt hw ArchDir.E φ g + ((nu g ^ t : ℝ) : ℂ) * archDerivAt hw ArchDir.Fm φ g)
      = ((nu g ^ t : ℝ) : ℂ) * (archDerivAt hw ArchDir.H φ g -
          Complex.I * (archDerivAt hw ArchDir.E φ g + archDerivAt hw ArchDir.Fm φ g)) by ring, hg, mul_zero]

end Rat

theorem hasArchCharacterAt₀_of_eq_ideleNorm_det_rpow_mul (t : ℝ) (φ φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ' : ∀ g, φ' g = ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * φ g) (n : ℤ)
    (h : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map
      (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ' :=
  hasArchCharacterAt₀_of_twist t hφ' n h w hw

theorem smooth_block_of_eq_ideleNorm_det_rpow_mul (t : ℝ) (φ φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ' : ∀ g, φ' g = ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ t : ℝ) : ℂ) * φ g)
    (h : IsArchSmoothAt Rat.isReal_infinitePlace φ) (w : InfinitePlace ℚ) (hw : w.IsReal) :
    IsArchSmoothAt hw φ' ∧
      (∀ lam : ℂ, archCasimirAt Rat.isReal_infinitePlace φ = lam • φ → archCasimirAt hw φ' = lam • φ') ∧
      (∀ ε : ℂ, (∀ g, φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) = ε * φ g) →
        ∀ g, φ' (g * archRealGLAt hw UpperHalfPlane.J) = ε * φ' g) ∧
      (archDerivAt Rat.isReal_infinitePlace ArchDir.H φ
          - Complex.I • (archDerivAt Rat.isReal_infinitePlace ArchDir.E φ + archDerivAt Rat.isReal_infinitePlace ArchDir.Fm φ) = 0 →
        archDerivAt hw ArchDir.H φ' - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ') = 0) :=
  ⟨isArchSmoothAt_of_twist t hφ' h w hw,
    fun lam hl => archCasimirAt_of_twist t hφ' lam hl w hw,
    fun ε hε => J_relation_of_twist t hφ' ε hε w hw,
    fun hlow => lowering_of_twist t hφ' hlow w hw⟩

end Ws47.PIN.L45S

end

namespace Ws47
namespace PIN
namespace L45

open NumberField.AdelicVolume

theorem centralChar_eq_of_toFun_eq {pins pins' : CarrierPins ℚ} (hZ : pins.Z = ⊤) (hZ' : pins'.Z = ⊤)
    {Θ Θ' : HeckeEigensystem ℚ ℂ}
    (R : SmoothCuspRealizationAt ℚ pins Θ) (R' : SmoothCuspRealizationAt ℚ pins' Θ') (h : R.toFun = R'.toFun)
    (zz : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    R.centralChar ⟨zz, hZ ▸ Subgroup.mem_top zz⟩ = R'.centralChar ⟨zz, hZ' ▸ Subgroup.mem_top zz⟩ := by
  obtain ⟨g, hg⟩ := R'.exists_ne_zero
  have hg' : R.toFun g ≠ 0 := by rw [h]; exact hg
  apply Units.ext
  rw [R.centralChar_apply_eq _ hg', R'.centralChar_apply_eq _ hg, h]

theorem det_centralScalar (zz : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 ℚ) ℚ zz) = zz * zz := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, centralScalar_val, Matrix.det_diagonal, Fin.prod_univ_two, Units.val_mul]

theorem ideleNorm_archCentralUnit {w : InfinitePlace ℚ} (hw : w.IsReal) (a : (w.Completion)ˣ) :
    ideleNorm ℚ (archCentralUnit ℚ w a) = ‖(a : w.Completion)‖ := by
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one ℚ _
    (archCentralUnit_snd w a), Fintype.prod_subsingleton _ w, archCentralUnit_fst_self,
    NumberField.InfinitePlace.mult, if_pos hw, pow_one]

theorem rpow_half_mul_self {x : ℝ} (hx : 0 ≤ x) : (x * x) ^ (1 / 2 : ℝ) = x := by
  rw [← sq, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

end Ws47.PIN.L45

namespace Ws47
namespace PIN

theorem exists_generalRealization_twist
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ)
    (R'' : SmoothCuspRealizationAt ℚ (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) Θ.toRawCentral)
    (hR'' : Continuous R''.toFun) :
    ∃ R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ)
        (Θ.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).toRawCentral,
      Continuous R.toFun ∧ R.exceptionalSet = R''.exceptionalSet ∧ R.toFun ≠ 0 ∧
      (∀ n : ℤ, HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) R''.toFun →
        ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) R.toFun) ∧
      (IsArchSmoothAt Rat.isReal_infinitePlace R''.toFun →
        ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), IsArchSmoothAt hw R.toFun ∧
          (∀ lam : ℂ, archCasimirAt Rat.isReal_infinitePlace R''.toFun = lam • R''.toFun → archCasimirAt hw R.toFun = lam • R.toFun) ∧
          (∀ ε : ℂ, (∀ g, R''.toFun (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) = ε * R''.toFun g) →
            ∀ g, R.toFun (g * archRealGLAt hw UpperHalfPlane.J) = ε * R.toFun g) ∧
          (archDerivAt Rat.isReal_infinitePlace ArchDir.H R''.toFun
              - Complex.I • (archDerivAt Rat.isReal_infinitePlace ArchDir.E R''.toFun + archDerivAt Rat.isReal_infinitePlace ArchDir.Fm R''.toFun) = 0 →
            archDerivAt hw ArchDir.H R.toFun - Complex.I • (archDerivAt hw ArchDir.E R.toFun + archDerivAt hw ArchDir.Fm R.toFun) = 0)) ∧
      (∀ (u : ℂ) (a : ℤ), IsArchCompAt ℚ (R''.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) Rat.infinitePlace u a →
        ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w (u + 1) a) := by

  classical

  obtain ⟨R₃, hR₃, hexc, htoFun⟩ :=
    AutomorphicForm.SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
      ℚ c u d₁ d₂ T hd₁ Θ R'' hR'' (1 / 2 : ℝ)

  obtain ⟨Rg, hRg⟩ := AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre
    c u d₁ d₂ T hc hd₁ hd hcov _ R₃ hR₃
  have hcc : Rg.centralChar = R₃.centralChar := by
    refine MonoidHom.ext fun zz => ?_
    exact Ws47.PIN.L45.centralChar_eq_of_toFun_eq rfl rfl Rg R₃ hRg zz
  have hsc : IsSmoothCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) R₃.centralChar R₃.toFun := by
    have h := Rg.smoothCusp
    rw [hRg, hcc] at h
    exact h
  let R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ)
      (Θ.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).toRawCentral :=
    { toFun := R₃.toFun
      exists_ne_zero := R₃.exists_ne_zero
      centralChar := R₃.centralChar
      smoothCusp := hsc
      level_invariant := fun g u hu => R₃.level_invariant g u hu
      exceptionalSet := R₃.exceptionalSet
      hecke_eigen := fun v hv => R₃.hecke_eigen v hv
      central_eigen := fun v hv g => R₃.central_eigen v hv g }
  have hRfun : R.toFun = R₃.toFun := rfl
  refine ⟨R, hR₃, hexc, R₃.toFun_ne_zero, ?_, ?_, ?_⟩
  · intro n hn w hw
    exact Ws47.PIN.L45S.hasArchCharacterAt₀_of_eq_ideleNorm_det_rpow_mul (1 / 2 : ℝ) R''.toFun R₃.toFun htoFun n hn w hw
  · intro hsm w hw
    exact Ws47.PIN.L45S.smooth_block_of_eq_ideleNorm_det_rpow_mul (1 / 2 : ℝ) R''.toFun R₃.toFun htoFun hsm w hw
  · intro u' a h w hw x
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    have hx := h x
    rw [archLocalChar_apply] at hx ⊢

    obtain ⟨g, hg⟩ := R''.exists_ne_zero
    have hν : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        ((ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := fun g =>
      Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (ideleNorm_pos _) _).ne'
    have hg₃ : R₃.toFun g ≠ 0 := by rw [htoFun]; exact mul_ne_zero (hν g) hg
    set zz : (AdeleRing (𝓞 ℚ) ℚ)ˣ := AdelicVolume.archCentralUnit ℚ Rat.infinitePlace x with hzz
    have e1 : ((R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) zz : ℂ)
        = R₃.toFun (centralScalar (𝓞 ℚ) ℚ zz * g) / R₃.toFun g :=
      R₃.centralChar_apply_eq ⟨zz, Subgroup.mem_top _⟩ hg₃
    have e2 : ((R''.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) zz : ℂ)
        = R''.toFun (centralScalar (𝓞 ℚ) ℚ zz * g) / R''.toFun g :=
      R''.centralChar_apply_eq ⟨zz, Subgroup.mem_top _⟩ hg
    have e3 : ideleNorm ℚ (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 ℚ) ℚ zz * g)) ^ (1 / 2 : ℝ)
        = ‖(x : Rat.infinitePlace.Completion)‖ * ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ (1 / 2 : ℝ) := by
      rw [map_mul, ideleNorm_mul, Ws47.PIN.L45.det_centralScalar, ideleNorm_mul,
        Real.mul_rpow (mul_nonneg (ideleNorm_pos _).le (ideleNorm_pos _).le) (ideleNorm_pos _).le,
        Ws47.PIN.L45.rpow_half_mul_self (ideleNorm_pos _).le, hzz,
        Ws47.PIN.L45.ideleNorm_archCentralUnit Rat.isReal_infinitePlace]
    rw [e1, htoFun, htoFun, e3]
    rw [e2] at hx
    have hxn : ((‖(x : Rat.infinitePlace.Completion)‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 x.ne_zero)
    rw [Complex.ofReal_mul, mul_assoc, mul_div_assoc, mul_div_mul_left _ _ (hν g), hx, ← mul_assoc]
    congr 1
    rw [NumberField.InfinitePlace.mult, if_pos Rat.isReal_infinitePlace, Nat.cast_one, one_mul, one_mul,
      Complex.cpow_add _ _ hxn, Complex.cpow_one, mul_comm]

end Ws47.PIN

noncomputable section

namespace Ws47
namespace PIN

namespace L9

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

end L9

namespace L9
namespace ReproducingClosure

p2m_open "AutomorphicForm~det_centralScalar NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicLevel IsDedekindDomain Filter Topology"
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

end L9.ReproducingClosure

namespace L9

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

private theorem exists_reproducing_window
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ)) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Ψ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ))
      Ψ.toRawCentral)
    (hR : Continuous R.toFun)
    (n : ℤ) (hn : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) R.toFun) :
    ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ R.toFun α = R.toFun := by
  classical
  have hw₀ : (default : InfinitePlace ℚ).IsReal := isReal_infinitePlace_rat default

  let χ := wtFam hw₀ n
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
  have harch : R.toFun ∈ archCutSubmodule ℚ tys := (mem_archCutSubmodule_wtFam_iff hw₀ n R.toFun).2 (hn _ hw₀)

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
      refine Submodule.mem_inf.2 ⟨?_, rightConv_mem_archCutSubmodule_ofChar χ R.toFun hQa⟩
      have hfact : IsFactorizableTestFn ℚ (ReproducingClosure.tensor a ff) :=
        ReproducingClosure.isFactorizableTestFn_tensor ha hff
      have hsupp : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, ReproducingClosure.tensor a ff x ≠ 0 → ∃ a' k : AdelicGL2 (𝓞 ℚ) ℚ,
          glFin (𝓞 ℚ) ℚ a' = 1 ∧ k ∈ levelOne (𝓞 ℚ) ℚ Ψ.level ⊓ finiteAdelicGL2Subgroup ℚ ∧ x = a' * k :=
        fun x hx => hffs x (right_ne_zero_of_mul hx)
      exact (AutomorphicForm.isIsotypicCuspFormAt_rightConv_of_isFactorizableTestFn_of_support_subset_of_coversModCentre
        c u d₁ d₂ T hd hcov Ψ R hR _ hfact hsupp).mem_isotypicCuspSubmodule)
    fa hfa (fun k => (hbi k).isArchBiFinite) (fun g => hlim g)
  exact ⟨ReproducingClosure.tensor a ff, ReproducingClosure.isFactorizableTestFn_tensor ha hff, hrepro⟩

end L9

theorem exists_isFactorizableTestFn_rightConv_eq_self
    (Ψ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Ψ.toRawCentral) (hR : Continuous R.toFun)
    (n : ℤ) (hn : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) R.toFun)
    (lam : ℂ) (hs : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), IsArchSmoothAt hw R.toFun ∧ archCasimirAt hw R.toFun = lam • R.toFun) :
    ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ R.toFun α = R.toFun :=
  L9.exists_reproducing_window (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num)
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat Ψ R hR n hn

end Ws47.PIN

end

namespace Ws47
namespace PIN
namespace L11
theorem one_eq_of_ne_zero_zmod_two : ∀ s : ZMod 2, ¬ s = 0 → (1 : ZMod 2) = s := by decide
end Ws47.PIN.L11

namespace Ws47
namespace PIN

namespace Parity

open NumberField.AdelicVolume MeasureTheory Matrix

private theorem _root_.Ws47.PIN.Parity.central_transform {F : Type} [Field F] [NumberField F] {pins : CarrierPins F}
    {Ψ : HeckeEigensystem F ℂ} (R : SmoothCuspRealizationAt F pins Ψ)
    (zz : pins.Z) (g : AdelicGL2 (𝓞 F) F) :
    R.toFun (centralScalar (𝓞 F) F (zz : (AdeleRing (𝓞 F) F)ˣ) * g) = ((R.centralChar zz : ℂˣ) : ℂ) * R.toFun g := by
  letI := pins.mS
  exact (((lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z R.centralChar pins.D R.toFun).mp
    R.smoothCusp.1.1).1).central_transform zz g

p2m_export "Ws47.PIN.Parity" "central_transform"

noncomputable def weylR : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mk'' (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (by rw [Matrix.det_fin_two_of]; norm_num)

theorem weylR_mem : weylR ∈ rowIsometrySubgroup₀ ℝ := weyl_mem_rowIsometrySubgroup₀ ℝ

noncomputable def rotPi : rowIsometrySubgroup₀ ℝ := ⟨weylR, weylR_mem⟩ * ⟨weylR, weylR_mem⟩

theorem rotPi_coe_coe : ((rotPi : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = -1 := by
  show ((weylR * weylR : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = -1
  rw [Units.val_mul]
  show (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; -1, 0] = -1
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem firstRowℂ_rotPi : firstRowℂ (rotPi : GL (Fin 2) ℝ) = -1 := by
  show firstRowℂ (weylR * weylR) = -1
  rw [firstRowℂ_mul_of_mem weylR_mem]
  have h : firstRowℂ weylR = ⟨0, 1⟩ := archWeightOneℝ_weyl
  rw [h]
  apply Complex.ext <;> simp

theorem archWeightCharℝ_apply_coe (n : ℤ) (k : rowIsometrySubgroup₀ ℝ) :
    (archWeightCharℝ n k : ℂ) = firstRowℂ (k : GL (Fin 2) ℝ) ^ n := by
  simp only [archWeightCharℝ, MonoidHom.coe_comp, Function.comp_apply, zpowGroupHom_apply,
    Units.val_zpow_eq_zpow_val]
  rfl

theorem archWeightCharℝ_rotPi (n : ℤ) : (archWeightCharℝ n rotPi : ℂ) = (-1) ^ n := by
  rw [archWeightCharℝ_apply_coe, firstRowℂ_rotPi]

variable {w : InfinitePlace ℚ} (hw : w.IsReal)

theorem symm_mem_rowIsometrySubgroup₀ (k : rowIsometrySubgroup₀ ℝ) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (k : GL (Fin 2) ℝ) ∈ rowIsometrySubgroup₀ w.Completion :=
  map_mem_rowIsometrySubgroup₀_of_normPreserving _
    (fun x => by
      rw [← norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm x), RingEquiv.apply_symm_apply])
    _ k.2

theorem rowIsometrySubgroup₀Map_symm (k : rowIsometrySubgroup₀ ℝ) :
    rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw)
      ⟨_, symm_mem_rowIsometrySubgroup₀ hw k⟩ = k := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [rowIsometrySubgroup₀Map, glEquivOfRingEquiv_apply_entry]

theorem adelicArchGLInclAt_rotPi :
    adelicArchGLInclAt ℚ w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (rotPi : GL (Fin 2) ℝ))
      = centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w (-1)) := by

  have hfin : glFin (𝓞 ℚ) ℚ (adelicArchGLInclAt ℚ w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (rotPi : GL (Fin 2) ℝ)))
      = glFin (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w (-1))) := by
    rw [glFin_centralScalar_archCentralUnit]
    exact glFin_adelicArchGLIncl ℚ _
  have harch : glArch (𝓞 ℚ) ℚ (adelicArchGLInclAt ℚ w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (rotPi : GL (Fin 2) ℝ)))
      = glArch (𝓞 ℚ) ℚ (centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w (-1))) := by
    show glArch (𝓞 ℚ) ℚ (adelicArchGLIncl ℚ (archGLIncl ℚ w _)) = _
    rw [glArch_adelicArchGLIncl]
    refine Units.ext (Matrix.ext fun i j => funext fun v => ?_)
    obtain rfl : v = w := Subsingleton.elim v w
    rw [← archComponent_apply, archComponent_archGLIncl_self,
      glEquivOfRingEquiv_apply_entry, rotPi_coe_coe, glArch_apply, centralScalar_val]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.neg_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq, map_neg, map_one,
        archCentralUnit_fst_self]
      rfl
    · rw [Matrix.neg_apply, Matrix.one_apply_ne hij, neg_zero, map_zero, Matrix.diagonal_apply_ne _ hij]
      rfl
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ ?_)
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing ℚ) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j) harch
    simpa [glArch_apply] using this
  · have := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j) hfin
    simpa [glFin_apply] using this

theorem centralScalar_comm (zz : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    g * centralScalar (𝓞 ℚ) ℚ zz = centralScalar (𝓞 ℚ) ℚ zz * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, centralScalar_val, ← Matrix.scalar_apply]
  exact (Matrix.scalar_commute (zz : AdeleRing (𝓞 ℚ) ℚ) (Commute.all _) _).eq.symm

theorem intCast_zmod_two_eq_of_neg_one_zpow_eq {n m : ℤ} (h : (-1 : ℂ) ^ n = (-1) ^ m) :
    (n : ZMod 2) = (m : ZMod 2) := by
  have key : ∀ k : ℤ, (k : ZMod 2) = if Even k then 0 else 1 := by
    intro k
    split_ifs with hk
    · exact (ZMod.intCast_eq_zero_iff_even).2 hk
    · have h01 : ∀ s : ZMod 2, ¬ s = 0 → s = 1 := by decide
      exact h01 _ (fun h0 => hk ((ZMod.intCast_eq_zero_iff_even).1 h0))
  rw [key n, key m]
  rcases Int.even_or_odd n with hn | hn <;> rcases Int.even_or_odd m with hm | hm
  · simp [hn, hm]
  · exfalso
    rw [hn.neg_one_zpow, hm.neg_one_zpow] at h
    norm_num at h
  · exfalso
    rw [hn.neg_one_zpow, hm.neg_one_zpow] at h
    norm_num at h
  · rw [if_neg (Int.not_even_iff_odd.2 hn), if_neg (Int.not_even_iff_odd.2 hm)]

end Parity

theorem parity_of_archOccursInClassOf_archWeightChar
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
    (n : ℤ)
    (hn : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
      (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ)) :
    (n : ZMod 2) = P.centralSign := by
  classical
  obtain ⟨Θ₀, hΘ₀, R₀, hR₀, hwt₀⟩ := hn

  have hcomp := isArchCompAt_centralChar_of_classWitness c u d₁ d₂ T hc hd₁ hd hcov Φ P archC dR dC hWF hWT hDE hnv
    hgen htype hP0 Θ₀ hΘ₀ R₀ hR₀
  set hw₀ : (Rat.infinitePlace).IsReal := Rat.isReal_infinitePlace with hw₀_def

  have hcen : ((R₀.centralChar ⟨AdelicVolume.archCentralUnit ℚ Rat.infinitePlace (-1), Subgroup.mem_top _⟩ : ℂˣ) : ℂ)
      = (-1 : ℂ) ^ (P.centralSign.val : ℤ) := by
    have h := hcomp (-1)
    rw [archLocalChar_apply] at h
    have e1 : (R₀.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) (AdelicVolume.archCentralUnit ℚ Rat.infinitePlace (-1))
        = R₀.centralChar ⟨AdelicVolume.archCentralUnit ℚ Rat.infinitePlace (-1), Subgroup.mem_top _⟩ := rfl
    rw [e1] at h
    rw [h, Units.val_neg, Units.val_one, norm_neg, norm_one, Complex.ofReal_one, Complex.one_cpow, one_mul,
      div_one, map_neg, map_one]

  have hrot := hwt₀ ⟨_, Parity.symm_mem_rowIsometrySubgroup₀ hw₀ Parity.rotPi⟩
  obtain ⟨g, hg⟩ : ∃ g, R₀.toFun g ≠ 0 := by
    by_contra hall
    push Not at hall
    exact R₀.toFun_ne_zero (funext hall)
  have h1 := hrot g
  rw [MonoidHom.comp_apply, Parity.rowIsometrySubgroup₀Map_symm hw₀, Parity.archWeightCharℝ_rotPi] at h1

  have h2 : R₀.toFun (g * adelicArchGLInclAt ℚ Rat.infinitePlace
        ((⟨_, Parity.symm_mem_rowIsometrySubgroup₀ hw₀ Parity.rotPi⟩ : rowIsometrySubgroup₀ (Rat.infinitePlace).Completion) :
          GL (Fin 2) (Rat.infinitePlace).Completion))
      = (-1 : ℂ) ^ (P.centralSign.val : ℤ) * R₀.toFun g := by
    show R₀.toFun (g * adelicArchGLInclAt ℚ Rat.infinitePlace
      (glEquivOfRingEquiv (ringEquivRealOfIsReal hw₀).symm (Parity.rotPi : GL (Fin 2) ℝ))) = _
    rw [Parity.adelicArchGLInclAt_rotPi hw₀, Parity.centralScalar_comm, ← hcen]
    exact Parity.central_transform R₀ ⟨AdelicVolume.archCentralUnit ℚ Rat.infinitePlace (-1), Subgroup.mem_top _⟩ g
  rw [h2] at h1
  have h3 : (-1 : ℂ) ^ (P.centralSign.val : ℤ) = (-1) ^ n := mul_right_cancel₀ hg h1
  have h4 := Parity.intCast_zmod_two_eq_of_neg_one_zpow_eq h3.symm
  rw [h4, Int.cast_natCast, ZMod.natCast_zmod_val]

end Ws47.PIN

namespace Ws47
namespace PIN

theorem typedMinWitness
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
    (hP0 : (RealArchParam.centralExponent P).re = 0) :
    ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
      (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ ∧
          IsArchSmoothAt Rat.isReal_infinitePlace φ ∧ archCasimirAt Rat.isReal_infinitePlace φ = (laplaceEigenvalue P) • φ) := by
  have mono : ∀ {Q Q' : (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) → Prop}, (∀ φ, Q φ → Q' φ) →
      ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ Q → ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ Q' :=
    fun hQ ⟨Θ, hΘ, R, hR, hP⟩ => ⟨Θ, hΘ, R, hR, hQ _ hP⟩

  obtain ⟨hWc, hWfin, hWs, hWΩ⟩ :=
    LanglandsTunnell.Converse.continuous_archW_and_isArchSmoothAt_and_archCasimirAt_eq_of_isCasimirEigen ℚ
      (fun _ _ => P) archC dR dC Rat.infinitePlace Rat.isReal_infinitePlace (hDE _ _)

  obtain ⟨n₀, hn₀⟩ :=
    LanglandsTunnell.exists_archOccursInClassOf_archCasimirAt_laplaceEigenvalue_of_whittakerCoefficient_fibre_eq ℚ
      c u d₁ d₂ T hd hcov Φ Rat.infinitePlace Rat.isReal_infinitePlace P (archW (fun _ _ => P) archC dR dC) hWc hWfin hWs hWΩ hWF
  have hTrue : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ (fun _ => True) := mono (fun _ _ => trivial) hn₀

  obtain ⟨Pc, hgenc, htypec, hminc⟩ :=
    LanglandsTunnell.exists_realArchParam_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre ℚ
      c u d₁ d₂ T hd hcov Φ Rat.infinitePlace Rat.isReal_infinitePlace hTrue
  have hiff :=
    LanglandsTunnell.archOccursInClassOf_archCasimirAt_iff_of_archOccursInClassOf_minimalType_laplaceEigenvalue_of_coversModCentre ℚ
      c u d₁ d₂ T hd hcov Φ Rat.infinitePlace Rat.isReal_infinitePlace Pc (mono (fun φ h => ⟨h.1, h.2.1, h.2.2.2.1⟩) hminc)
  obtain ⟨hn₀T, hlam⟩ := (hiff n₀ (laplaceEigenvalue P)).mp hn₀
  have hpar : (n₀ : ZMod 2) = P.centralSign :=
    parity_of_archOccursInClassOf_archWeightChar c u d₁ d₂ T hc hd₁ hd hcov Φ P archC dR dC hWF hWT hDE hnv hgen htype hP0 n₀ (mono (fun φ h => h.1) hn₀)
  refine (hiff _ (laplaceEigenvalue P)).mpr ⟨?_, hlam⟩

  have hZ2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  clear hiff hminc hTrue hn₀ hWΩ hWs hWfin hWc mono
  cases P with
  | principal u₁ a₁ u₂ a₂ =>
    cases Pc with
    | principal v₁ b₁ v₂ b₂ =>
      change ((n₀ : ℤ) : ZMod 2) = b₁ + b₂ at hn₀T
      change ((n₀ : ℤ) : ZMod 2) = a₁ + a₂ at hpar
      show (((if a₁ + a₂ = 0 then (0 : ℤ) else 1) : ℤ) : ZMod 2) = b₁ + b₂
      rw [← hn₀T, hpar]
      by_cases h : a₁ + a₂ = 0
      · simp [h]
      · simp [h, (hZ2 _ h)]
    | discrete v m hm =>
      exfalso
      change laplaceEigenvalue (principal u₁ a₁ u₂ a₂) = laplaceEigenvalue (discrete v m hm) at hlam
      simp only [laplaceEigenvalue] at hlam
      have h2 : (u₁ - u₂) ^ 2 = (m : ℂ) ^ 2 := by linear_combination (-4) * hlam
      have hlt := htype u₁ u₂ a₁ a₂ rfl
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
      all_goals (rw [h] at hlt; simp at hlt; omega)
  | discrete u₀ m hm =>
    cases Pc with
    | principal v₁ b₁ v₂ b₂ =>
      exfalso
      change laplaceEigenvalue (discrete u₀ m hm) = laplaceEigenvalue (principal v₁ b₁ v₂ b₂) at hlam
      simp only [laplaceEigenvalue] at hlam
      have h2 : (v₁ - v₂) ^ 2 = (m : ℂ) ^ 2 := by linear_combination 4 * hlam
      have hlt := htypec v₁ v₂ b₁ b₂ rfl
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
      all_goals (rw [h] at hlt; simp at hlt; omega)
    | discrete v m' hm' =>
      change laplaceEigenvalue (discrete u₀ m hm) = laplaceEigenvalue (discrete v m' hm') at hlam
      simp only [laplaceEigenvalue] at hlam
      have h2 : ((m : ℕ) : ℂ) ^ 2 = ((m' : ℕ) : ℂ) ^ 2 := by linear_combination (-4) * hlam
      have hmm : m = m' := by
        have : (m : ℂ) = (m' : ℂ) ∨ (m : ℂ) = -(m' : ℂ) := sq_eq_sq_iff_eq_or_eq_neg.mp h2
        rcases this with h | h
        · exact_mod_cast h
        · exfalso
          have hre := congrArg Complex.re h
          simp at hre
          have : (0 : ℝ) < m := by exact_mod_cast hm
          have : (0 : ℝ) ≤ m' := by exact_mod_cast (Nat.zero_le m')
          linarith
      subst hmm
      show ((m : ℤ) + 1 ≤ |(m : ℤ) + 1| ∧ Even (((m : ℤ) + 1) - ((m : ℤ) + 1)))
      refine ⟨?_, by simp⟩
      rw [abs_of_nonneg (by positivity)]

end Ws47.PIN

namespace Ws47
namespace PIN

namespace L10

theorem zmod_two_add_self : ∀ a : ZMod 2, a + a = 0 := by decide
theorem zmod_two_add_ne_zero : ∀ a b : ZMod 2, a ≠ b → a + b ≠ 0 := by decide

theorem laplaceEigenvalue_principal_eq (u₀ : ℂ) (a₁ a₂ : ZMod 2) :
    laplaceEigenvalue (RealArchParam.principal u₀ a₁ u₀ a₂) = ((1 : ℤ) : ℂ) / 2 * (1 - ((1 : ℤ) : ℂ) / 2) := by
  rw [laplaceEigenvalue_principal]; push_cast; ring

theorem laplaceEigenvalue_discrete_eq (u₀ : ℂ) (m : ℕ) (hm : 1 ≤ m) :
    laplaceEigenvalue (RealArchParam.discrete u₀ m hm) = ((((m : ℤ) + 1 : ℤ)) : ℂ) / 2 * (1 - ((((m : ℤ) + 1 : ℤ)) : ℂ) / 2) := by
  rw [laplaceEigenvalue_discrete]; push_cast; ring

end L10

theorem typedMinWitness_sheet
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
    (hP0 : (RealArchParam.centralExponent P).re = 0) :
    ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
      (fun φ => (HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ (match (generalizing := false) P with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ ∧
          IsArchSmoothAt Rat.isReal_infinitePlace φ ∧ archCasimirAt Rat.isReal_infinitePlace φ = (laplaceEigenvalue P) • φ) ∧
        (∀ (u₁ u₂ : ℂ) (a₁ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₁ →
          ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * archRealGLAt Rat.isReal_infinitePlace UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ g) ∧
        (∀ (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n), P = RealArchParam.discrete u₀ n hn →
          archDerivAt Rat.isReal_infinitePlace ArchDir.H φ
            - Complex.I • (archDerivAt Rat.isReal_infinitePlace ArchDir.E φ + archDerivAt Rat.isReal_infinitePlace ArchDir.Fm φ) = 0) ∧
        (∀ (u₀ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
          archDerivAt Rat.isReal_infinitePlace ArchDir.H φ
            - Complex.I • (archDerivAt Rat.isReal_infinitePlace ArchDir.E φ + archDerivAt Rat.isReal_infinitePlace ArchDir.Fm φ) = 0)) := by
  classical
  have hw₀ : (Rat.infinitePlace).IsReal := Rat.isReal_infinitePlace

  have htyped := typedMinWitness c u d₁ d₂ T hc hd₁ hd hcov Φ P archC dR dC hWF hWT hDE hnv hgen htype hP0

  rcases P with ⟨u₁, a₁, u₂, a₂⟩ | ⟨u₀, m, hm⟩
  ·
    by_cases ha : a₁ = a₂
    ·
      subst ha
      have hsign :=
        LanglandsTunnell.archOccursInClassOf_archWeightChar_zero_archCasimirAt_apply_mul_J_eq_neg_one_pow_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
          c u d₁ d₂ T hc hd₁ hd hcov Φ _ archC dR dC hWF hWT hDE hnv hgen htype hP0 u₁ u₂ a₁ rfl
      refine hsign.mono fun φ hφ => ?_
      obtain ⟨hwt, hsm, hcas, hJ⟩ := hφ
      refine ⟨⟨?_, hsm, hcas⟩, ?_, ?_, ?_⟩
      · simpa [L10.zmod_two_add_self] using hwt
      · intro u₁' u₂' a₁' hP' g
        cases hP'
        exact hJ g
      · intro u₀ n hn hP'
        cases hP'
      · intro u₀ b₁ b₂ hP' hb
        cases hP'
        exact absurd rfl hb
    · have h0 : a₁ + a₂ ≠ 0 := L10.zmod_two_add_ne_zero a₁ a₂ ha
      by_cases hu : u₁ = u₂
      ·
        subst hu
        have h1 : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
            (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ 1).comp
                (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw₀) (norm_ringEquivRealOfIsReal hw₀))) φ ∧
              IsArchSmoothAt hw₀ φ ∧ archCasimirAt hw₀ φ = (laplaceEigenvalue (RealArchParam.principal u₁ a₁ u₁ a₂)) • φ) :=
          htyped.mono fun φ hφ => ⟨by simpa [h0] using hφ.1, hφ.2.1, hφ.2.2⟩
        have h2 := AutomorphicForm.archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
          ℚ c u d₁ d₂ T hd hcov Φ Rat.infinitePlace hw₀ 1 _ h1
        have h3 := AutomorphicForm.archOccursInClassOf_lower_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
          ℚ c u d₁ d₂ T hd hcov Φ Rat.infinitePlace hw₀ 1
          (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ (match (generalizing := false) (RealArchParam.principal u₁ a₁ u₁ a₂) with
              | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
              | .discrete _ m _ => (m : ℤ) + 1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ ∧
            IsArchSmoothAt Rat.isReal_infinitePlace φ ∧
            archCasimirAt Rat.isReal_infinitePlace φ = (laplaceEigenvalue (RealArchParam.principal u₁ a₁ u₁ a₂)) • φ)
          (h2.mono fun φ hφ => by
            obtain ⟨hwt, hsm, hdd, hcas⟩ := hφ
            refine ⟨⟨by simpa [h0] using hwt, hsm, hcas⟩, hwt, hsm, hdd, ?_⟩
            rw [hcas, L10.laplaceEigenvalue_principal_eq])
        refine h3.mono fun φ hφ => ?_
        obtain ⟨hP, hlow⟩ := hφ
        refine ⟨hP, ?_, ?_, ?_⟩
        · intro u₁' u₂' a₁' hP' g
          cases hP'
          exact absurd rfl ha
        · intro u₀ n hn hP'
          cases hP'
        · intro u₀ b₁ b₂ hP' hb
          exact hlow
      ·
        refine htyped.mono fun φ hφ => ⟨hφ, ?_, ?_, ?_⟩
        · intro u₁' u₂' a₁' hP' g
          cases hP'
          exact absurd rfl ha
        · intro u₀ n hn hP'
          cases hP'
        · intro u₀ b₁ b₂ hP' hb
          cases hP'
          exact absurd rfl hu
  ·
    have h1 : ArchOccursInClassOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂) Φ
        (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ ((m : ℤ) + 1)).comp
            (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw₀) (norm_ringEquivRealOfIsReal hw₀))) φ ∧
          IsArchSmoothAt hw₀ φ ∧ archCasimirAt hw₀ φ = (laplaceEigenvalue (RealArchParam.discrete u₀ m hm)) • φ) :=
      htyped.mono fun φ hφ => ⟨by simpa using hφ.1, hφ.2.1, hφ.2.2⟩
    have h2 := AutomorphicForm.archOccursInClassOf_continuous_foldr_archDerivAt_of_archOccursInClassOf_archCasimirAt_eq_smul_of_coversModCentre
      ℚ c u d₁ d₂ T hd hcov Φ Rat.infinitePlace hw₀ ((m : ℤ) + 1) _ h1
    have h3 := AutomorphicForm.archOccursInClassOf_lower_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
      ℚ c u d₁ d₂ T hd hcov Φ Rat.infinitePlace hw₀ ((m : ℤ) + 1)
      (fun φ => HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ (match (generalizing := false) (RealArchParam.discrete u₀ m hm) with
          | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
          | .discrete _ m _ => (m : ℤ) + 1)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ ∧
        IsArchSmoothAt Rat.isReal_infinitePlace φ ∧
        archCasimirAt Rat.isReal_infinitePlace φ = (laplaceEigenvalue (RealArchParam.discrete u₀ m hm)) • φ)
      (h2.mono fun φ hφ => by
        obtain ⟨hwt, hsm, hdd, hcas⟩ := hφ
        refine ⟨⟨by simpa using hwt, hsm, hcas⟩, hwt, hsm, hdd, ?_⟩
        rw [hcas, L10.laplaceEigenvalue_discrete_eq])
    refine h3.mono fun φ hφ => ?_
    obtain ⟨hP, hlow⟩ := hφ
    refine ⟨hP, ?_, ?_, ?_⟩
    · intro u₁' u₂' a₁' hP' g
      cases hP'
    · intro u₀' n hn hP'
      exact hlow
    · intro u₀' b₁ b₂ hP' hb
      cases hP'

end Ws47.PIN

open Ws47.PIN in
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
    (hP0 : (RealArchParam.centralExponent P).re = 0) :
    ∃ (Φ' : HeckeEigensystem ℚ ℂ) (S : Finset (HeightOneSpectrum (𝓞 ℚ))),
      Φ'.AgreesAwayFromFinite Φ ∧
      ∃ R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).toRawCentral,
      Continuous R.toFun ∧
      R.exceptionalSet ⊆ S ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          (P.centralExponent + 1) (P.centralSign.val : ℤ)) ∧
      ∃ (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ) (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)),
        (IsIsotypicCuspFormAt ℚ
            (productionPinsGeneral ℚ)
            R.centralChar (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)).level S (Φ'.twist fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) φ₁) ∧
        (φ₁ ≠ 0) ∧
        (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
          P = RealArchParam.principal u₁ a₁ u₂ a₂ →
            (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂)) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          P = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = P.laplaceEigenvalue • φ₁) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          P = RealArchParam.principal u₁ a₁ u₂ a₁ →
            ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ₁ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ₁ g) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          P = RealArchParam.discrete u₀ n hn →
            archDerivAt hw ArchDir.H φ₁
                - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
          P = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
            archDerivAt hw ArchDir.H φ₁
                - Complex.I • (archDerivAt hw ArchDir.E φ₁ + archDerivAt hw ArchDir.Fm φ₁) = 0) ∧

        CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) R.centralChar V ∧ φ₁ ∈ V ∧
        (∀ φ ∈ V,
              (∀ p : HeightOneSpectrum (𝓞 ℚ),
                ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ p φ,
                  W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ p φ,
                    W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                      fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
                (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
                  ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                    ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                      NumberField.StandardAddChar.psiQ p φ,
                      (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                        W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
                (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ p φ,
                  ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                    ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)))) ∧
        (∃ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 (diagOne a) ≠ 0) := by
  classical

  obtain ⟨Θ, hΘΦ, R'', hR''gen, ⟨hwt'', hsm'', hcas''⟩, hJ'', hlow'', hlow1''⟩ :=
    typedMinWitness_sheet c u d₁ d₂ T hc hd₁ hd hcov Φ P archC dR dC hWF hWT hDE hnv hgen htype hP0

  obtain ⟨R, hRc, hRexc, hRne, hRwt, hRsm, hRcen⟩ :=
    exists_generalRealization_twist c u d₁ d₂ T hc hd₁ hd hcov Θ R'' hR''gen

  have hcenP := isArchCompAt_centralChar_of_classWitness c u d₁ d₂ T hc hd₁ hd hcov Φ P archC dR dC hWF hWT hDE hnv hgen htype hP0 Θ hΘΦ R'' hR''gen
  have hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w (P.centralExponent + 1) (P.centralSign.val : ℤ) :=
    fun w hw => hRcen _ _ hcenP w hw
  have hwt := hRwt _ hwt''
  have hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw R.toFun ∧ archCasimirAt hw R.toFun = P.laplaceEigenvalue • R.toFun :=
    fun w hw => ⟨(hRsm hsm'' w hw).1, (hRsm hsm'' w hw).2.1 _ hcas''⟩
  have hJ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₁ →
      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, R.toFun (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * R.toFun g :=
    fun w hw u₁ u₂ a₁ hP => (hRsm hsm'' w hw).2.2.1 _ (hJ'' u₁ u₂ a₁ hP)
  have hlow : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n), P = RealArchParam.discrete u₀ n hn →
      archDerivAt hw ArchDir.H R.toFun - Complex.I • (archDerivAt hw ArchDir.E R.toFun + archDerivAt hw ArchDir.Fm R.toFun) = 0 :=
    fun w hw u₀ n hn hP => (hRsm hsm'' w hw).2.2.2 (hlow'' u₀ n hn hP)
  have hlow1 : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
      archDerivAt hw ArchDir.H R.toFun - Complex.I • (archDerivAt hw ArchDir.E R.toFun + archDerivAt hw ArchDir.Fm R.toFun) = 0 :=
    fun w hw u₀ a₁ a₂ hP hne => (hRsm hsm'' w hw).2.2.2 (hlow1'' u₀ a₁ a₂ hP hne)
  obtain ⟨α, hα⟩ := exists_isFactorizableTestFn_rightConv_eq_self _ R hRc _ hwt _ hpair
  have hiso0 := R.isIsotypicCuspFormAt hRc

  obtain ⟨V, φa, hV, hφaV, hisoa, hnea, hconva, hwta, hpaira, hJa, hlowa⟩ :=
    LanglandsTunnell.exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq
      R.centralChar _ (HeckeEigensystem.level_ne_bot _) R.exceptionalSet _ R.toFun hiso0 hRne ⟨α, hα⟩
      (fun w hw => ⟨_, hwt w hw⟩)

  obtain ⟨S', φb, hSS', hφbV, hisob, hneb, hconvb, hwtb, hpairb, hJb, -, hlowb, a₀, ha₀, hWb⟩ :=
    LanglandsTunnell.exists_mem_isCuspConstituent_isIsotypicCuspFormAt_whittakerCoefficient_diagOne_ne_zero_J_rigid_of_hasArchCharacterAt
      R.centralChar _ (HeckeEigensystem.level_ne_bot _) R.exceptionalSet _ V hV φa hφaV hisoa hnea
      (fun w hw => ⟨_, hwta w hw _ (hwt w hw)⟩)
  have hWfun : whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φb 1 ≠ 0 := by
    intro h0
    apply hWb
    rw [h0]
    rfl

  have hVloc := fun φ (hφ : φ ∈ V) (p : HeightOneSpectrum (𝓞 ℚ)) =>
    AutomorphicForm.CuspidalConstituent.IsCuspConstituent.localSpaceAt_cyclic_finite_fixed_smooth_of_hasMultiplicityOneAt
      R.centralChar V hV p φb hφbV hWfun (P2M.WPlusSelect.multiplicityOne R.centralChar V hV p φb hφbV) φ hφ
  refine ⟨Θ, S', hΘΦ, R, hRc, hSS', hcen, φb, (fun _ : InfinitePlace ℚ => (match (generalizing := false) P with
        | .principal _ a₁ _ a₂ => if a₁ + a₂ = 0 then (0 : ℤ) else 1
        | .discrete _ m _ => (m : ℤ) + 1)), V, hisob, hneb, hconvb,
    fun w hw => hwtb w hw _ (hwta w hw _ (hwt w hw)), ?_, ?_,
    fun w hw => hpairb w hw _ (hpaira w hw _ (hpair w hw)),
    fun w hw u₁ u₂ a₁ h g => hJb w hw _ (hJa w hw _ (hJ w hw u₁ u₂ a₁ h)) g,
    fun w hw u₀ n hn h => hlowb w hw (hlowa w hw (hlow w hw u₀ n hn h)),
    fun w hw u₀ a₁ a₂ h h12 => hlowb w hw (hlowa w hw (hlow1 w hw u₀ a₁ a₂ h h12)),
    hV, hφbV, hVloc, a₀, ha₀, hWb⟩
  · intro w hw u₁ u₂ a₁ a₂ hP
    subst hP
    by_cases h0 : a₁ + a₂ = 0
    · simp [h0]
    · refine ⟨Or.inr (by simp [h0]), ?_⟩
      simp only [h0, if_false, Int.cast_one]
      exact Ws47.PIN.L11.one_eq_of_ne_zero_zmod_two _ h0
  · intro w hw u₀ n hn hP
    subst hP
    rfl

end S_LanglandsTunnell_exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen
end P2MW
export P2MW.S_LanglandsTunnell_exists_agreesAwayFromFinite_twist_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_whittakerCoefficient_fibre_eq_archW_of_isCasimirEigen (solution)
