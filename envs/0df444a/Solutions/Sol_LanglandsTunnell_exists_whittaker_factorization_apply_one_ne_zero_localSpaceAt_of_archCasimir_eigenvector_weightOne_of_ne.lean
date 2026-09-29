-- Prove2me | solution 1 for LanglandsTunnell.exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/2b1c03a2-705d-5a38-af09-3e5c86daa85f

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicBox
import Mathlib.Analysis.MellinTransform
import Theorems.Thm_LanglandsTunnell_exists_whittaker_factorization_add_smul_reflect_lower_of_archCasimir_eigenvector_weightOne_of_ne
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar"
p2m_attr_erase "instance" "AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul"
p2m_attr_erase "simp" "TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace P2M
namespace WPlusFamilyOdd

open NumberField IsDedekindDomain MeasureTheory
open AutomorphicForm

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

theorem whittakerCoefficient_smul (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (c : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (c • φ) α g = c * whittakerCoefficient F pins ψ φ α g := by
  letI := pins.nS
  simp only [whittakerCoefficient, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _

theorem whittakerCoefficient_add (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    {φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ} {α : F} {g : AdelicGL2 (𝓞 F) F}
    (h₁ : WhittakerCoefficientIntegrable F pins ψ φ₁ α g) (h₂ : WhittakerCoefficientIntegrable F pins ψ φ₂ α g) :
    whittakerCoefficient F pins ψ (φ₁ + φ₂) α g =
      whittakerCoefficient F pins ψ φ₁ α g + whittakerCoefficient F pins ψ φ₂ α g := by
  letI := pins.nS
  unfold WhittakerCoefficientIntegrable at h₁ h₂
  simp only [whittakerCoefficient, Pi.add_apply, add_mul]
  exact integral_add h₁ h₂

theorem whittakerCoefficient_fun_zero (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (0 : AdelicGL2 (𝓞 F) F → ℂ) α g = 0 :=
  whittakerCoefficient_zero F pins ψ α g

theorem psiQ_archLine (w : InfinitePlace ℚ) (_hw : w.IsReal) (x : InfiniteAdeleRing ℚ)
    (_hx : ∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) :
    NumberField.StandardAddChar.psiQ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ)
      = Complex.exp (2 * Real.pi * Complex.I * InfinitePlace.Completion.extensionEmbedding w (x w)) := by
  rw [NumberField.StandardAddChar.psiQ_apply]
  show NumberField.StandardAddChar.psiArch x * NumberField.StandardAddChar.psiFin 0 = _
  rw [AddChar.map_zero_eq_one, mul_one, NumberField.StandardAddChar.psiArch_apply, finprod_eq_prod_of_fintype,
    Fintype.prod_subsingleton _ w, NumberField.StandardAddChar.psiArchPlace_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]

end P2M.WPlusFamilyOdd

end

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

theorem solution
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (_hR : Continuous R.toFun)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam)
    (_hS : R.exceptionalSet ⊆ S)
    (_htype : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1)
    (_hcen : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
        ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ))
    (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k₁ : InfinitePlace ℚ → ℤ)
    (_hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsGeneral ℚ)
        R.centralChar Φ.level S Φ φ₁)
    (_hne : φ₁ ≠ 0)
    (_hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₁ α = φ₁)
    (_hwt : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k₁ w)) φ₁)
    (_hminp : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₁ w = 0 ∨ k₁ w = 1) ∧ ((k₁ w : ZMod 2) = a₁ + a₂))
    (_hmind : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
      archR w hw = RealArchParam.discrete u₀ n hn → k₁ w = (n : ℤ) + 1)
    (_hpair : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
      IsArchSmoothAt hw φ₁ ∧ archCasimirAt hw φ₁ = (archR w hw).laplaceEigenvalue • φ₁)
    (_hne₂ : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
      archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ ∧ a₁ ≠ a₂ ∧ u₁ ≠ u₂)

    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (_hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) R.centralChar V) (_hφ₁V : φ₁ ∈ V)
    (_hVloc : ∀ φ ∈ V,
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
                ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))))
    (_htorus : ∃ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 (diagOne a) ≠ 0) :
    ∃ archR' : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam,
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal), archR' w hw = archR w hw ∨
        ∃ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ ∧
          archR' w hw = RealArchParam.principal u₁ a₂ u₂ a₁) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
          ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2)) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          ((archR' w hw).centralExponent + 1) ((archR' w hw).centralSign.val : ℤ)) ∧
      ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
      C 1 1 ≠ 0 ∧
      ∀ par : InfinitePlace ℚ → ZMod 2,
        ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wr : InfinitePlace ℚ → ℂ → ℂ) (k : InfinitePlace ℚ → ℤ),
          IsIsotypicCuspFormAt ℚ
              (productionPinsGeneral ℚ)
              R.centralChar Φ.level S Φ φ ∧
          φ ≠ 0 ∧
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
                ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))) ∧
          (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
            HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
            archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
              (k w : ℂ) = signShift (a₁ + par w) + signShift (a₂ + par w)) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            archR' w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
          (∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
              whittakerCoefficient ℚ
                  (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ φ 1 (diagOne a * g)
                = (∏ w : InfinitePlace ℚ, Wr w (extensionEmbedding w ((a : AdeleRing (𝓞 ℚ) ℚ).1 w)))
                    * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ →
              ∀ t : ℝ, Wr w (-t) = (-1 : ℂ) ^ a₁.val * Wr w t) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
            archR' w hw = RealArchParam.discrete u₀ n hn → ∀ t : ℝ, t < 0 → Wr w t = 0) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
            archR' w hw = RealArchParam.principal u₁ a₁ u₂ a₁ → par w = a₁ + 1 →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ a₁.val * Wr w (-t)) / (t : ℂ)) s
                    = (2 * s + u₁ + u₂ - 1) / (4 * (Real.pi : ℂ))
                        * ((archR' w hw).twist 0 a₁).archFactor s) ∧
          (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (b : ZMod 2),
            (b = par w ∨ b = par w + (archR' w hw).centralSign) →
              ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
                MellinConvergent
                    (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s ∧
                  mellin (fun t : ℝ => (Wr w t + (-1 : ℂ) ^ b.val * Wr w (-t)) / (t : ℂ)) s
                    = ((archR' w hw).twist 0 b).archFactor s) := by
  classical

  obtain ⟨w₀⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  have hw₀ : w₀.IsReal := isReal_infinitePlace_rat w₀
  have hcov : CoversModCentre ℚ
      (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) :=
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
  obtain ⟨u₁, u₂, a₁, a₂, hP, hapar, huu⟩ := _hne₂ w₀ hw₀
  have hμ0 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr huu

  set Tφ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      (archDerivAt hw₀ ArchDir.H φ₁
        - Complex.I • (archDerivAt hw₀ ArchDir.E φ₁ + archDerivAt hw₀ ArchDir.Fm φ₁))
          (g * archRealGLAt hw₀ UpperHalfPlane.J) with hTφdef
  have hlowV : (archDerivAt hw₀ ArchDir.H φ₁
      - Complex.I • (archDerivAt hw₀ ArchDir.E φ₁ + archDerivAt hw₀ ArchDir.Fm φ₁)) ∈ V := by
    let χ : ∀ v : InfinitePlace ℚ, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
      fun v => archWeightCharAt (isReal_infinitePlace_rat v) (k₁ v)
    let χ' : ℤ → ∀ v : InfinitePlace ℚ, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
      fun m v => archWeightCharAt (isReal_infinitePlace_rat v) m
    have hmem : φ₁ ∈ V ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ
          (productionPinsOf ℚ (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)
            (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
            (adelicBox ℚ)) Φ.level ⊓
          archCutSubmodule ℚ (ArchTypeFamily.ofChar ℚ χ) := by
      refine ⟨⟨_hφ₁V, fun g u' hu' => _hiso.level_invariant g u' hu'⟩, ?_⟩
      refine (mem_archCutSubmodule_ofChar_iff (F := ℚ) χ φ₁).mpr fun v => ?_
      obtain rfl : v = w₀ := Subsingleton.elim _ _
      exact _hwt v (isReal_infinitePlace_rat v)
    have h := AutomorphicForm.CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar ℚ
      (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) (by norm_num) (by norm_num) hcov R.centralChar V _hV
      isReal_infinitePlace_rat Φ.level Φ.level_ne_bot χ w₀ hw₀ (k₁ w₀) rfl χ'
      (fun m v hv => absurd (Subsingleton.elim v w₀) hv) (fun m => rfl) φ₁ hmem
    have h1 := (Submodule.mem_inf.mp (Submodule.mem_inf.mp (h.1 1)).1).1
    simp only [Function.iterate_one] at h1
    exact h1
  have hTV : Tφ ∈ V :=
    AutomorphicForm.CuspidalConstituent.comp_mul_archRealGLAt_J_mem_of_isCuspConstituent_of_cuspConstituentMeets_of_coversModCentre
      ℚ (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov R.centralChar Φ.level S Φ V _hV
      ⟨φ₁, _hφ₁V, _hne, _hiso⟩ w₀ hw₀ _ hlowV
  have hcontV : ∀ y ∈ V, Continuous y := fun y hy =>
    P2M.WPlusFamilyOdd.continuous_of_mem_of_isCuspSubrep ℚ (productionPinsGeneral ℚ) R.centralChar _hV.1 hy

  have hcombV : ∀ μ : ℂ, φ₁ + μ⁻¹ • Tφ ∈ V := fun μ => V.add_mem _hφ₁V (V.smul_mem _ hTV)

  obtain ⟨a₀, ha₀, hWa₀⟩ := _htorus
  have hint : ∀ y ∈ V, WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ
      y 1 (diagOne a₀) := fun y hy =>
    P2M.WPlusFamilyOdd.whittakerCoefficientIntegrable_productionPinsGeneral_of_continuous y (hcontV y hy) 1 _
  have hsum : whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ
        (φ₁ + (u₁ - u₂)⁻¹ • Tφ) 1 (diagOne a₀)
      + whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ
        (φ₁ + (u₂ - u₁)⁻¹ • Tφ) 1 (diagOne a₀)
      = 2 * whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 (diagOne a₀) := by
    have hfun : (φ₁ + (u₁ - u₂)⁻¹ • Tφ) + (φ₁ + (u₂ - u₁)⁻¹ • Tφ) = (2 : ℂ) • φ₁ := by
      rw [← neg_sub u₁ u₂, inv_neg, neg_smul, two_smul]
      abel
    rw [← P2M.WPlusFamilyOdd.whittakerCoefficient_add ℚ _ _ (hint _ (hcombV _)) (hint _ (hcombV _)), hfun,
      P2M.WPlusFamilyOdd.whittakerCoefficient_smul]

  obtain ⟨μ, hμsign, hWμ⟩ : ∃ μ : ℂ, (μ = u₁ - u₂ ∨ μ = u₂ - u₁) ∧
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ
        (φ₁ + μ⁻¹ • Tφ) 1 (diagOne a₀) ≠ 0 := by
    by_cases hplus : whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ
        (φ₁ + (u₁ - u₂)⁻¹ • Tφ) 1 (diagOne a₀) = 0
    · refine ⟨u₂ - u₁, Or.inr rfl, fun hminus => hWa₀ ?_⟩
      have h := hsum
      rw [hplus, hminus, zero_add] at h
      exact (mul_eq_zero.mp h.symm).resolve_left two_ne_zero
    · exact ⟨u₁ - u₂, Or.inl rfl, hplus⟩
  have hneμ : φ₁ + μ⁻¹ • Tφ ≠ 0 := by
    intro h0
    apply hWμ
    rw [h0]
    exact P2M.WPlusFamilyOdd.whittakerCoefficient_fun_zero ℚ _ _ 1 _

  obtain ⟨archR', hK1, hK2, hK3, hK4, C, hfam⟩ :=
    LanglandsTunnell.exists_whittaker_factorization_add_smul_reflect_lower_of_archCasimir_eigenvector_weightOne_of_ne
      (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov Φ R _hR
      NumberField.StandardAddChar.psiQ NumberField.StandardAddChar.isGlobalAddChar_psiQ
      P2M.WPlusFamilyOdd.psiQ_archLine S archR _hS _htype _hcen φ₁ k₁ _hiso _hne _hconv _hwt _hminp _hmind
      _hpair _hne₂ w₀ hw₀ μ ⟨u₁, u₂, a₁, a₂, hP, hμsign⟩ hneμ

  have hC : C 1 1 ≠ 0 := by
    obtain ⟨φ, Wr, k, hform, -, -, -, -, -, -, hfact, -⟩ := hfam (fun _ => 0)
    intro h0
    apply hWμ
    have h := hfact a₀ 1 (Subgroup.one_mem _)
    rw [hform, mul_one, ha₀, h0, mul_zero] at h
    exact h

  refine ⟨archR', hK1, hK2, hK3, hK4, C, hC, fun par => ?_⟩
  obtain ⟨φ, Wr, k, hform, hiso, hne, hconv, hwt, hkp, hkd, hfact, hpar, hvan, hmel1, hmel2⟩ := hfam par
  have hφV : φ ∈ V := by
    rw [hform]
    exact hcombV μ
  exact ⟨φ, Wr, k, hiso, hne, fun p => _hVloc φ hφV p, hconv, hwt, hkp, hkd, hfact, hpar, hvan, hmel1, hmel2⟩

end S_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne
end P2MW
export P2MW.S_LanglandsTunnell_exists_whittaker_factorization_apply_one_ne_zero_localSpaceAt_of_archCasimir_eigenvector_weightOne_of_ne (solution)
