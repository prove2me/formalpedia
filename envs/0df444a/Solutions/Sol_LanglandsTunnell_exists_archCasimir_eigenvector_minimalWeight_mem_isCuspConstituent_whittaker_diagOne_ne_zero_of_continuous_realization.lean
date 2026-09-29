-- Prove2me | solution 1 for LanglandsTunnell.exists_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_continuous_realization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5fba462d-8524-5fd6-b851-c85f0e16e4f2

import Mathlib
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_WhittakerModelMultiplicityOne
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_exists_archCasimir_eigenvector_minimalWeight_of_continuous_realization
import Theorems.Thm_AutomorphicForm_SiegelCovering_coversModCentre_productionPinsGeneral_D_rat
import Theorems.Thm_LanglandsTunnell_exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq
import Theorems.Thm_LanglandsTunnell_exists_mem_isCuspConstituent_isIsotypicCuspFormAt_whittakerCoefficient_diagOne_ne_zero_J_rigid_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_IsCuspConstituent_exists_irreducible_admissible_isotypicAt
import Theorems.Thm_AutomorphicForm_LocalFunctionSpace_mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_exists_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_continuous_realization
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul"
p2m_attr_erase "instance" "IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul AutomorphicForm.mem_sigmaCentralizer_iff M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec LanglandsTunnell.RankinSelberg.mem_primeFibre AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

noncomputable section

namespace P2M
namespace WPlusSelect

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

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal

theorem solution
    (Φ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (_hR : Continuous R.toFun) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
      (archR : ∀ w : InfinitePlace ℚ, w.IsReal → RealArchParam),
      R.exceptionalSet ⊆ S ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
        archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ → |(u₁ - u₂).re| < 1) ∧
      (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
        IsArchCompAt ℚ (R.centralChar.comp Subgroup.topEquiv.symm.toMonoidHom) w
          ((archR w hw).centralExponent + 1) ((archR w hw).centralSign.val : ℤ)) ∧
      ∃ (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (k : InfinitePlace ℚ → ℤ),
        IsIsotypicCuspFormAt ℚ
            (productionPinsGeneral ℚ)
            R.centralChar Φ.level S Φ φ ∧
        φ ≠ 0 ∧
        (∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          HasArchCharacterAt₀ ℚ w (archWeightCharAt hw (k w)) φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₂ →
            (k w = 0 ∨ k w = 1) ∧ ((k w : ZMod 2) = a₁ + a₂)) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn → k w = (n : ℤ) + 1) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (archR w hw).laplaceEigenvalue • φ) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₁ u₂ : ℂ) (a₁ : ZMod 2),
          archR w hw = RealArchParam.principal u₁ a₁ u₂ a₁ →
            ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, φ (g * archRealGLAt hw UpperHalfPlane.J) = (-1 : ℂ) ^ a₁.val * φ g) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (n : ℕ) (hn : 1 ≤ n),
          archR w hw = RealArchParam.discrete u₀ n hn →
            archDerivAt hw ArchDir.H φ
                - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0) ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (u₀ : ℂ) (a₁ a₂ : ZMod 2),
          archR w hw = RealArchParam.principal u₀ a₁ u₀ a₂ → a₁ ≠ a₂ →
            archDerivAt hw ArchDir.H φ
                - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ) = 0) ∧

        (∃ V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
          CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) R.centralChar V ∧ φ ∈ V ∧
          ∃ ρ ∈ V, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ ρ 1 ≠ 0 ∧
            ∀ p : HeightOneSpectrum (𝓞 ℚ),
              AutomorphicForm.WhittakerModel.HasMultiplicityOneAt ℚ (productionPinsGeneral ℚ)
                NumberField.StandardAddChar.psiQ ρ p (NumberField.StandardAddChar.psiV p)) ∧

        (∃ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, (a : AdeleRing (𝓞 ℚ) ℚ).2 = 1 ∧
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 (diagOne a) ≠ 0) := by
  classical

  have hcov : CoversModCentre ℚ
      (⋃ x ∈ classRepTranslates ℚ, (· * x) '' centreCutSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2) :=
    AutomorphicForm.SiegelCovering.coversModCentre_productionPinsGeneral_D_rat
  obtain ⟨S, archR, hS, htype, hcen, φ, k, hiso, hne, hconv, hwt, hminp, hmind, hpair, hJ, hlow, hlow1⟩ :=
    LanglandsTunnell.exists_archCasimir_eigenvector_minimalWeight_of_continuous_realization
      (1/2 : ℝ) 1 (1/2) 2 (classRepTranslates ℚ) (by norm_num) hcov Φ R _hR

  obtain ⟨V, φa, hV, hφaV, hisoa, hnea, hconva, hwta, hpaira, hJa, hlowa⟩ :=
    LanglandsTunnell.exists_isCuspConstituent_mem_isIsotypicCuspFormAt_of_isIsotypicCuspFormAt_of_rightConv_eq
      R.centralChar Φ.level Φ.level_ne_bot S Φ φ hiso hne hconv (fun w hw => ⟨k w, hwt w hw⟩)

  obtain ⟨S', φb, hSS', hφbV, hisob, hneb, hconvb, hwtb, hpairb, hJb, _hJrigb, hlowb, a₀, ha₀, hWb⟩ :=
    LanglandsTunnell.exists_mem_isCuspConstituent_isIsotypicCuspFormAt_whittakerCoefficient_diagOne_ne_zero_J_rigid_of_hasArchCharacterAt
      R.centralChar Φ.level Φ.level_ne_bot S Φ V hV φa hφaV hisoa hnea
      (fun w hw => ⟨k w, hwta w hw (k w) (hwt w hw)⟩)

  have hWfun : whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φb 1 ≠ 0 := by
    intro h0
    apply hWb
    rw [h0]
    rfl

  refine ⟨S', archR, hS.trans hSS', htype, hcen, φb, k, hisob, hneb, hconvb,
    fun w hw => hwtb w hw (k w) (hwta w hw (k w) (hwt w hw)), hminp, hmind,
    fun w hw => hpairb w hw _ (hpaira w hw _ (hpair w hw)),
    fun w hw u₁ u₂ a₁ h g => hJb w hw _ (hJa w hw _ (hJ w hw u₁ u₂ a₁ h)) g,
    fun w hw u₀ n hn h => hlowb w hw (hlowa w hw (hlow w hw u₀ n hn h)),
    fun w hw u₀ a₁ a₂ h h12 => hlowb w hw (hlowa w hw (hlow1 w hw u₀ a₁ a₂ h h12)),
    ⟨V, hV, hφbV, φb, hφbV, hWfun, fun p => P2M.WPlusSelect.multiplicityOne R.centralChar V hV p φb hφbV⟩,
    a₀, ha₀, hWb⟩

end S_LanglandsTunnell_exists_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_continuous_realization
end P2MW
export P2MW.S_LanglandsTunnell_exists_archCasimir_eigenvector_minimalWeight_mem_isCuspConstituent_whittaker_diagOne_ne_zero_of_continuous_realization (solution)
