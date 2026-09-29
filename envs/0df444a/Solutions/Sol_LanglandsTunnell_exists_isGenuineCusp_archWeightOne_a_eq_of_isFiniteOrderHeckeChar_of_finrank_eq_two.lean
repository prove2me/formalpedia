-- Prove2me | solution 1 for LanglandsTunnell.exists_isGenuineCusp_archWeightOne_a_eq_of_isFiniteOrderHeckeChar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/6d8d66fd-2aa8-5e67-a211-8d4896217de8

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic
import Theorems.Thm_LanglandsTunnell_exists_isNicePinned_twistedDatum_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
import Theorems.Thm_LanglandsTunnell_exists_isAdmissibleTwist_apply_uniformizerIdele_eq_det_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
import Theorems.Thm_LanglandsTunnell_exists_differentiable_hasProd_eulerProduct_induced_twist_of_isFiniteOrderHeckeChar_of_finrank_eq_two
import Theorems.Thm_LanglandsTunnell_Converse_not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist
import Theorems.Thm_LanglandsTunnell_exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_isGenuineCusp_archWeightOne_a_eq_of_isFiniteOrderHeckeChar_of_finrank_eq_two
p2m_attr_erase "instance" "AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "instance" "instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val MeasureTheory.L2.kernelIntegralLM_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr"
p2m_attr_erase "simp" "IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply"
p2m_attr_erase "simp" "RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply"
p2m_attr_erase "simp" "IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain HeckeCharacter

open LanglandsTunnell LanglandsTunnell.Converse
open scoped Pointwise

namespace InducedWeightOneAssemblySol

section Quad

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finiteDimensional (h2 : Module.finrank F E = 2) : FiniteDimensional F E :=
  Module.finite_of_finrank_eq_succ h2

theorem isGalois (h2 : Module.finrank F E = 2) : IsGalois F E := by
  haveI := finiteDimensional h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  infer_instance

theorem card_gal (h2 : Module.finrank F E = 2) :
    haveI := finiteDimensional h2
    Fintype.card (E ≃ₐ[F] E) = 2 := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]

theorem exists_ne_one (h2 : Module.finrank F E = 2) : ∃ τ : E ≃ₐ[F] E, τ ≠ 1 := by
  haveI := finiteDimensional h2
  have h : 1 < Fintype.card (E ≃ₐ[F] E) := by rw [card_gal h2]; norm_num
  haveI := Fintype.one_lt_card_iff_nontrivial.mp h
  exact exists_ne 1

theorem eq_one_or_eq (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1)
    (σ : E ≃ₐ[F] E) : σ = 1 ∨ σ = τ := by
  classical
  haveI := finiteDimensional h2
  have hcard : (Finset.univ : Finset (E ≃ₐ[F] E)).card = 2 := by
    rw [Finset.card_univ, card_gal h2]
  obtain ⟨x, y, -, hxy⟩ := Finset.card_eq_two.mp hcard
  have hmem : ∀ g : E ≃ₐ[F] E, g = x ∨ g = y := fun g => by
    have := Finset.mem_univ g
    rw [hxy, Finset.mem_insert, Finset.mem_singleton] at this
    exact this
  rcases hmem 1 with h1 | h1 <;> rcases hmem τ with hτ' | hτ' <;> rcases hmem σ with hσ | hσ
  all_goals first
    | exact absurd (hτ'.trans h1.symm) hτ
    | exact Or.inl (hσ.trans h1.symm)
    | exact Or.inr (hσ.trans hτ'.symm)

end Quad

section Action

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in
theorem algebraMap_smul (τ : E ≃ₐ[F] E) (x : 𝓞 E) :
    algebraMap (𝓞 E) E (τ • x) = τ (algebraMap (𝓞 E) E x) := rfl

omit [NumberField F] in
theorem smul_algebraMap (τ : E ≃ₐ[F] E) (a : 𝓞 F) :
    τ • (algebraMap (𝓞 F) (𝓞 E) a) = algebraMap (𝓞 F) (𝓞 E) a := by
  apply IsFractionRing.injective (𝓞 E) E
  rw [algebraMap_smul]
  change τ (algebraMap F E (algebraMap (𝓞 F) F a)) = algebraMap F E (algebraMap (𝓞 F) F a)
  exact τ.commutes _

omit [NumberField F] in
theorem smulCommClass : SMulCommClass (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) :=
  ⟨fun τ a x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', smul_algebraMap]⟩

attribute [local instance] smulCommClass

omit [NumberField F] [NumberField E] in
theorem smul_ideal_ne_bot (τ : E ≃ₐ[F] E) {I : Ideal (𝓞 E)} (hI : I ≠ ⊥) : τ • I ≠ ⊥ := by
  intro h
  apply hI
  have := congrArg (fun J : Ideal (𝓞 E) => τ⁻¹ • J) h
  simp only [inv_smul_smul] at this
  rw [this, ← Submodule.zero_eq_bot, smul_zero]

def smulHOS (τ : E ≃ₐ[F] E) (𝔓 : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  ⟨τ • 𝔓.asIdeal, inferInstance, smul_ideal_ne_bot τ 𝔓.ne_bot⟩

omit [NumberField F] [NumberField E] in
@[scoped simp] theorem smulHOS_asIdeal (τ : E ≃ₐ[F] E) (𝔓 : HeightOneSpectrum (𝓞 E)) :
    (smulHOS τ 𝔓).asIdeal = τ • 𝔓.asIdeal := rfl

omit [NumberField F] in
theorem under_smulHOS (τ : E ≃ₐ[F] E) (𝔓 : HeightOneSpectrum (𝓞 E)) :
    (smulHOS τ 𝔓).under (𝓞 F) = 𝔓.under (𝓞 F) := by
  apply HeightOneSpectrum.ext
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, smulHOS_asIdeal,
    Ideal.under_smul]

omit [NumberField F] [NumberField E] in
theorem smulHOS_eq_iff {τ : E ≃ₐ[F] E} (𝔓 : HeightOneSpectrum (𝓞 E)) :
    smulHOS τ 𝔓 = 𝔓 ↔ τ • 𝔓.asIdeal = 𝔓.asIdeal :=
  ⟨fun h => by rw [← smulHOS_asIdeal, h], fun h => HeightOneSpectrum.ext h⟩

end Action

section Ramification

variable (K : Type*) [Field K] [NumberField K]

theorem exists_prime_mem (𝔓 : HeightOneSpectrum (𝓞 K)) : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ 𝔓.asIdeal := by
  haveI := 𝔓.isPrime
  obtain ⟨p, hp⟩ := (IsPrincipalIdealRing.principal (𝔓.asIdeal.under ℤ)).principal
  have hp' : 𝔓.asIdeal.under ℤ = Ideal.span {p} := hp
  have hne : 𝔓.asIdeal.under ℤ ≠ ⊥ := by
    intro h
    have hn : ((Ideal.absNorm 𝔓.asIdeal : ℤ) : 𝓞 K) ∈ 𝔓.asIdeal := by
      rw [Int.cast_natCast]; exact Ideal.absNorm_mem _
    have : (Ideal.absNorm 𝔓.asIdeal : ℤ) ∈ 𝔓.asIdeal.under ℤ := by
      rw [Ideal.under_def, Ideal.mem_comap, eq_intCast]; exact hn
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at this
    exact 𝔓.ne_bot this
  have hp0 : p ≠ 0 := by
    intro h0; apply hne; rw [hp', h0]; simp
  have hprime : Prime p := by
    rw [← Ideal.span_singleton_prime hp0, ← hp']
    exact Ideal.IsPrime.under ℤ 𝔓.asIdeal
  refine ⟨p.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_⟩
  have hmem : (p : 𝓞 K) ∈ 𝔓.asIdeal := by
    have : p ∈ 𝔓.asIdeal.under ℤ := by rw [hp']; exact Ideal.mem_span_singleton_self p
    rw [Ideal.under_def, Ideal.mem_comap, eq_intCast] at this
    exact this
  rcases Int.natAbs_eq p with h | h
  · rw [← Int.cast_natCast, ← h]; exact hmem
  · rw [← Int.cast_natCast, show ((p.natAbs : ℕ) : ℤ) = -p by omega, Int.cast_neg]
    exact 𝔓.asIdeal.neg_mem hmem

noncomputable def badPrimes : Finset ℕ := (NumberField.discr K).natAbs.primeFactors

theorem isUnramifiedAt_of_not_mem_badPrimes {p : ℕ} (hp : p.Prime) (hpB : p ∉ badPrimes K)
    (P : Ideal (𝓞 K)) [P.IsPrime] (hpP : (p : 𝓞 K) ∈ P) : Algebra.IsUnramifiedAt ℤ P := by
  have hnd : ¬ ((p : ℤ) ∣ NumberField.discr K) := by
    intro h
    apply hpB
    rw [badPrimes, Nat.mem_primeFactors]
    exact ⟨hp, Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr h),
      Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)⟩
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  exact (NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) hpr).mp hnd P inferInstance
    (by exact_mod_cast hpP)

theorem finite_setOf_exists_mem (B : Finset ℕ) :
    {v : HeightOneSpectrum (𝓞 K) | ∃ p ∈ B, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hsub : {v : HeightOneSpectrum (𝓞 K) | ∃ p ∈ B, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal} ⊆
      ⋃ p ∈ (B.filter Nat.Prime), {v : HeightOneSpectrum (𝓞 K) |
        v.asIdeal ∣ Ideal.span {(p : 𝓞 K)}} := by
    rintro v ⟨p, hpB, hp, hpv⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter, exists_prop]
    refine ⟨p, ⟨hpB, hp⟩, ?_⟩
    rw [Ideal.dvd_span_singleton]
    exact hpv
  refine Set.Finite.subset ?_ hsub
  refine Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => ?_
  have hp' : (p : ℕ).Prime := (Finset.mem_filter.mp hp).2
  apply Ideal.finite_factors
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp'.ne_zero

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

noncomputable def ramSet : Finset (HeightOneSpectrum (𝓞 F)) :=
  (finite_setOf_exists_mem F (badPrimes E)).toFinset

variable {F E}

omit [NumberField F] [NumberField E] in
theorem mem_under_iff {v : HeightOneSpectrum (𝓞 F)} {𝔓 : HeightOneSpectrum (𝓞 E)}
    (h : 𝔓.under (𝓞 F) = v) (x : 𝓞 F) :
    x ∈ v.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) x ∈ 𝔓.asIdeal := by
  rw [← h, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]

theorem ramificationIdx_eq_one {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ ramSet F E)
    {𝔓 : HeightOneSpectrum (𝓞 E)} (h : 𝔓.under (𝓞 F) = v) :
    v.asIdeal.ramificationIdx' 𝔓.asIdeal = 1 := by
  obtain ⟨p, hp, hp𝔓⟩ := exists_prime_mem E 𝔓
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by
    rw [mem_under_iff h, map_natCast]; exact hp𝔓
  have hpB : p ∉ badPrimes E := by
    intro hB
    apply hv
    rw [ramSet, Set.Finite.mem_toFinset]
    exact ⟨p, hB, hp, hpv⟩
  haveI := 𝔓.isPrime
  haveI : Algebra.IsUnramifiedAt ℤ 𝔓.asIdeal := isUnramifiedAt_of_not_mem_badPrimes E hp hpB _ hp𝔓
  haveI : Algebra.IsUnramifiedAt (𝓞 F) 𝔓.asIdeal := Algebra.IsUnramifiedAt.of_restrictScalars ℤ _
  have h1 := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 F) (p := 𝔓.asIdeal)
  haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h, HeightOneSpectrum.under_asIdeal]⟩
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal 𝔓.asIdeal v.ne_bot]
  exact h1

attribute [local instance] Ideal.Quotient.field in

theorem card_stabilizer_eq_inertiaDeg (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ ramSet F E) {𝔓 : HeightOneSpectrum (𝓞 E)} (h : 𝔓.under (𝓞 F) = v) :
    haveI := finiteDimensional h2
    Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) 𝔓.asIdeal) = v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  haveI : IsGaloisGroup (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) :=
    IsGaloisGroup.of_isFractionRing (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) F E
  haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h, HeightOneSpectrum.under_asIdeal]⟩
  haveI := 𝔓.isPrime.isMaximal 𝔓.ne_bot
  haveI := v.isPrime.isMaximal v.ne_bot
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  rw [Ideal.card_stabilizer_eq (G := E ≃ₐ[F] E) v.asIdeal 𝔓.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal 𝔓.asIdeal (E ≃ₐ[F] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal 𝔓.asIdeal v.ne_bot,
    ramificationIdx_eq_one hv h, one_mul,
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal 𝔓.asIdeal (E ≃ₐ[F] E),
    ← Ideal.inertiaDeg'_eq_inertiaDeg (p := v.asIdeal) (q := 𝔓.asIdeal)]

theorem dichotomy (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ ramSet F E) {𝔓 : HeightOneSpectrum (𝓞 E)}
    (h : 𝔓.under (𝓞 F) = v) :
    (smulHOS τ 𝔓 ≠ 𝔓 ∧ v.asIdeal.inertiaDeg' 𝔓.asIdeal = 1) ∨
      (smulHOS τ 𝔓 = 𝔓 ∧ v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2) := by
  haveI := finiteDimensional h2
  have hcard := card_stabilizer_eq_inertiaDeg h2 hv h
  by_cases hfix : τ • 𝔓.asIdeal = 𝔓.asIdeal
  · right
    refine ⟨(smulHOS_eq_iff 𝔓).mpr hfix, ?_⟩
    have htop : MulAction.stabilizer (E ≃ₐ[F] E) 𝔓.asIdeal = ⊤ := by
      rw [eq_top_iff]
      intro σ _
      rcases eq_one_or_eq h2 hτ σ with hσ | hσ
      · rw [hσ]; exact Subgroup.one_mem _
      · rw [hσ, MulAction.mem_stabilizer_iff]; exact hfix
    rw [htop, Subgroup.card_top, Nat.card_eq_fintype_card, card_gal h2] at hcard
    exact hcard.symm
  · left
    refine ⟨fun h' => hfix ((smulHOS_eq_iff 𝔓).mp h'), ?_⟩
    have hbot : MulAction.stabilizer (E ≃ₐ[F] E) 𝔓.asIdeal = ⊥ := by
      rw [eq_bot_iff]
      intro σ hσ
      rw [MulAction.mem_stabilizer_iff] at hσ
      rcases eq_one_or_eq h2 hτ σ with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1] at hσ; exact absurd hσ hfix
    rw [hbot, Subgroup.card_bot] at hcard
    exact hcard.symm

omit [NumberField E] in

theorem exists_under_eq (v : HeightOneSpectrum (𝓞 F)) : ∃ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 F) = v := by
  haveI := v.isPrime.isMaximal v.ne_bot
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hQne : Q ≠ ⊥ := by
    intro hQ0
    apply v.ne_bot
    rw [hQ.over, hQ0, Ideal.under_def, Ideal.comap_bot_of_injective]
    exact RingOfIntegers.algebraMap.injective F E
  refine ⟨⟨Q, hQmax.isPrime, hQne⟩, HeightOneSpectrum.ext ?_⟩
  rw [HeightOneSpectrum.under_asIdeal]
  exact hQ.over.symm

theorem exists_split_or_inert (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ ramSet F E) :
    ∃ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 F) = v ∧
      ((smulHOS τ 𝔓 ≠ 𝔓 ∧ (smulHOS τ 𝔓).under (𝓞 F) = v) ∨ v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2) := by
  obtain ⟨𝔓, h𝔓⟩ := exists_under_eq (E := E) v
  refine ⟨𝔓, h𝔓, ?_⟩
  rcases dichotomy h2 hτ hv h𝔓 with ⟨hne, -⟩ | ⟨-, hf⟩
  · exact Or.inl ⟨hne, (under_smulHOS τ 𝔓).trans h𝔓⟩
  · exact Or.inr hf

end Ramification

section Generic

theorem norm_apply_eq_one {G : Type*} [Group G] {χ : G →* ℂˣ} (hχ : IsOfFinOrder χ) (x : G) :
    ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, hn, hχn⟩ := hχ.exists_pow_eq_one
  have h1 : ((χ x : ℂˣ) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχn, MonoidHom.one_apply, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h1 hn.ne'

theorem norm_ratio_gt_four (q : ℕ) (hq : 2 ≤ q) :
    4 < ‖((q : ℂ) + 2 + (q : ℂ)⁻¹)‖ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hq : 0 < q)
  have hcast : ((q : ℂ) + 2 + (q : ℂ)⁻¹) = (((q : ℝ) + 2 + (q : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast; ring
  have hpos : (0 : ℝ) < (q : ℝ)⁻¹ := inv_pos.mpr hq0
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  linarith

theorem sq_add_ne (x y : ℂ) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (q : ℕ) (hq : 2 ≤ q) :
    (x + y) ^ 2 ≠ x * y * (((q : ℂ) + 2 + (q : ℂ)⁻¹)) := by
  intro h
  have hl : ‖(x + y) ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    have : ‖x + y‖ ≤ 2 := (norm_add_le x y).trans (by rw [hx, hy]; norm_num)
    nlinarith [norm_nonneg (x + y)]
  have hr : 4 < ‖x * y * (((q : ℂ) + 2 + (q : ℂ)⁻¹))‖ := by
    rw [norm_mul, norm_mul, hx, hy, one_mul, one_mul]
    exact norm_ratio_gt_four q hq
  rw [h] at hl
  exact absurd hl (not_le.mpr hr)

theorem zero_sq_ne (x : ℂ) (hx : ‖x‖ = 1) (q : ℕ) (hq : 2 ≤ q) :
    (0 : ℂ) ^ 2 ≠ -x * (((q : ℂ) + 2 + (q : ℂ)⁻¹)) := by
  intro h
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hx; exact zero_ne_one hx
  have hr0 : ((q : ℂ) + 2 + (q : ℂ)⁻¹) ≠ 0 := by
    intro h0
    have := norm_ratio_gt_four q hq
    rw [h0, norm_zero] at this
    linarith
  rw [zero_pow two_ne_zero, eq_comm, mul_eq_zero, neg_eq_zero] at h
  rcases h with h | h
  · exact hx0 h
  · exact hr0 h

theorem two_le_absNorm {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h =>
    v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

end Generic

section Arch

theorem oddArtin_centralExponent : RealArchParam.oddArtin.centralExponent = 0 := by
  simp [RealArchParam.oddArtin, RealArchParam.centralExponent]

theorem oddArtin_centralSign_val : ((RealArchParam.oddArtin.centralSign).val : ℤ) = 1 := by
  simp only [RealArchParam.oddArtin, RealArchParam.centralSign, zero_add]
  decide

theorem trivialArtin_centralExponent : ComplexArchParam.trivialArtin.centralExponent = 0 := by
  simp [ComplexArchParam.trivialArtin, ComplexArchParam.centralExponent]

theorem trivialArtin_centralTwist : ComplexArchParam.trivialArtin.centralTwist = 0 := by
  simp [ComplexArchParam.trivialArtin, ComplexArchParam.centralTwist]

theorem oddArtin_generic (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2)
    (h : RealArchParam.oddArtin = RealArchParam.principal u₁ a₁ u₂ a₂) (p : ℤ) (hp : p ≠ 0)
    (hu : u₁ - u₂ = (p : ℂ)) : a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2) := by
  exfalso
  simp only [RealArchParam.oddArtin, RealArchParam.principal.injEq] at h
  obtain ⟨h1, -, h3, -⟩ := h
  rw [← h1, ← h3, sub_zero, eq_comm, Int.cast_eq_zero] at hu
  exact hp hu

theorem trivialArtin_generic (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    ¬ ((2 * (ComplexArchParam.trivialArtin.u₁ - ComplexArchParam.trivialArtin.u₂) = ((p + q : ℕ) : ℂ) ∧
          ComplexArchParam.trivialArtin.k₁ - ComplexArchParam.trivialArtin.k₂ = (p : ℤ) - q) ∨
        (2 * (ComplexArchParam.trivialArtin.u₁ - ComplexArchParam.trivialArtin.u₂) = -((p + q : ℕ) : ℂ) ∧
          ComplexArchParam.trivialArtin.k₁ - ComplexArchParam.trivialArtin.k₂ = (q : ℤ) - p)) := by
  have hpq : ((p + q : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show p + q ≠ 0 by omega)
  simp only [ComplexArchParam.trivialArtin, sub_self, mul_zero]
  rintro (⟨h, -⟩ | ⟨h, -⟩)
  · exact hpq h.symm
  · exact hpq (neg_eq_zero.mp h.symm)

end Arch

end InducedWeightOneAssemblySol
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_isGenuineCusp_archWeightOne_a_eq_of_isFiniteOrderHeckeChar_of_finrank_eq_two.InducedWeightOneAssemblySol"

open InducedWeightOneAssemblySol in
theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (ξ : (AdeleRing (𝓞 M) M)ˣ →* ℂˣ) (hξ : IsFiniteOrderHeckeChar M ξ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 M))) (hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w')
    (hsign : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1)
    (hcusp : ∃ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' ∧ w'.under (𝓞 E) = w''.under (𝓞 E) ∧
      w' ∉ S₀ ∧ w'' ∉ S₀ ∧ ξ (uniformizerIdele M w') ≠ ξ (uniformizerIdele M w''))
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 E) E)) (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ Ψ : HeckeEigensystem E ℂ,
      (∃ R : SmoothCuspRealizationAt E
          (productionPinsOf E (⋃ x ∈ T, (· * x) '' centreCutSiegelSet E c u d₁ d₂)
            (fun N => levelOne (𝓞 E) E N ⊓ finiteAdelicGL2Subgroup E) (fun v => heckeGen (𝓞 E) E v)
            (adelicBox E))
          Ψ.toRawCentral,
        IsGenuineCuspRealizationAt E
          (productionPinsOf E (⋃ x ∈ T, (· * x) '' centreCutSiegelSet E c u d₁ d₂)
            (fun N => levelOne (𝓞 E) E N ⊓ finiteAdelicGL2Subgroup E) (fun v => heckeGen (𝓞 E) E v)
            (adelicBox E))
          Ψ.toRawCentral R ∧
        (∀ w : InfinitePlace E, ∀ hw : w.IsReal, HasArchCharacterAt₀ E w (archWeightOneAt hw) R.toFun) ∧
        (∀ w : InfinitePlace E, ∀ hw : w.IsReal, IsArchHolomorphicAt w hw R.toFun)) ∧
      ∃ S : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∉ S →
        (∀ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' → w'.under (𝓞 E) = w → w''.under (𝓞 E) = w →
          Ψ.a w = (ξ (uniformizerIdele M w') : ℂ) + ξ (uniformizerIdele M w'') ∧
          Ψ.b w = (ξ (uniformizerIdele M w') : ℂ) * ξ (uniformizerIdele M w'')) ∧
        (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
          Ψ.a w = 0 ∧ Ψ.b w = -(ξ (uniformizerIdele M w') : ℂ)) := by
  classical

  obtain ⟨ω, hω, hωR, hωC, S_D, hD⟩ :=
    LanglandsTunnell.exists_isAdmissibleTwist_apply_uniformizerIdele_eq_det_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
      E M h2 ξ hξ hsign

  obtain ⟨Pi, S, A, Ad, hT, htab, hbd, hsupp, hA0, hnice⟩ :=
    LanglandsTunnell.exists_isNicePinned_twistedDatum_induced_of_isFiniteOrderHeckeChar_of_finrank_eq_two
      E M h2 ξ hξ S₀ hunr hsign hcusp (S_D ∪ ramSet E M)
  have hSD : ∀ v, v ∉ S → v ∉ S_D := fun v hv h => hv (hT (Finset.mem_union_left _ h))
  have hSR : ∀ v, v ∉ S → v ∉ ramSet E M := fun v hv h => hv (hT (Finset.mem_union_right _ h))

  obtain ⟨τ, hτ⟩ := exists_ne_one (F := E) (E := M) h2

  have hn1 : ∀ x, ‖((ξ x : ℂˣ) : ℂ)‖ = 1 := fun x => norm_apply_eq_one hξ.isOfFinOrder x

  have key : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ S →
      ∃ x y : ℂ, ‖x‖ = 1 ∧ (y = 0 ∨ ‖y‖ = 1) ∧
        ((Pi.a v = x + y ∧ Pi.b v = x * y ∧ ‖y‖ = 1) ∨ (Pi.a v = 0 ∧ Pi.b v = -x)) ∧
        ((ω (uniformizerIdele E v) : ℂˣ) : ℂ) = Pi.b v := by
    intro v hv
    obtain ⟨𝔓, h𝔓, hcase⟩ := exists_split_or_inert (F := E) (E := M) h2 hτ (hSR v hv)
    obtain ⟨htS, htI⟩ := htab v hv
    obtain ⟨-, hDS, hDI⟩ := hD v (hSD v hv)
    rcases hcase with ⟨hne, hτ𝔓⟩ | hf
    · obtain ⟨ha, hb⟩ := htS 𝔓 (smulHOS τ 𝔓) (Ne.symm hne) h𝔓 hτ𝔓
      have hωv := hDS 𝔓 (smulHOS τ 𝔓) (Ne.symm hne) h𝔓 hτ𝔓
      exact ⟨_, _, hn1 _, Or.inr (hn1 _), Or.inl ⟨ha, hb, hn1 _⟩, hωv.trans hb.symm⟩
    · obtain ⟨ha, hb⟩ := htI 𝔓 h𝔓 hf
      have hωv := hDI 𝔓 h𝔓 hf
      exact ⟨_, 0, hn1 (uniformizerIdele M 𝔓), Or.inl rfl, Or.inr ⟨ha, hb⟩, hωv.trans hb.symm⟩

  obtain ⟨Φ', hR, S', hagr⟩ :=
    LanglandsTunnell.Converse.exists_isArithGenuineCuspRealizable_archWeightOne_isArchHolomorphicAt_of_forall_isNicePinned_of_centralChar_of_generic
      E c u d₁ d₂ T hc hd₁ Pi S
      (fun _ _ => RealArchParam.oddArtin) (fun _ _ => ComplexArchParam.trivialArtin)
      (fun _ => 1)
      (fun v _ => (continuous_const : Continuous fun _ : (v.adicCompletion E)ˣ => (1 : ℂˣ)))
      A Ad
      (fun N v hv => LanglandsTunnell.exists_heckeCosetSystem_productionPinsGeneral_of_not_dvd E N v hv)
      hbd hsupp hA0
      (fun μ hμ hunit => hnice μ hμ (fun v hv t ht => by simpa using hunit v hv t ht))
      (fun μ₁ μ₂ h₁ h₂' hc₁ hc₂ =>
        LanglandsTunnell.Converse.not_agreesAwayFromFinite_eisensteinTableOf_of_hasProd_eulerProduct_unitary_twist
          E Pi
          (fun χ hχ hcχ huχ =>
            LanglandsTunnell.exists_differentiable_hasProd_eulerProduct_induced_twist_of_isFiniteOrderHeckeChar_of_finrank_eq_two
              E M h2 ξ hξ S₀ hunr hcusp Pi S htab χ hχ hcχ huχ)
          Pi.level Pi.level_ne_bot μ₁ μ₂ h₁ h₂' hc₁ hc₂)
      ω hω
      (fun v hv => (hD v (hSD v hv)).1)
      (fun v hv => by
        obtain ⟨_, _, -, -, -, h⟩ := key v hv
        exact h)
      (fun v hv => by
        obtain ⟨x, y, hx, -, hval, -⟩ := key v hv
        rcases hval with ⟨ha, hb, hy⟩ | ⟨ha, hb⟩
        · rw [ha, hb]; exact sq_add_ne x y hx hy _ (two_le_absNorm v)
        · rw [ha, hb]; exact zero_sq_ne x hx _ (two_le_absNorm v))
      (fun _ _ u₁ u₂ a₁ a₂ h p hp hu => oddArtin_generic u₁ u₂ a₁ a₂ h p hp hu)
      (fun _ _ p q hp hq => trivialArtin_generic p q hp hq)
      (fun w hw => by
        first
          | rw [show ((fun (_ : InfinitePlace E) (_ : _root_.NumberField.InfinitePlace.IsReal _) =>
              RealArchParam.oddArtin) w hw) = RealArchParam.oddArtin from rfl,
              oddArtin_centralExponent, oddArtin_centralSign_val]
          | rw [oddArtin_centralExponent, oddArtin_centralSign_val]
          | (simp only []; rw [oddArtin_centralExponent, oddArtin_centralSign_val])
        exact hωR w hw)
      (fun w hw => by
        first
          | rw [show ((fun (_ : InfinitePlace E) (_ : _root_.NumberField.InfinitePlace.IsComplex _) =>
              ComplexArchParam.trivialArtin) w hw) = ComplexArchParam.trivialArtin from rfl,
              trivialArtin_centralExponent, trivialArtin_centralTwist]
          | rw [trivialArtin_centralExponent, trivialArtin_centralTwist]
          | (simp only []; rw [trivialArtin_centralExponent, trivialArtin_centralTwist])
        exact hωC w hw)
      (fun _ _ => ⟨0, 1, by decide, rfl⟩)

  refine ⟨Φ', hR, S ∪ S', fun w hw => ?_⟩
  have hwS : w ∉ S := fun h => hw (Finset.mem_union_left _ h)
  have hwS' : w ∉ S' := fun h => hw (Finset.mem_union_right _ h)
  obtain ⟨ha', hb'⟩ := hagr w hwS'
  obtain ⟨htS, htI⟩ := htab w hwS
  refine ⟨fun w' w'' hne h' h'' => ?_, fun w' h' hf => ?_⟩
  · obtain ⟨ha, hb⟩ := htS w' w'' hne h' h''
    exact ⟨ha'.symm.trans ha, hb'.symm.trans hb⟩
  · obtain ⟨ha, hb⟩ := htI w' h' hf
    exact ⟨ha'.symm.trans ha, hb'.symm.trans hb⟩

end S_LanglandsTunnell_exists_isGenuineCusp_archWeightOne_a_eq_of_isFiniteOrderHeckeChar_of_finrank_eq_two
end P2MW
export P2MW.S_LanglandsTunnell_exists_isGenuineCusp_archWeightOne_a_eq_of_isFiniteOrderHeckeChar_of_finrank_eq_two (solution)
