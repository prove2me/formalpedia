-- Prove2me | solution 1 for LanglandsTunnell.exists_agreesAwayFromFinite_isGenuineCusp_of_raySymbol_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/f0c7c88d-f229-53db-9475-0bac498cfcb1

import Mathlib
import Definitions.Def_AutomorphicForm_ViaGeneralCuspNotion
import Definitions.Def_NarrowRayClassGroup
import Theorems.Thm_NumberField_exists_ne_zero_and_sub_one_mem_and_lt_zero_iff
import Theorems.Thm_NumberField_exists_sq_eq_one_and_raySymbol_span_singleton_eq_prod_of_forall_pos
import Theorems.Thm_LanglandsTunnell_exists_isGenuineCusp_archWeightOne_a_eq_of_raySymbol_eq_prod_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_agreesAwayFromFinite_isGenuineCusp_of_raySymbol_eq_one
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom RestrictedProduct.SecondCountableTopology_of_principal"
p2m_attr_erase "instance" "instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "AutomorphicForm.rightTranslationEmbed_smul_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val MeasureTheory.L2.kernelIntegralLM_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply"
p2m_attr_erase "simp" "AutomorphicForm.IsStableLinearOn.coe_toEnd_apply AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Equiv_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero"

open NumberField IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel Deep.NTSupply
open NumberField.AdelicLevel NumberField.AdelicBox EisensteinWeightOne
open scoped nonZeroDivisors Pointwise

namespace GenuineCuspAISol

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

theorem mul_self_eq_one (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1) : τ * τ = 1 := by
  rcases eq_one_or_eq h2 hτ (τ * τ) with h | h
  · exact h
  · exact absurd (mul_left_cancel (h.trans (mul_one τ).symm)) hτ

theorem inv_eq_self (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1) : τ⁻¹ = τ :=
  inv_eq_of_mul_eq_one_right (mul_self_eq_one h2 hτ)

theorem realEmb_eq_comp (h2 : Module.finrank F E = 2) {τ : E ≃ₐ[F] E} (hτ : τ ≠ 1)
    {φ φ' : E →+* ℝ} (hne : φ ≠ φ') (hF : φ.comp (algebraMap F E) = φ'.comp (algebraMap F E))
    (x : E) : φ' x = φ (τ x) := by
  haveI := finiteDimensional h2
  haveI := isGalois h2
  letI : Algebra F ℝ := (φ.comp (algebraMap F E)).toAlgebra
  letI : Algebra E ℝ := φ.toAlgebra
  haveI : IsScalarTower F E ℝ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let φ'ₐ : E →ₐ[F] ℝ :=
    { φ' with
      commutes' := fun a => by
        change φ' (algebraMap F E a) = φ (algebraMap F E a)
        exact (RingHom.congr_fun hF a).symm }
  set σ : E ≃ₐ[F] E := AlgHom.restrictNormal' φ'ₐ E with hσ
  have hσx : ∀ y : E, φ (σ y) = φ' y := fun y => by
    have := AlgHom.restrictNormal_commutes φ'ₐ E y
    rw [Algebra.algebraMap_self, RingHom.id_apply] at this
    change algebraMap E ℝ (AlgHom.restrictNormal φ'ₐ E y) = φ' y at this
    rw [hσ, AlgHom.restrictNormal', AlgEquiv.ofBijective_apply]
    exact this
  rcases eq_one_or_eq h2 hτ σ with h | h
  · exfalso
    apply hne
    ext y
    rw [← hσx y, h, AlgEquiv.one_apply]
  · rw [← hσx x, h]

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
theorem smul_natCast (τ : E ≃ₐ[F] E) (n : ℕ) : τ • (n : 𝓞 E) = n :=
  map_natCast (MulSemiringAction.toRingHom _ _ τ) n

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
theorem smulHOS_smulHOS {τ : E ≃ₐ[F] E} (h : τ * τ = 1) (𝔓 : HeightOneSpectrum (𝓞 E)) :
    smulHOS τ (smulHOS τ 𝔓) = 𝔓 := by
  apply HeightOneSpectrum.ext
  rw [smulHOS_asIdeal, smulHOS_asIdeal, smul_smul, h, one_smul]

omit [NumberField F] [NumberField E] in
theorem smulHOS_eq_iff {τ : E ≃ₐ[F] E} (𝔓 : HeightOneSpectrum (𝓞 E)) :
    smulHOS τ 𝔓 = 𝔓 ↔ τ • 𝔓.asIdeal = 𝔓.asIdeal :=
  ⟨fun h => by rw [← smulHOS_asIdeal, h], fun h => HeightOneSpectrum.ext h⟩

omit [NumberField F] [NumberField E] in
theorem smul_span_singleton (τ : E ≃ₐ[F] E) (x : 𝓞 E) :
    τ • (Ideal.span {x} : Ideal (𝓞 E)) = Ideal.span {τ • x} := by
  rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
  rfl

end Action

section Ray

variable {K : Type*} [Field K] [NumberField K] {M : Type*} [CommGroup M]

theorem raySymbol_coe_prime (f : HeightOneSpectrum (𝓞 K) → M) (v : HeightOneSpectrum (𝓞 K)) :
    raySymbol K f (v.asIdeal : FractionalIdeal ((𝓞 K)⁰) K) = f v := by
  rw [← primeUnit_val]
  exact raySymbol_primeUnit K f v

theorem raySymbol_coe_top (f : HeightOneSpectrum (𝓞 K) → M) :
    raySymbol K f ((⊤ : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) = 1 := by
  rw [FractionalIdeal.coeIdeal_top]
  unfold raySymbol
  simp [FractionalIdeal.count_one]

theorem raySymbol_coe_mul (f : HeightOneSpectrum (𝓞 K) → M) {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥)
    (hJ : J ≠ ⊥) :
    raySymbol K f ((I * J : Ideal (𝓞 K)) : FractionalIdeal ((𝓞 K)⁰) K) =
      raySymbol K f (I : FractionalIdeal ((𝓞 K)⁰) K) * raySymbol K f (J : FractionalIdeal ((𝓞 K)⁰) K) := by
  rw [FractionalIdeal.coeIdeal_mul]
  exact raySymbol_mul K f (FractionalIdeal.coeIdeal_ne_zero.mpr hI) (FractionalIdeal.coeIdeal_ne_zero.mpr hJ)

theorem raySymbol_fun_mul (f g : HeightOneSpectrum (𝓞 K) → M) (I : FractionalIdeal ((𝓞 K)⁰) K) :
    raySymbol K (f * g) I = raySymbol K f I * raySymbol K g I := by
  unfold raySymbol
  rw [← finprod_mul_distrib (hasFiniteMulSupport_raySymbol_factors K f I)
    (hasFiniteMulSupport_raySymbol_factors K g I)]
  exact finprod_congr fun v => by rw [Pi.mul_apply, mul_zpow]

end Ray

section RayTransport

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {M : Type*} [CommGroup M]

omit [NumberField F] in

theorem raySymbol_smul (f : HeightOneSpectrum (𝓞 E) → M) (τ : E ≃ₐ[F] E) (J : Ideal (𝓞 E)) :
    J ≠ ⊥ → raySymbol E f ((τ • J : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) =
      raySymbol E (f ∘ smulHOS τ) (J : FractionalIdeal ((𝓞 E)⁰) E) := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd (Submodule.zero_eq_bot) h
  | h₂ J hJ =>
    intro _
    rw [Ideal.isUnit_iff.mp hJ]
    have : τ • (⊤ : Ideal (𝓞 E)) = ⊤ := by rw [Ideal.pointwise_smul_def, Ideal.map_top]
    rw [this, raySymbol_coe_top, raySymbol_coe_top]
  | h₃ J p hJ hp ih =>
    intro _
    have hp0 : p ≠ ⊥ := hp.ne_zero
    have hpP : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hp
    have hJ' : J ≠ ⊥ := hJ
    rw [smul_mul', raySymbol_coe_mul f (smul_ideal_ne_bot τ hp0) (smul_ideal_ne_bot τ hJ'),
      raySymbol_coe_mul _ hp0 hJ', ih hJ']
    congr 1
    have h1 := raySymbol_coe_prime f (smulHOS τ ⟨p, hpP, hp0⟩)
    have h2 := raySymbol_coe_prime (f ∘ smulHOS τ) ⟨p, hpP, hp0⟩
    rw [smulHOS_asIdeal] at h1
    rw [h1, h2]
    rfl

end RayTransport

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
    Ideal.inertiaDeg'_eq_inertiaDeg v.asIdeal 𝔓.asIdeal]

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

theorem absNorm_eq_pow {v : HeightOneSpectrum (𝓞 F)} {𝔓 : HeightOneSpectrum (𝓞 E)}
    (h : 𝔓.under (𝓞 F) = v) :
    Ideal.absNorm 𝔓.asIdeal = Ideal.absNorm v.asIdeal ^ v.asIdeal.inertiaDeg' 𝔓.asIdeal := by
  haveI : 𝔓.asIdeal.LiesOver v.asIdeal := ⟨by rw [← h, HeightOneSpectrum.under_asIdeal]⟩
  exact Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver 𝔓.asIdeal v.asIdeal v.isPrime v.ne_bot

end Ramification

section Chi

theorem chi_eq (n : ℕ) : chiNegThree n = if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0 := rfl

theorem chi_mul (m n : ℕ) : chiNegThree (m * n) = chiNegThree m * chiNegThree n := by
  rw [chi_eq, chi_eq m, chi_eq n, Nat.mul_mod]
  have hm : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hn : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hm' : m % 3 <;> interval_cases hn' : n % 3 <;> simp

theorem chi_pow (n k : ℕ) : chiNegThree (n ^ k) = chiNegThree n ^ k := by
  induction k with
  | zero => simp [chi_eq]
  | succ k ih => rw [pow_succ, chi_mul, ih, pow_succ]

theorem chi_of_mod_eq_two {n : ℕ} (h : n % 3 = 2) : chiNegThree n = -1 := by
  rw [chi_eq]; simp [h]

end Chi

section NormArith

variable {K : Type*} [Field K] [NumberField K]

theorem norm_modEq_one {α : 𝓞 K} {n : ℕ} (h3 : 3 ∣ n)
    (hα : α - 1 ∈ Ideal.span {(n : 𝓞 K)}) : ((Algebra.norm ℤ α : ℤ) : ZMod 3) = 1 := by
  classical
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hα
  have hαe : α = 1 + n • y := by
    rw [nsmul_eq_mul, mul_comm, hy]; ring
  set b := RingOfIntegers.basis K
  have hM : Algebra.leftMulMatrix b α = 1 + n • Algebra.leftMulMatrix b y := by
    rw [hαe, map_add, map_one, map_nsmul]
  rw [Algebra.norm_eq_matrix_det b α, ← eq_intCast (Int.castRingHom (ZMod 3)), RingHom.map_det,
    hM, map_add, map_one, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3),
    (ZMod.natCast_eq_zero_iff n 3).mpr h3, zero_smul, add_zero, Matrix.det_one]

open scoped Classical in

theorem prod_nonreal_eq (x : K) (hx : x ≠ 0) :
    ∏ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => ¬ ComplexEmbedding.IsReal σ), σ x =
      ∏ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => ¬ ComplexEmbedding.IsReal σ), (‖σ x‖ : ℂ) := by
  classical
  set s := Finset.univ.filter (fun σ : K →+* ℂ => ¬ ComplexEmbedding.IsReal σ) with hs
  have hne : ∀ σ : K →+* ℂ, σ x ≠ 0 := fun σ => (map_ne_zero σ).mpr hx
  have hnorm : ∀ σ : K →+* ℂ, ((‖σ x‖ : ℝ) : ℂ) ≠ 0 := fun σ => by
    rw [Ne, Complex.ofReal_eq_zero, norm_eq_zero]; exact hne σ

  have h1 : ∏ σ ∈ s, σ x / (‖σ x‖ : ℂ) = 1 := by
    refine Finset.prod_involution (fun σ _ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_
    · intro σ _
      rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj, div_mul_div_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq, Complex.ofReal_pow, ← pow_two]
      exact div_self (pow_ne_zero 2 (hnorm σ))
    · intro σ hσ _
      rw [hs, Finset.mem_filter] at hσ
      intro h
      exact hσ.2 (ComplexEmbedding.isReal_iff.mpr h)
    · intro σ hσ
      change ComplexEmbedding.conjugate σ ∈ s
      rw [hs, Finset.mem_filter] at hσ
      rw [hs, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, fun h => hσ.2 (ComplexEmbedding.isReal_conjugate_iff.mp h)⟩
    · intro σ _
      exact NumberField.ComplexEmbedding.involutive_conjugate K σ
  calc ∏ σ ∈ s, σ x = ∏ σ ∈ s, (σ x / (‖σ x‖ : ℂ)) * (‖σ x‖ : ℂ) := by
        refine Finset.prod_congr rfl fun σ _ => ?_
        rw [div_mul_cancel₀ _ (hnorm σ)]
    _ = (∏ σ ∈ s, σ x / (‖σ x‖ : ℂ)) * ∏ σ ∈ s, (‖σ x‖ : ℂ) := Finset.prod_mul_distrib
    _ = ∏ σ ∈ s, (‖σ x‖ : ℂ) := by rw [h1, one_mul]

open scoped Classical in

theorem prod_real_eq (x : K) :
    ∏ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => ComplexEmbedding.IsReal σ), σ x =
      ((∏ φ : K →+* ℝ, φ x : ℝ) : ℂ) := by
  classical
  rw [Complex.ofReal_prod]
  symm
  refine Finset.prod_bij' (fun (φ : K →+* ℝ) _ => Complex.ofRealHom.comp φ)
    (fun (σ : K →+* ℂ) (hσ : σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => ComplexEmbedding.IsReal σ)) =>
      ComplexEmbedding.IsReal.embedding (Finset.mem_filter.mp hσ).2) ?_ ?_ ?_ ?_ ?_
  · intro φ _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [ComplexEmbedding.isReal_iff]
    ext y
    simp [ComplexEmbedding.conjugate_coe_eq]
  · intro σ hσ; exact Finset.mem_univ _
  · intro φ _
    ext y
    apply Complex.ofReal_injective
    rw [ComplexEmbedding.IsReal.coe_embedding_apply]
    rfl
  · intro σ hσ
    ext y
    exact ComplexEmbedding.IsReal.coe_embedding_apply _ y
  · intro φ _
    rfl

theorem norm_eq_prod_real_mul (x : K) (hx : x ≠ 0) :
    ∃ P : ℝ, 0 < P ∧ ((Algebra.norm ℚ x : ℚ) : ℝ) = (∏ φ : K →+* ℝ, φ x) * P := by
  classical
  refine ⟨∏ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => ¬ ComplexEmbedding.IsReal σ), ‖σ x‖,
    Finset.prod_pos fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr hx), ?_⟩
  apply Complex.ofReal_injective
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun σ => σ x)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun σ : K →+* ℂ => ComplexEmbedding.IsReal σ), prod_real_eq, prod_nonreal_eq x hx] at h
  rw [Complex.ofReal_prod] at h
  rw [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_prod, ← h, Complex.ofReal_ratCast,
    eq_ratCast]

theorem norm_lt_zero (x : K) (φ₀ : K →+* ℝ) (h0 : φ₀ x < 0)
    (hpos : ∀ φ : K →+* ℝ, φ ≠ φ₀ → 0 < φ x) : Algebra.norm ℚ x < 0 := by
  classical
  have hx : x ≠ 0 := fun h => by rw [h, map_zero] at h0; exact lt_irrefl _ h0
  obtain ⟨P, hP, hnorm⟩ := norm_eq_prod_real_mul x hx
  have hprod : (∏ φ : K →+* ℝ, φ x) < 0 := by
    rw [← Finset.mul_prod_erase Finset.univ (fun φ : K →+* ℝ => φ x) (Finset.mem_univ φ₀)]
    exact mul_neg_of_neg_of_pos h0 (Finset.prod_pos fun φ hφ => hpos φ (Finset.ne_of_mem_erase hφ))
  have : ((Algebra.norm ℚ x : ℚ) : ℝ) < 0 := by rw [hnorm]; exact mul_neg_of_neg_of_pos hprod hP
  exact_mod_cast this

theorem chi_absNorm_span_eq_neg_one {α : 𝓞 K} {n : ℕ} (h3 : 3 ∣ n)
    (hα : α - 1 ∈ Ideal.span {(n : 𝓞 K)}) (φ₀ : K →+* ℝ)
    (h0 : φ₀ (algebraMap (𝓞 K) K α) < 0)
    (hpos : ∀ φ : K →+* ℝ, φ ≠ φ₀ → 0 < φ (algebraMap (𝓞 K) K α)) :
    chiNegThree (Ideal.absNorm (Ideal.span {α} : Ideal (𝓞 K))) = -1 := by
  have hneg : Algebra.norm ℤ α < 0 := by
    have h := norm_lt_zero (algebraMap (𝓞 K) K α) φ₀ h0 hpos
    have hc := Algebra.coe_norm_int α
    have : ((Algebra.norm ℤ α : ℤ) : ℚ) < 0 := by rw [hc]; exact h
    exact_mod_cast this
  have hmod := norm_modEq_one h3 hα
  rw [Ideal.absNorm_span_singleton]
  apply chi_of_mod_eq_two
  have hcast : (((Algebra.norm ℤ α).natAbs : ℕ) : ZMod 3) = -1 := by
    have : (((Algebra.norm ℤ α).natAbs : ℕ) : ℤ) = -Algebra.norm ℤ α := by omega
    rw [← Int.cast_natCast, this, Int.cast_neg, hmod]
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_natCast] at hval
  rw [hval]
  rfl

end NormArith

section PerPrime

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] in

theorem raySymbol_eq_chi (ψ : HeightOneSpectrum (𝓞 E) → ℂˣ) (τ : E ≃ₐ[F] E)
    (good : HeightOneSpectrum (𝓞 E) → Prop)
    (hgood : ∀ 𝔓, good 𝔓 →
      (ψ 𝔓 : ℂ) * ψ (smulHOS τ 𝔓) = chiNegThree (Ideal.absNorm 𝔓.asIdeal))
    (J : Ideal (𝓞 E)) :
    J ≠ ⊥ → (∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.asIdeal ∣ J → good 𝔓) →
      ((raySymbol E (fun 𝔓 => ψ 𝔓 * ψ (smulHOS τ 𝔓)) (J : FractionalIdeal ((𝓞 E)⁰) E) : ℂˣ) : ℂ) =
        chiNegThree (Ideal.absNorm J) := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd (Submodule.zero_eq_bot) h
  | h₂ J hJ =>
    intro _ _
    rw [Ideal.isUnit_iff.mp hJ, raySymbol_coe_top, Ideal.absNorm_top]
    simp [chi_eq]
  | h₃ J p hJ hp ih =>
    intro _ hall
    have hp0 : p ≠ ⊥ := hp.ne_zero
    have hpP : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hp
    have hJ' : J ≠ ⊥ := hJ
    rw [raySymbol_coe_mul _ hp0 hJ', Units.val_mul, map_mul, chi_mul, Int.cast_mul,
      ih hJ' (fun 𝔓 h𝔓 => hall 𝔓 (dvd_mul_of_dvd_right h𝔓 p))]
    congr 1
    have h1 := raySymbol_coe_prime (fun 𝔓 => ψ 𝔓 * ψ (smulHOS τ 𝔓)) ⟨p, hpP, hp0⟩
    simp only at h1
    rw [h1, Units.val_mul]
    exact hgood ⟨p, hpP, hp0⟩ (hall ⟨p, hpP, hp0⟩ (dvd_mul_right p J))

end PerPrime

section Parity

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]

attribute [local instance] smulCommClass

structure Data (F : Type) [Field F] [NumberField F] (E : Type) [Field E] [NumberField E]
    [Algebra F E] where
  h2 : Module.finrank F E = 2
  ψ : HeightOneSpectrum (𝓞 E) → ℂˣ
  𝔣 : Ideal (𝓞 E)
  h𝔣 : 𝔣 ≠ ⊥
  Φ₀ : HeckeEigensystem F (ℤ√(-2))
  S₁ : Finset (HeightOneSpectrum (𝓞 F))
  hΦ₀ : ∀ v ∉ S₁,
      (∀ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 E), 𝔓₁ ≠ 𝔓₂ → 𝔓₁.under (𝓞 F) = v → 𝔓₂.under (𝓞 F) = v →
        iotaZsqrtdNegTwo (Φ₀.a v) = (ψ 𝔓₁ : ℂ) + ψ 𝔓₂ ∧ iotaZsqrtdNegTwo (Φ₀.b v) = (ψ 𝔓₁ : ℂ) * ψ 𝔓₂) ∧
      (∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 F) = v → v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2 →
        Φ₀.a v = 0 ∧ iotaZsqrtdNegTwo (Φ₀.b v) = -(ψ 𝔓 : ℂ))
  S₂ : Finset (HeightOneSpectrum (𝓞 F))
  hb : ∀ v ∉ S₂, Φ₀.b v = ((chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2))
  τ : E ≃ₐ[F] E
  hτ : τ ≠ 1
  ε : (E →+* ℝ) → ℂˣ
  hε : ∀ α : 𝓞 E, α ≠ 0 → α - 1 ∈ 𝔣 →
      raySymbol E ψ ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) =
        ∏ φ ∈ Finset.univ.filter (fun φ : E →+* ℝ => φ (algebraMap (𝓞 E) E α) < 0), ε φ

variable (D : Data F E)

noncomputable def Data.bad : Finset (HeightOneSpectrum (𝓞 F)) := by
  classical exact D.S₁ ∪ D.S₂ ∪ ramSet F E

theorem Data.not_mem_bad_iff (v : HeightOneSpectrum (𝓞 F)) :
    v ∉ D.bad ↔ (v ∉ D.S₁ ∧ v ∉ D.S₂) ∧ v ∉ ramSet F E := by
  classical
  simp only [Data.bad, Finset.mem_union, not_or]

theorem iota_intCast (z : ℤ) : iotaZsqrtdNegTwo (z : ℤ√(-2)) = z := map_intCast _ z

theorem Data.perPrime (𝔓 : HeightOneSpectrum (𝓞 E)) (hgood : 𝔓.under (𝓞 F) ∉ D.bad) :
    (D.ψ 𝔓 : ℂ) * D.ψ (smulHOS D.τ 𝔓) = chiNegThree (Ideal.absNorm 𝔓.asIdeal) := by
  set v := 𝔓.under (𝓞 F) with hv
  obtain ⟨⟨h1, h2'⟩, hram⟩ := (D.not_mem_bad_iff v).mp hgood
  have hbv := D.hb v h2'
  obtain ⟨hsplit, hinert⟩ := D.hΦ₀ v h1
  rw [absNorm_eq_pow hv.symm, chi_pow, Int.cast_pow]
  rcases dichotomy D.h2 D.hτ hram hv.symm with ⟨hne, hf⟩ | ⟨heq, hf⟩
  ·
    obtain ⟨-, hb⟩ := hsplit 𝔓 (smulHOS D.τ 𝔓) (Ne.symm hne) rfl (under_smulHOS D.τ 𝔓)
    rw [hf, pow_one, ← hb, hbv, iota_intCast]
  ·
    obtain ⟨-, hb⟩ := hinert 𝔓 rfl hf
    rw [heq, hf, hbv, iota_intCast] at *
    have : (D.ψ 𝔓 : ℂ) = -(chiNegThree (Ideal.absNorm v.asIdeal) : ℂ) := by
      rw [hb, neg_neg]
    rw [this]
    ring

noncomputable def Data.n₀ : ℕ := 3 * (Ideal.absNorm D.𝔣 * ∏ v ∈ D.bad, Ideal.absNorm v.asIdeal)

theorem Data.n₀_ne_zero : D.n₀ ≠ 0 := by
  rw [Data.n₀]
  refine mul_ne_zero (by norm_num) (mul_ne_zero ?_ ?_)
  · exact Ideal.absNorm_eq_zero_iff.not.mpr D.h𝔣
  · exact Finset.prod_ne_zero_iff.mpr fun v _ => Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot

theorem Data.three_dvd_n₀ : 3 ∣ D.n₀ := by
  unfold Data.n₀; exact dvd_mul_right 3 _

theorem Data.natCast_n₀_mem_𝔣 : (D.n₀ : 𝓞 E) ∈ D.𝔣 := by
  have h : Ideal.absNorm D.𝔣 ∣ D.n₀ := by
    rw [Data.n₀]; exact Dvd.dvd.mul_left (dvd_mul_right _ _) 3
  obtain ⟨k, hk⟩ := h
  rw [hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem Data.natCast_n₀_mem_of_mem_bad {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ D.bad) :
    (D.n₀ : 𝓞 F) ∈ v.asIdeal := by
  have h : Ideal.absNorm v.asIdeal ∣ D.n₀ := by
    rw [Data.n₀]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hv) _) 3
  obtain ⟨k, hk⟩ := h
  rw [hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

theorem Data.span_n₀_ne_bot : (Ideal.span {(D.n₀ : 𝓞 E)} : Ideal (𝓞 E)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
  exact D.n₀_ne_zero

theorem Data.good_of_dvd {α : 𝓞 E} (hα : α - 1 ∈ Ideal.span {(D.n₀ : 𝓞 E)})
    (𝔓 : HeightOneSpectrum (𝓞 E)) (hdvd : 𝔓.asIdeal ∣ Ideal.span {α}) : 𝔓.under (𝓞 F) ∉ D.bad := by
  intro hbad
  have hn : (D.n₀ : 𝓞 E) ∈ 𝔓.asIdeal := by
    have := (mem_under_iff (rfl : 𝔓.under (𝓞 F) = 𝔓.under (𝓞 F)) (D.n₀ : 𝓞 F)).mp
      (D.natCast_n₀_mem_of_mem_bad hbad)
    rwa [map_natCast] at this
  have hα1 : α - 1 ∈ 𝔓.asIdeal :=
    (Ideal.span_singleton_le_iff_mem _ |>.mpr hn) hα
  have hα𝔓 : α ∈ 𝔓.asIdeal := Ideal.dvd_span_singleton.mp hdvd
  have : (1 : 𝓞 E) ∈ 𝔓.asIdeal := by
    have := 𝔓.asIdeal.sub_mem hα𝔓 hα1
    rwa [sub_sub_cancel] at this
  exact 𝔓.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

theorem Data.hsign (φ φ' : E →+* ℝ) (hne : φ ≠ φ') (hF : φ.comp (algebraMap F E) = φ'.comp (algebraMap F E)) :
    D.ε φ * D.ε φ' = -1 := by
  classical
  have hττ : D.τ * D.τ = 1 := mul_self_eq_one D.h2 D.hτ
  have hφ' : ∀ x, φ' x = φ (D.τ x) := realEmb_eq_comp D.h2 D.hτ hne hF

  obtain ⟨α, hα0, hα1, hαsign⟩ := NumberField.exists_ne_zero_and_sub_one_mem_and_lt_zero_iff E
    (Ideal.span {(D.n₀ : 𝓞 E)}) D.span_n₀_ne_bot ({φ} : Set (E →+* ℝ))
  simp only [Set.mem_singleton_iff] at hαsign
  have hα1𝔣 : α - 1 ∈ D.𝔣 := (Ideal.span_singleton_le_iff_mem _ |>.mpr D.natCast_n₀_mem_𝔣) hα1
  have hτα0 : D.τ • α ≠ 0 := fun h => hα0 (by
    have := congrArg (fun y => D.τ⁻¹ • y) h
    simpa using this)
  have hτα1 : D.τ • α - 1 ∈ D.𝔣 := by
    have h : D.τ • α - 1 = D.τ • (α - 1) := by rw [smul_sub, smul_one]
    rw [h]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hα1
    rw [← hy, smul_mul', smul_natCast]
    exact Ideal.mul_mem_left _ _ D.natCast_n₀_mem_𝔣

  have hrayα : raySymbol E D.ψ ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) = D.ε φ := by
    rw [D.hε α hα0 hα1𝔣]
    have : Finset.univ.filter (fun ρ : E →+* ℝ => ρ (algebraMap (𝓞 E) E α) < 0) = {φ} := by
      ext ρ; simp [hαsign ρ]
    rw [this, Finset.prod_singleton]

  have hrayτα : raySymbol E D.ψ ((Ideal.span {D.τ • α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) =
      D.ε φ' := by
    rw [D.hε (D.τ • α) hτα0 hτα1]
    have : Finset.univ.filter (fun ρ : E →+* ℝ => ρ (algebraMap (𝓞 E) E (D.τ • α)) < 0) = {φ'} := by
      ext ρ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [algebraMap_smul]
      have key : ρ (D.τ (algebraMap (𝓞 E) E α)) < 0 ↔ ρ.comp D.τ.toRingEquiv.toRingHom = φ :=
        hαsign (ρ.comp D.τ.toRingEquiv.toRingHom)
      rw [key]
      constructor
      · intro h
        ext x
        rw [hφ', ← h]
        change ρ x = ρ (D.τ (D.τ x))
        rw [← AlgEquiv.mul_apply, hττ, AlgEquiv.one_apply]
      · intro h
        ext x
        change ρ (D.τ x) = φ x
        rw [h, hφ', ← AlgEquiv.mul_apply, hττ, AlgEquiv.one_apply]
    rw [this, Finset.prod_singleton]

  have hspan0 : (Ideal.span {α} : Ideal (𝓞 E)) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hα0
  have hprod : (D.ε φ * D.ε φ' : ℂˣ) =
      raySymbol E (fun 𝔓 => D.ψ 𝔓 * D.ψ (smulHOS D.τ 𝔓))
        ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) := by
    rw [← hrayα, ← hrayτα, ← smul_span_singleton, raySymbol_smul D.ψ D.τ _ hspan0,
      ← raySymbol_fun_mul]
    rfl
  have hchi := raySymbol_eq_chi D.ψ D.τ (fun 𝔓 => 𝔓.under (𝓞 F) ∉ D.bad) D.perPrime
    (Ideal.span {α}) hspan0 (D.good_of_dvd hα1)
  have hval : chiNegThree (Ideal.absNorm (Ideal.span {α} : Ideal (𝓞 E))) = -1 :=
    chi_absNorm_span_eq_neg_one D.three_dvd_n₀ hα1 φ ((hαsign φ).mpr rfl)
      (fun ρ hρ => lt_of_le_of_ne (not_lt.mp (fun h => hρ ((hαsign ρ).mp h)))
        (by rw [ne_comm, map_ne_zero]; exact RingOfIntegers.coe_ne_zero_iff.mpr hα0))
  apply Units.ext
  rw [hprod, hchi, hval, Units.val_neg, Units.val_one]
  push_cast
  ring

end Parity

section Transport

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in

noncomputable def transportRealization (pins : CarrierPins F) {Ψ Ψ' : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Ψ) (hlev : Ψ'.level = Ψ.level)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, Ψ'.a v = Ψ.a v ∧ Ψ'.b v = Ψ.b v) :
    SmoothCuspRealizationAt F pins Ψ' where
  toFun := R.toFun
  exists_ne_zero := R.exists_ne_zero
  centralChar := R.centralChar
  smoothCusp := R.smoothCusp
  level_invariant := by rw [hlev]; exact R.level_invariant
  exceptionalSet := R.exceptionalSet ∪ S
  hecke_eigen := fun v hv => by
    rw [Finset.mem_union, not_or] at hv
    rw [hlev, (hS v hv.2).1]
    exact R.hecke_eigen v hv.1
  central_eigen := fun v hv g => by
    rw [Finset.mem_union, not_or] at hv
    rw [(hS v hv.2).2]
    exact R.central_eigen v hv.1 g

open scoped Classical in
@[scoped simp] theorem transportRealization_toFun (pins : CarrierPins F) {Ψ Ψ' : HeckeEigensystem F ℂ}
    (R : SmoothCuspRealizationAt F pins Ψ) (hlev : Ψ'.level = Ψ.level)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, Ψ'.a v = Ψ.a v ∧ Ψ'.b v = Ψ.b v) :
    (transportRealization pins R hlev S hS).toFun = R.toFun := rfl

end Transport

end GenuineCuspAISol
p2m_reactivate "P2MW.S_LanglandsTunnell_exists_agreesAwayFromFinite_isGenuineCusp_of_raySymbol_eq_one.GenuineCuspAISol"

open GenuineCuspAISol in
theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    {E : Type} [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2)
    (ψ : HeightOneSpectrum (𝓞 E) → ℂˣ) (𝔣 : Ideal (𝓞 E)) (h𝔣 : 𝔣 ≠ ⊥)
    (hψ : ∀ α : 𝓞 E, α ≠ 0 → α - 1 ∈ 𝔣 → (∀ τ : E →+* ℝ, 0 < τ (algebraMap (𝓞 E) E α)) →
      raySymbol E ψ ((Ideal.span {α} : Ideal (𝓞 E)) : FractionalIdeal ((𝓞 E)⁰) E) = 1)
    (hcusp : ∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ v ∉ S, ∃ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 E),
      𝔓₁ ≠ 𝔓₂ ∧ 𝔓₁.under (𝓞 F) = v ∧ 𝔓₂.under (𝓞 F) = v ∧ ψ 𝔓₁ ≠ ψ 𝔓₂)
    (Φ₀ : HeckeEigensystem F (ℤ√(-2)))
    (hΦ₀ : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      (∀ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 E), 𝔓₁ ≠ 𝔓₂ → 𝔓₁.under (𝓞 F) = v → 𝔓₂.under (𝓞 F) = v →
        iotaZsqrtdNegTwo (Φ₀.a v) = (ψ 𝔓₁ : ℂ) + ψ 𝔓₂ ∧ iotaZsqrtdNegTwo (Φ₀.b v) = (ψ 𝔓₁ : ℂ) * ψ 𝔓₂) ∧
      (∀ 𝔓 : HeightOneSpectrum (𝓞 E), 𝔓.under (𝓞 F) = v → v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2 →
        Φ₀.a v = 0 ∧ iotaZsqrtdNegTwo (Φ₀.b v) = -(ψ 𝔓 : ℂ)))
    (hb : ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ v ∉ S,
      Φ₀.b v = ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2)))
    (hc : 0 < c) (hd₁ : 0 < d₁) :
    ∃ Φ : HeckeEigensystem F (ℤ√(-2)), Φ.AgreesAwayFromFinite Φ₀ ∧
      (∃ R : SmoothCuspRealizationAt F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
          (Φ.map iotaZsqrtdNegTwo).toRawCentral,
        IsGenuineCuspRealizationAt F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
          (Φ.map iotaZsqrtdNegTwo).toRawCentral R ∧
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal,
          HasArchCharacterAt₀ F w (archWeightOneAt hw) R.toFun) ∧
        (∀ w : InfinitePlace F, ∀ hw : w.IsReal, IsArchHolomorphicAt w hw R.toFun)) := by
  classical
  haveI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.decEq _

  obtain ⟨τ, hτ⟩ := exists_ne_one h2
  obtain ⟨ε, -, hε⟩ :=
    NumberField.exists_sq_eq_one_and_raySymbol_span_singleton_eq_prod_of_forall_pos E ψ 𝔣 h𝔣 hψ
  obtain ⟨S₁, hS₁⟩ := hΦ₀
  obtain ⟨S₂, hS₂⟩ := hb
  let D : Data F E :=
    { h2 := h2, ψ := ψ, 𝔣 := 𝔣, h𝔣 := h𝔣, Φ₀ := Φ₀, S₁ := S₁, hΦ₀ := hS₁, S₂ := S₂, hb := hS₂,
      τ := τ, hτ := hτ, ε := ε, hε := hε }

  have hsign : ∀ φ φ' : E →+* ℝ, φ ≠ φ' → φ.comp (algebraMap F E) = φ'.comp (algebraMap F E) →
      ε φ * ε φ' = -1 := fun φ φ' hne hF => D.hsign φ φ' hne hF

  have hcusp' : ∃ w' w'' : HeightOneSpectrum (𝓞 E), w' ≠ w'' ∧ w'.under (𝓞 F) = w''.under (𝓞 F) ∧
      ¬ w'.asIdeal ∣ 𝔣 ∧ ¬ w''.asIdeal ∣ 𝔣 ∧ ψ w' ≠ ψ w'' := by
    have hfin : {v : HeightOneSpectrum (𝓞 F) | ∃ 𝔓 : HeightOneSpectrum (𝓞 E),
        𝔓.asIdeal ∣ 𝔣 ∧ 𝔓.under (𝓞 F) = v}.Finite := by
      have : {v : HeightOneSpectrum (𝓞 F) | ∃ 𝔓 : HeightOneSpectrum (𝓞 E),
          𝔓.asIdeal ∣ 𝔣 ∧ 𝔓.under (𝓞 F) = v} =
          (fun 𝔓 : HeightOneSpectrum (𝓞 E) => 𝔓.under (𝓞 F)) ''
            {𝔓 : HeightOneSpectrum (𝓞 E) | 𝔓.asIdeal ∣ 𝔣} := by
        ext v; simp
      rw [this]
      exact (Ideal.finite_factors h𝔣).image _
    obtain ⟨v, hv, 𝔓₁, 𝔓₂, hne, h1, h2', hψne⟩ := hcusp hfin.toFinset
    rw [Set.Finite.mem_toFinset] at hv
    refine ⟨𝔓₁, 𝔓₂, hne, h1.trans h2'.symm, fun h => hv ⟨𝔓₁, h, h1⟩, fun h => hv ⟨𝔓₂, h, h2'⟩, hψne⟩

  obtain ⟨Ψ, ⟨R, hR, harch, hhol⟩, SΘ, htab⟩ :=
    LanglandsTunnell.exists_isGenuineCusp_archWeightOne_a_eq_of_raySymbol_eq_prod_of_finrank_eq_two
      F E h2 𝔣 h𝔣 ψ ε hε hsign hcusp' c u d₁ d₂ T hc hd₁

  let Φ : HeckeEigensystem F (ℤ√(-2)) := ⟨Ψ.level, Ψ.level_ne_bot, Φ₀.a, Φ₀.b⟩

  have hagree : ∀ v ∉ SΘ ∪ S₁ ∪ ramSet F E,
      (Φ.map iotaZsqrtdNegTwo).toRawCentral.a v = Ψ.toRawCentral.a v ∧
        (Φ.map iotaZsqrtdNegTwo).toRawCentral.b v = Ψ.toRawCentral.b v := by
    intro v hv
    simp only [Finset.mem_union, not_or] at hv
    obtain ⟨⟨hvΘ, hv1⟩, hvram⟩ := hv
    change iotaZsqrtdNegTwo (Φ₀.a v) = Ψ.a v ∧
      (HeckeEigensystem.cNorm v)⁻¹ * iotaZsqrtdNegTwo (Φ₀.b v) = (HeckeEigensystem.cNorm v)⁻¹ * Ψ.b v
    obtain ⟨𝔓, h𝔓⟩ := exists_under_eq (E := E) v
    obtain ⟨hsplit₀, hinert₀⟩ := hS₁ v hv1
    obtain ⟨hsplitΘ, hinertΘ⟩ := htab v hvΘ
    rcases dichotomy h2 hτ hvram h𝔓 with ⟨hne, hf⟩ | ⟨heq, hf⟩
    · obtain ⟨ha, hb'⟩ := hsplit₀ 𝔓 (smulHOS τ 𝔓) (Ne.symm hne) h𝔓 ((under_smulHOS τ 𝔓).trans h𝔓)
      obtain ⟨haΘ, hbΘ⟩ := hsplitΘ 𝔓 (smulHOS τ 𝔓) (Ne.symm hne) h𝔓 ((under_smulHOS τ 𝔓).trans h𝔓)
      exact ⟨ha.trans haΘ.symm, by rw [hb', hbΘ]⟩
    · obtain ⟨ha, hb'⟩ := hinert₀ 𝔓 h𝔓 hf
      obtain ⟨haΘ, hbΘ⟩ := hinertΘ 𝔓 h𝔓 hf
      exact ⟨by rw [ha, map_zero, haΘ], by rw [hb', hbΘ]⟩

  let R' := transportRealization _ R (rfl : (Φ.map iotaZsqrtdNegTwo).toRawCentral.level = Ψ.toRawCentral.level)
    (SΘ ∪ S₁ ∪ ramSet F E) hagree
  refine ⟨Φ, ⟨∅, fun v _ => ⟨rfl, rfl⟩⟩, R', ?_, ?_, ?_⟩
  · exact hR
  · exact harch
  · exact hhol

end S_LanglandsTunnell_exists_agreesAwayFromFinite_isGenuineCusp_of_raySymbol_eq_one
end P2MW
export P2MW.S_LanglandsTunnell_exists_agreesAwayFromFinite_isGenuineCusp_of_raySymbol_eq_one (solution)
