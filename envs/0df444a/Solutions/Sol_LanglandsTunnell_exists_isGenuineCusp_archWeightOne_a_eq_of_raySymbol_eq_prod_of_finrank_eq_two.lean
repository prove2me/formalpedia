-- Prove2me | solution 1 for LanglandsTunnell.exists_isGenuineCusp_archWeightOne_a_eq_of_raySymbol_eq_prod_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/b1eac5dd-cbe4-539a-b947-b9128fa59df3

import Mathlib
import Definitions.Def_AutomorphicForm_HeckeEigensystem
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_HeckeCharacter_exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod
import Theorems.Thm_LanglandsTunnell_exists_isGenuineCusp_archWeightOne_a_eq_of_isFiniteOrderHeckeChar_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_isGenuineCusp_archWeightOne_a_eq_of_raySymbol_eq_prod_of_finrank_eq_two
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom RestrictedProduct.SecondCountableTopology_of_principal"
p2m_attr_erase "instance" "instCountableElemSetSetsCofinite_definitions instCountableHeightOneSpectrumRingOfIntegers_definitions instCountableHeightOneSpectrumRingOfIntegersRat_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val MeasureTheory.L2.kernelIntegralLM_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right"
p2m_attr_erase "simp" "IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply"
p2m_attr_erase "simp" "MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.IsStableLinearOn.coe_toEnd_apply"
p2m_attr_erase "simp" "AutomorphicForm.ArchRepAt.mk.sizeOf_spec AutomorphicForm.IsIsotypicCuspFormAt.toRealization_toFun AutomorphicForm.ArchTypeFamily.mk.sizeOf_spec AutomorphicForm.charRep_apply AutomorphicForm.ArchRepAt.mk.injEq AutomorphicForm.ArchTypeFamily.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain HeckeCharacter Deep.NTSupply

open scoped nonZeroDivisors

noncomputable section

namespace DihedralRaySymbolAssemblySol

variable {K : Type} [Field K] [NumberField K]

theorem idealMultiplicity_eq_zero_of_not_dvd {𝔣 : Ideal (𝓞 K)} (h𝔣 : 𝔣 ≠ ⊥)
    {v : HeightOneSpectrum (𝓞 K)} (hv : ¬ v.asIdeal ∣ 𝔣) : idealMultiplicity K v 𝔣 = 0 := by
  classical
  unfold idealMultiplicity
  by_contra h
  exact hv ((Associates.count_ne_zero_iff_dvd h𝔣 v.irreducible).mp h)

theorem isUnramifiedCharAt_of_modulus {ξ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {𝔣 : Ideal (𝓞 K)}
    (h𝔣 : 𝔣 ≠ ⊥) (hmod : AdmitsModulus K ξ 𝔣) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ 𝔣) : IsUnramifiedCharAt ξ v := by
  classical
  intro t ht htinv
  rw [localChar_apply]
  apply hmod
  · rfl
  · intro w

    have hval1 : Valued.v (t : v.adicCompletion K) = 1 := by
      apply le_antisymm ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp ht)
      have h2 : Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp htinv
      have hprod : Valued.v (t : v.adicCompletion K) *
          Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      have hne : Valued.v (t : v.adicCompletion K) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hprod; exact zero_ne_one hprod
      calc (1 : WithZero (Multiplicative ℤ))
          = Valued.v (t : v.adicCompletion K) *
              Valued.v ((t⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) := hprod.symm
        _ ≤ Valued.v (t : v.adicCompletion K) * 1 := by gcongr
        _ = Valued.v (t : v.adicCompletion K) := mul_one _
    show Valued.v (((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K) w) = 1 ∧
      Valued.v (((localUnit (𝓞 K) K v t : (FiniteAdeleRing (𝓞 K) K)ˣ) :
        FiniteAdeleRing (𝓞 K) K) w - 1) ≤ WithZero.exp (-(idealMultiplicity K w 𝔣 : ℤ))
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, idealMultiplicity_eq_zero_of_not_dvd h𝔣 hv]
      refine ⟨hval1, ?_⟩
      simp only [CharP.cast_eq_zero, neg_zero, WithZero.exp_zero]
      calc Valued.v ((t : w.adicCompletion K) - 1)
          ≤ max (Valued.v (t : w.adicCompletion K)) (Valued.v (1 : w.adicCompletion K)) :=
            Valuation.map_sub _ _ _
        _ = 1 := by rw [hval1, map_one, max_self]
    · rw [localUnit_apply_of_ne (𝓞 K) K v t hw]
      refine ⟨map_one _, ?_⟩
      rw [sub_self, map_zero]
      exact zero_le'

omit [NumberField K] in
theorem mk_ofRealHom_comp_embedding_of_isReal {w : InfinitePlace K} (hw : w.IsReal) :
    InfinitePlace.mk (Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw)) = w := by
  have h : Complex.ofRealHom.comp (InfinitePlace.embedding_of_isReal hw) = w.embedding := by
    ext x
    exact InfinitePlace.embedding_of_isReal_apply hw x
  rw [h, InfinitePlace.mk_embedding]

omit [NumberField K] in
theorem comp_eq_comp_of_comap_eq {E : Type} [Field E] (f : E →+* K) {w w' : InfinitePlace K}
    (hw : w.IsReal) (hw' : w'.IsReal) (h : w.comap f = w'.comap f) :
    (InfinitePlace.embedding_of_isReal hw).comp f = (InfinitePlace.embedding_of_isReal hw').comp f := by
  rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', InfinitePlace.comap_mk,
    InfinitePlace.comap_mk, InfinitePlace.mk_eq_iff] at h
  have hreal : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.mp hw
  have hC : w.embedding.comp f = w'.embedding.comp f := by
    rcases h with h | h
    · exact h
    · rw [← h]
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, ComplexEmbedding.conjugate_coe_eq]
      exact (RingHom.congr_fun hreal (f x)).symm
  ext x
  apply Complex.ofReal_injective
  have := RingHom.congr_fun hC x
  simpa only [RingHom.coe_comp, Function.comp_apply, InfinitePlace.embedding_of_isReal_apply] using this

end DihedralRaySymbolAssemblySol

end

open DihedralRaySymbolAssemblySol in
theorem solution
    (E : Type) [Field E] [NumberField E] (M : Type) [Field M] [NumberField M] [Algebra E M]
    (h2 : Module.finrank E M = 2)
    (𝔣 : Ideal (𝓞 M)) (h𝔣 : 𝔣 ≠ ⊥) (ψ : HeightOneSpectrum (𝓞 M) → ℂˣ) (ε : (M →+* ℝ) → ℂˣ)
    (hψ : ∀ α : 𝓞 M, α ≠ 0 → α - 1 ∈ 𝔣 →
      raySymbol M ψ ((Ideal.span {α} : Ideal (𝓞 M)) : FractionalIdeal ((𝓞 M)⁰) M) =
        ∏ φ ∈ Finset.univ.filter (fun φ : M →+* ℝ => φ (algebraMap (𝓞 M) M α) < 0), ε φ)
    (hsign : ∀ φ φ' : M →+* ℝ, φ ≠ φ' → φ.comp (algebraMap E M) = φ'.comp (algebraMap E M) →
      ε φ * ε φ' = -1)
    (hcusp : ∃ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' ∧ w'.under (𝓞 E) = w''.under (𝓞 E) ∧
      ¬ w'.asIdeal ∣ 𝔣 ∧ ¬ w''.asIdeal ∣ 𝔣 ∧ ψ w' ≠ ψ w'')
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
          Ψ.a w = (ψ w' : ℂ) + ψ w'' ∧ Ψ.b w = (ψ w' : ℂ) * ψ w'') ∧
        (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → w.asIdeal.inertiaDeg' w'.asIdeal = 2 →
          Ψ.a w = 0 ∧ Ψ.b w = -(ψ w' : ℂ)) := by
  classical

  obtain ⟨ξ, hfo, hmod, _huni, hval, hsgn⟩ :=
    HeckeCharacter.exists_isFiniteOrderHeckeChar_apply_uniformizerIdele_eq_archLocalChar_neg_one_eq_of_raySymbol_eq_prod
      M 𝔣 h𝔣 ψ ε hψ

  set S₀ : Finset (HeightOneSpectrum (𝓞 M)) := (Ideal.finite_factors h𝔣).toFinset with hS₀
  have hmemS₀ : ∀ w' : HeightOneSpectrum (𝓞 M), w' ∈ S₀ ↔ w'.asIdeal ∣ 𝔣 := fun w' => by
    rw [hS₀, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hunr : ∀ w' ∉ S₀, IsUnramifiedCharAt ξ w' := fun w' hw' =>
    isUnramifiedCharAt_of_modulus h𝔣 hmod ((hmemS₀ w').not.mp hw')

  have hsgn' : ∀ (φ : M →+* ℝ) (w : InfinitePlace M),
      InfinitePlace.mk (Complex.ofRealHom.comp φ) = w →
        archLocalChar ξ w (-1) = ε φ := by
    rintro φ w rfl
    exact hsgn φ
  have hsignW : ∀ w w' : InfinitePlace M, w ≠ w' → w.IsReal → w'.IsReal →
      w.comap (algebraMap E M) = w'.comap (algebraMap E M) →
      ((archLocalChar ξ w (-1) : ℂˣ) : ℂ) * archLocalChar ξ w' (-1) = -1 := by
    intro w w' hne hw hw' hcomap
    set φ := InfinitePlace.embedding_of_isReal hw with hφ
    set φ' := InfinitePlace.embedding_of_isReal hw' with hφ'
    have hwφ : InfinitePlace.mk (Complex.ofRealHom.comp φ) = w :=
      mk_ofRealHom_comp_embedding_of_isReal hw
    have hwφ' : InfinitePlace.mk (Complex.ofRealHom.comp φ') = w' :=
      mk_ofRealHom_comp_embedding_of_isReal hw'
    have hφne : φ ≠ φ' := by
      intro h
      apply hne
      rw [← hwφ, ← hwφ', h]
    have hres : φ.comp (algebraMap E M) = φ'.comp (algebraMap E M) :=
      comp_eq_comp_of_comap_eq (algebraMap E M) hw hw' hcomap
    rw [hsgn' φ w hwφ, hsgn' φ' w' hwφ', ← Units.val_mul, hsign φ φ' hφne hres]
    simp

  have hcusp' : ∃ w' w'' : HeightOneSpectrum (𝓞 M), w' ≠ w'' ∧ w'.under (𝓞 E) = w''.under (𝓞 E) ∧
      w' ∉ S₀ ∧ w'' ∉ S₀ ∧ ξ (uniformizerIdele M w') ≠ ξ (uniformizerIdele M w'') := by
    obtain ⟨w', w'', hne, hunder, h1, h2, hψne⟩ := hcusp
    refine ⟨w', w'', hne, hunder, (hmemS₀ w').not.mpr h1, (hmemS₀ w'').not.mpr h2, ?_⟩
    rwa [hval w' h1, hval w'' h2]

  obtain ⟨Ψ, hR, S, hS⟩ :=
    LanglandsTunnell.exists_isGenuineCusp_archWeightOne_a_eq_of_isFiniteOrderHeckeChar_of_finrank_eq_two
      E M h2 ξ hfo S₀ hunr hsignW hcusp' c u d₁ d₂ T hc hd₁
  refine ⟨Ψ, hR, S ∪ S₀.image (fun w' => w'.under (𝓞 E)), fun w hw => ?_⟩
  rw [Finset.mem_union, not_or] at hw

  have hnd : ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 E) = w → ¬ w'.asIdeal ∣ 𝔣 := by
    intro w' hw' hdvd
    exact hw.2 (Finset.mem_image.mpr ⟨w', (hmemS₀ w').mpr hdvd, hw'⟩)
  obtain ⟨hsplit, hinert⟩ := hS w hw.1
  refine ⟨fun w' w'' hne h' h'' => ?_, fun w' h' hf => ?_⟩
  · obtain ⟨ha, hb⟩ := hsplit w' w'' hne h' h''
    rw [hval w' (hnd w' h'), hval w'' (hnd w'' h'')] at ha hb
    exact ⟨ha, hb⟩
  · obtain ⟨ha, hb⟩ := hinert w' h' hf
    rw [hval w' (hnd w' h')] at hb
    exact ⟨ha, hb⟩

end S_LanglandsTunnell_exists_isGenuineCusp_archWeightOne_a_eq_of_raySymbol_eq_prod_of_finrank_eq_two
end P2MW
export P2MW.S_LanglandsTunnell_exists_isGenuineCusp_archWeightOne_a_eq_of_raySymbol_eq_prod_of_finrank_eq_two (solution)
