-- Prove2me | solution 1 for LanglandsTunnell.exists_quadratic_rayClassChar_table_liftTraceSeed_sylowH_of_detDictionaryRow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/4813ec92-8557-530d-a6d6-a7f67496c839

import Definitions.Def_LanglandsTunnell_QuatH
import Definitions.Def_LanglandsTunnell_DetDictionaryRow
import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_NarrowRayClassGroup
import Theorems.Thm_LanglandsTunnell_liftTraceSeed_sylowH_table_eq_artinValue
import Theorems.Thm_LanglandsTunnell_exists_split_place_artinValue_ne
import Theorems.Thm_LanglandsTunnell_P2_raySymbol_artinValue_span_eq_one
import Theorems.Thm_LanglandsTunnell_liftTraceSeed_b_eq_chiNegThree_of_detDictionaryRow
import Theorems.Thm_LanglandsTunnell_exists_finset_forall_inertia_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_quadratic_rayClassChar_table_liftTraceSeed_sylowH_of_detDictionaryRow
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers"
p2m_attr_erase "instance" "instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "instance" "IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply"
p2m_attr_erase "simp" "IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option autoImplicit false

open NumberField
open IsDedekindDomain
open AutomorphicForm
open Deep.NTSupply
open scoped nonZeroDivisors
open LanglandsTunnell

private theorem cubicGlue_exists_zeta :
    ∃ ζ : ℂ, ζ ^ 4 = -1 ∧ ζ + ζ ^ 3 = iotaZsqrtdNegTwo Zsqrtd.sqrtd := by
  have hs : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hR : iotaZsqrtdNegTwo Zsqrtd.sqrtd = ((Real.sqrt 2 : ℝ) : ℂ) * Complex.I := by
    simp [iotaZsqrtdNegTwo_apply, Zsqrtd.sqrtd]
  refine ⟨((Real.sqrt 2 : ℝ) : ℂ) / 2 * (1 + Complex.I), ?_, ?_⟩
  · linear_combination ((((Real.sqrt 2 : ℝ) : ℂ) ^ 2 + 2) * (1 + Complex.I) ^ 4 / 16) * hs
      + ((Complex.I ^ 2 + 4 * Complex.I + 5) / 4) * Complex.I_sq
  · rw [hR]
    linear_combination (((Real.sqrt 2 : ℝ) : ℂ) * (1 + Complex.I) ^ 3 / 8) * hs
      + (((Real.sqrt 2 : ℝ) : ℂ) * (Complex.I + 3) / 4) * Complex.I_sq

private theorem cubicGlue_exists_modulus (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] :
    ∃ 𝔣₀ : Ideal (𝓞 ℚ), 𝔣₀ ≠ ⊥ ∧
      ∀ v : HeightOneSpectrum (𝓞 ℚ), (P2.Artin.primeAbove ℚ L v).inertia (L ≃ₐ[ℚ] L) ≠ ⊥ →
        v.asIdeal ^ (4 * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) v.asIdeal
          + 2 * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) v.asIdeal + 1) ∣ 𝔣₀ := by
  obtain ⟨B, hB⟩ := exists_finset_forall_inertia_eq_bot L
  have hinj : Function.Injective (Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ)) := fun v w h =>
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)
  have hfin : {v : HeightOneSpectrum (𝓞 ℚ) | Rat.HeightOneSpectrum.natGenerator v ∈ B}.Finite :=
    B.finite_toSet.preimage hinj.injOn
  refine ⟨∏ v ∈ hfin.toFinset, v.asIdeal ^ (4 * Ideal.ramificationIdx' (Ideal.span {(2 : ℤ)}) v.asIdeal
      + 2 * Ideal.ramificationIdx' (Ideal.span {(3 : ℤ)}) v.asIdeal + 1), ?_, ?_⟩
  · rw [← Ideal.zero_eq_bot]
    exact Finset.prod_ne_zero_iff.mpr fun v _ =>
      pow_ne_zero _ (by simpa [Ideal.zero_eq_bot] using v.ne_bot)
  · intro v hv
    apply Finset.dvd_prod_of_mem
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    by_contra hnot
    apply hv
    have hn : (Rat.HeightOneSpectrum.natGenerator v).Prime := Rat.HeightOneSpectrum.prime_natGenerator v
    haveI : Fact (Rat.HeightOneSpectrum.natGenerator v).Prime := ⟨hn⟩
    have hmemv : ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
      obtain ⟨x, hx, hfx⟩ :=
        (Ideal.mem_map_of_equiv _ _).1 ((Rat.HeightOneSpectrum.natGenerator_dvd_iff v).1 dvd_rfl)
      have hx' : x = ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ) :=
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective (by rw [hfx, map_natCast])
      exact hx' ▸ hx
    have hmemQ : ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 L) ∈ P2.Artin.primeAbove ℚ L v := by
      rw [← P2.Artin.under_primeAbove ℚ L v] at hmemv
      have h' : algebraMap (𝓞 ℚ) (𝓞 L) ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : 𝓞 ℚ)
          ∈ P2.Artin.primeAbove ℚ L v := hmemv
      rwa [map_natCast] at h'
    haveI hQprime : (P2.Artin.primeAbove ℚ L v).IsPrime := Ideal.IsMaximal.isPrime inferInstance
    have hlies : (P2.Artin.primeAbove ℚ L v).LiesOver
        (FrobeniusDensity.ratPrimeIdeal (Rat.HeightOneSpectrum.natGenerator v)) := by
      refine ⟨(FrobeniusDensity.isMaximal_ratPrimeIdeal _).eq_of_le
        (Ideal.comap_ne_top _ hQprime.ne_top) ?_⟩
      refine (Ideal.span_singleton_le_iff_mem _).mpr ?_
      show algebraMap ℤ (𝓞 L) ((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ∈ P2.Artin.primeAbove ℚ L v
      simpa using hmemQ
    exact hB hn hnot (P2.Artin.primeAbove ℚ L v) hQprime hlies

private theorem cubicGlue_algebraMap_injective (M : Type) [Field M] [NumberField M] :
    Function.Injective (algebraMap (𝓞 ℚ) (𝓞 M)) := by
  have hZ : Function.Injective
      ((algebraMap (𝓞 ℚ) (𝓞 M)).comp (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom) :=
    RingHom.injective_int _
  intro a b hab
  apply (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).injective
  apply hZ
  simpa using hab

theorem solution
    {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) (hdet : DetDictionaryRow e) :
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra ↥(fixFld (sylowH e)) M),
      Module.finrank ↥(fixFld (sylowH e)) M = 2 ∧
      ∃ (ψ : HeightOneSpectrum (𝓞 M) → ℂˣ) (𝔣 : Ideal (𝓞 M)), 𝔣 ≠ ⊥ ∧
      (∀ α : 𝓞 M, α ≠ 0 → α - 1 ∈ 𝔣 → (∀ τ : M →+* ℝ, 0 < τ (algebraMap (𝓞 M) M α)) →
      raySymbol M ψ ((Ideal.span {α} : Ideal (𝓞 M)) : FractionalIdeal ((𝓞 M)⁰) M) = 1) ∧
      (∀ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (sylowH e)))), ∃ v ∉ S, ∃ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 M),
      𝔓₁ ≠ 𝔓₂ ∧ 𝔓₁.under (𝓞 ↥(fixFld (sylowH e))) = v ∧ 𝔓₂.under (𝓞 ↥(fixFld (sylowH e))) = v ∧ ψ 𝔓₁ ≠ ψ 𝔓₂) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (sylowH e)))), ∀ v ∉ S,
      (∀ 𝔓₁ 𝔓₂ : HeightOneSpectrum (𝓞 M), 𝔓₁ ≠ 𝔓₂ → 𝔓₁.under (𝓞 ↥(fixFld (sylowH e))) = v →
          𝔓₂.under (𝓞 ↥(fixFld (sylowH e))) = v →
        iotaZsqrtdNegTwo ((P2.liftTraceSeed e (sylowH e)).a v) = (ψ 𝔓₁ : ℂ) + ψ 𝔓₂ ∧
            iotaZsqrtdNegTwo ((P2.liftTraceSeed e (sylowH e)).b v) = (ψ 𝔓₁ : ℂ) * ψ 𝔓₂) ∧
      (∀ 𝔓 : HeightOneSpectrum (𝓞 M), 𝔓.under (𝓞 ↥(fixFld (sylowH e))) = v → v.asIdeal.inertiaDeg' 𝔓.asIdeal = 2 →
        (P2.liftTraceSeed e (sylowH e)).a v = 0 ∧ iotaZsqrtdNegTwo ((P2.liftTraceSeed e (sylowH e)).b v) =
            -(ψ 𝔓 : ℂ))) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 ↥(fixFld (sylowH e)))), ∀ v ∉ S,
      (P2.liftTraceSeed e (sylowH e)).b v =
          ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℤ√(-2)))
    := by
  obtain ⟨ζ, hζ, hpin⟩ := cubicGlue_exists_zeta
  obtain ⟨𝔣₀, h𝔣₀ne, h𝔣₀⟩ := cubicGlue_exists_modulus L
  refine ⟨↥(fixFld (P2.c8H e)), inferInstance, inferInstance, inferInstance,
    finrank_fixFldSylowH_fixFldC8H e, P2.artinValue e hζ,
    𝔣₀.map (algebraMap (𝓞 ℚ) (𝓞 ↥(fixFld (P2.c8H e)))), ?_, ?_, ?_, ?_, ?_⟩
  · exact (Ideal.map_eq_bot_iff_of_injective (cubicGlue_algebraMap_injective _)).not.mpr h𝔣₀ne
  · intro α hα hα𝔣 hαpos
    exact P2.raySymbol_artinValue_span_eq_one e hζ 𝔣₀ h𝔣₀ α hα hα𝔣 hαpos
  · exact exists_split_place_artinValue_ne e hζ
  · exact liftTraceSeed_sylowH_table_eq_artinValue e hζ hpin
  · exact liftTraceSeed_b_eq_chiNegThree_of_detDictionaryRow e (sylowH e) hdet

end S_LanglandsTunnell_exists_quadratic_rayClassChar_table_liftTraceSeed_sylowH_of_detDictionaryRow
end P2MW
export P2MW.S_LanglandsTunnell_exists_quadratic_rayClassChar_table_liftTraceSeed_sylowH_of_detDictionaryRow (solution)
