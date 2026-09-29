-- Prove2me | solution 1 for M4aHerbrand.exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f07729e0-6a42-5f14-87c9-682bd21891fb

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_RelationModule
import Definitions.Def_GroupCohomology_RelationModuleRes
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Theorems.Thm_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage
import Theorems.Thm_Rep_exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective
import Theorems.Thm_Rep_exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv
import Theorems.Thm_Rep_exists_shapiro_corestriction_map_delta_ind_eq
import Theorems.Thm_Rep_exists_hom_ind_injective_exact_of_forall_rho_eq
import Theorems.Thm_Rep_shortExact_map_indFunctor
import Theorems.Thm_Rep_exists_comp_eq_or_exists_map_delta_ne_zero_of_forall_sum_rho_eq_nsmul
import Theorems.Thm_Rep_relationSeqInt_shortExact
import Theorems.Thm_Rep_exists_hom_relationModuleInt_forall_map_delta_eq
import Theorems.Thm_M4aHerbrand_exists_fundamentalClass_sIdeleClassGroup
import Theorems.Thm_IntermediateField_adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow
import Theorems.Thm_IntermediateField_exists_le_isGalois_dvd_finrank_forall_prod_fixingSubgroup_sClassAct_eq_pow
import Theorems.Thm_NumberField_ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO"
p2m_attr_erase "instance" "ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "Rep.splittingShortComplex_X₃ Rep.splittingShortComplex_X₁ Rep.splittingShortComplex_X₂ Rep.splittingShortComplex_f Rep.augShortComplex_f Rep.augShortComplex_X₃ Rep.cocycleTwist_single Rep.augShortComplex_X₂ Rep.splittingModuleι_hom_apply Rep.augShortComplex_X₁ Rep.splittingShortComplex_g Rep.augShortComplex_g Rep.splittingModuleπ_hom_apply Representation.TateResCor.cosetDecomp_apply Rep.coe_tateHneg1Res_apply Representation.TateResCor.coe_tateHneg1Cores_apply Representation.TateResCor.tateH0Res_mk Rep.coe_tateHneg1Cores_apply Rep.tateH0Res_mk Representation.TateResCor.coe_cosetNormInvariants_apply Rep.tateH0Cores_mk Representation.TateResCor.coinvariantsCores_mk Representation.TateResCor.coinvariantsTransfer_mk Representation.TateResCor.tateH0Cores_mk Representation.TateResCor.coe_tateHneg1Res_apply Rep.coe_dimShiftDownObjMap_apply M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq"
p2m_attr_erase "simp" "FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply"
p2m_attr_erase "simp" "RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply"
p2m_attr_erase "simp" "groupCohomology.Kummer.coe_smul_rootsOfUnity NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory NumberField IsDedekindDomain M4aHerbrand ExtCitation

local instance isAlgebraicQbar_exf : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar_exf : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar_exf : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

namespace Reduce95

section places
local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (p : Nat.Primes) :
    ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.primesEquiv v = p := by
  have h1 : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ (p : ℕ) := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff, ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) (p : ℕ),
      Ideal.apply_mem_of_equiv_iff]
  rw [h1, Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) p.2]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

end places

section hunr

variable (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

theorem asIdeal_eq_span_primesEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v
  have h2 : v.asIdeal = (v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm := by
    rw [Ideal.map_symm, Ideal.comap_map_of_bijective _ (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).bijective]
  rw [h2, ← h, Ideal.map_span, Set.image_singleton, map_natCast]
  rfl

theorem hunr_F (hFS : F.IsUnramifiedOutside S) (w : HeightOneSpectrum (𝓞 ↥F))
    (hw : w ∉ NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes)) :
    Ideal.ramificationIdx' (w.asIdeal.under (𝓞 ℚ)) w.asIdeal = 1 := by
  set v : HeightOneSpectrum (𝓞 ℚ) := w.under (𝓞 ℚ) with hvdef
  set ℓ : Nat.Primes := Rat.HeightOneSpectrum.primesEquiv v with hℓdef
  have hℓv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := (natCast_mem_asIdeal_iff v ℓ).2 rfl
  have hℓw : ((ℓ : ℕ) : 𝓞 ↥F) ∈ w.asIdeal := by
    have : algebraMap (𝓞 ℚ) (𝓞 ↥F) (((ℓ : ℕ) : 𝓞 ℚ)) ∈ w.asIdeal := hℓv
    rwa [map_natCast] at this
  have hℓS : ℓ ∉ S := fun h => hw ((NumberField.mem_placesOverPrimes_iff _ _ _).2 ⟨ℓ, h, hℓw⟩)
  have hHin : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime (ℓ : ℕ) → P.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup :=
    fun P hP => hFS.2 ℓ hℓS P hP
  have h1 := NumberField.ramificationIdx_span_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup F (ℓ : ℕ) ℓ.2 hHin
    w.asIdeal w.isMaximal hℓw
  have hmapZ : (Ideal.span {(((ℓ : ℕ) : ℕ) : ℤ)}).map (algebraMap ℤ (𝓞 ↥F)) = Ideal.span {((ℓ : ℕ) : 𝓞 ↥F)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have hmapQ : (w.asIdeal.under (𝓞 ℚ)).map (algebraMap (𝓞 ℚ) (𝓞 ↥F)) = Ideal.span {((ℓ : ℕ) : 𝓞 ↥F)} := by
    have hv : w.asIdeal.under (𝓞 ℚ) = v.asIdeal := rfl
    rw [hv, asIdeal_eq_span_primesEquiv v, Ideal.map_span, Set.image_singleton, map_natCast]
  unfold Ideal.ramificationIdx' at h1 ⊢
  rw [hmapQ, ← hmapZ]
  exact h1

end hunr

end Reduce95

namespace ReduceEXF
open groupCohomology

section helpers

attribute [local instance 10] AddCommGroup.toIntModule

section general

theorem modsmul_eq_zsmul {M : Type} [AddCommGroup M] (inst : Module ℤ M) (a : ℤ) (x : M) :
    @HSMul.hSMul ℤ M M (@instHSMul ℤ M (@SMulZeroClass.toSMul ℤ M _ (@DistribSMul.toSMulZeroClass ℤ M _
      (@DistribMulAction.toDistribSMul ℤ M _ _ (@Module.toDistribMulAction ℤ M _ _ inst))))) a x =
    @HSMul.hSMul ℤ M M (@instHSMul ℤ M ZSMul.toSMul) a x :=
  int_smul_eq_zsmul inst a x

theorem comp_eq_zero_of_exact {G : Type} [Group G] {X₁ X₂ X₃ : Rep.{0} ℤ G} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hfg : Function.Exact f.hom g.hom) : f ≫ g = 0 := by
  ext x
  change g.hom (f.hom x) = 0
  exact (hfg (f.hom x)).2 ⟨x, rfl⟩

theorem shortExact_of_maps {G : Type} [Group G] {X₁ X₂ X₃ : Rep.{0} ℤ G} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    (ShortComplex.mk f g (comp_eq_zero_of_exact f g hfg)).ShortExact where
  exact := (forget₂ (Rep ℤ G) (ModuleCat ℤ)).reflects_exact_of_faithful _ <|
    (ShortComplex.moduleCat_exact_iff _).2 fun x hx => (hfg x).1 hx
  mono_f := (Rep.mono_iff_injective _).2 hf
  epi_g := (Rep.epi_iff_surjective _).2 hg

theorem isIso_map_of_bijective {G H : Type} [Group G] [Group H] {A : Rep ℤ H} {B : Rep ℤ G}
    (f : G →* H) (hf : Function.Bijective f) (φ : Rep.res f A ⟶ B) [Mono φ] [Epi φ] (n : ℕ) :
    IsIso (groupCohomology.map f φ n) := by
  haveI : ∀ i, IsIso ((groupCohomology.cochainsMap f φ).f i) := fun i => by
    haveI := groupCohomology.cochainsMap_f_map_mono f φ hf.2 i
    haveI := groupCohomology.cochainsMap_f_map_epi f φ hf.1 i
    exact isIso_of_mono_of_epi _
  haveI : IsIso (groupCohomology.cochainsMap f φ) := HomologicalComplex.Hom.isIso_of_components _
  change IsIso ((HomologicalComplex.homologyFunctor _ _ n).map (groupCohomology.cochainsMap f φ))
  infer_instance

theorem map_congr_hom_apply {G H : Type} [Group G] [Group H] {A : Rep ℤ H} {B : Rep ℤ G}
    {f₁ f₂ : G →* H} (h : f₁ = f₂) (φ : Rep.res f₁ A ⟶ B) (ψ : Rep.res f₂ A ⟶ B)
    (hφψ : ∀ x : A, φ.hom x = ψ.hom x) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map f₁ φ n).hom x = (groupCohomology.map f₂ ψ n).hom x := by
  subst h
  obtain rfl : φ = ψ := Rep.hom_ext (DFunLike.ext _ _ hφψ)
  rfl

theorem free_lift {G : Type} [Group G] {α : Type} {X Y : Rep ℤ G} (e : X ⟶ Y) (he : Function.Surjective e.hom)
    (χ : Rep.free ℤ G α ⟶ Y) : ∃ χ' : Rep.free ℤ G α ⟶ X, χ' ≫ e = χ := by
  classical
  choose x hx using fun a : α => he (χ.hom (Finsupp.single a (MonoidAlgebra.single (1 : G) (1 : ℤ))))
  refine ⟨Rep.freeLift ℤ G X x, Rep.free_ext ℤ G Y _ _ fun a => ?_⟩
  rw [← hx a]
  change e.hom ((Rep.freeLift ℤ G X x).hom (Finsupp.single a (MonoidAlgebra.single 1 1))) = e.hom (x a)
  congr 1
  simp [Rep.freeLift]
  first
    | exact one_smul ℤ (x a)
    | exact @one_smul ℤ X.V _ (@DistribMulAction.toMulAction ℤ X.V _ _ (@Module.toDistribMulAction ℤ X.V _ _ X.hV2)) (x a)

theorem ind_free_lift {G : Type} [Group G] (N : Subgroup G) {α : Type} {X Y : Rep ℤ G} (e : X ⟶ Y)
    (he : Function.Surjective e.hom) (χ : (Rep.indFunctor ℤ N.subtype).obj (Rep.free ℤ ↥N α) ⟶ Y) :
    ∃ χ' : (Rep.indFunctor ℤ N.subtype).obj (Rep.free ℤ ↥N α) ⟶ X, χ' ≫ e = χ := by
  let adj := Rep.indResAdjunction ℤ N.subtype
  obtain ⟨χ₀', h⟩ := free_lift ((Rep.resFunctor N.subtype).map e) he ((adj.homEquiv _ _) χ)
  refine ⟨(adj.homEquiv _ _).symm χ₀', (adj.homEquiv _ _).injective ?_⟩
  rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, h]

end general

section resres
variable {G : Type} [Group G] (C : Rep ℤ G) (N : Subgroup G) (S : Subgroup ↥N)

abbrev up : Subgroup G := S.map N.subtype

def upHom : ↥S →* ↥(up N S) :=
  (N.subtype.comp S.subtype).codRestrict (up N S) fun s => ⟨s.1, s.2, rfl⟩

theorem upHom_bijective : Function.Bijective (upHom N S) := by
  constructor
  · intro a b h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  · rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

def upφ : Rep.res (upHom N S) (Rep.res (up N S).subtype C) ⟶ Rep.res S.subtype (Rep.res N.subtype C) :=
  Rep.ofHom ⟨(Rep.Hom.hom (𝟙 (Rep.res S.subtype (Rep.res N.subtype C)))).toLinearMap, fun _ => rfl⟩

scoped instance : Mono (upφ C N S) := (Rep.mono_iff_injective _).2 fun _ _ h => h
scoped instance : Epi (upφ C N S) := (Rep.epi_iff_surjective _).2 fun x => ⟨x, rfl⟩

noncomputable def upIso (n : ℕ) : groupCohomology (Rep.res (up N S).subtype C) n ≅ groupCohomology (Rep.res S.subtype (Rep.res N.subtype C)) n :=
  haveI := isIso_map_of_bijective (upHom N S) (upHom_bijective N S) (upφ C N S) n
  asIso (groupCohomology.map (upHom N S) (upφ C N S) n)

theorem upIso_hom_res (u : groupCohomology C 2) :
    (upIso C N S 2).hom.hom ((map (up N S).subtype (𝟙 (Rep.res (up N S).subtype C)) 2).hom u) =
      (map S.subtype (𝟙 (Rep.res S.subtype (Rep.res N.subtype C))) 2).hom
        ((map N.subtype (𝟙 (Rep.res N.subtype C)) 2).hom u) := by
  change (map (up N S).subtype (𝟙 (Rep.res (up N S).subtype C)) 2 ≫ map (upHom N S) (upφ C N S) 2).hom u =
    (map N.subtype (𝟙 (Rep.res N.subtype C)) 2 ≫ map S.subtype (𝟙 (Rep.res S.subtype (Rep.res N.subtype C))) 2).hom u
  rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
  exact map_congr_hom_apply (f₁ := (up N S).subtype.comp (upHom N S)) (f₂ := N.subtype.comp S.subtype)
    (MonoidHom.ext fun _ => rfl) ((Rep.resFunctor (upHom N S)).map (𝟙 (Rep.res (up N S).subtype C)) ≫ upφ C N S)
    ((Rep.resFunctor S.subtype).map (𝟙 (Rep.res N.subtype C)) ≫ 𝟙 (Rep.res S.subtype (Rep.res N.subtype C))) (fun _ => rfl) 2 u

theorem classModule_res (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤) :
    (∀ S : Subgroup ↥N, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.res N.subtype C)) 1)) ∧
    (∀ (S : Subgroup ↥N) [Fintype S],
      Nat.card (groupCohomology (Rep.res S.subtype (Rep.res N.subtype C)) 2) = Fintype.card S) ∧
    (∀ S : Subgroup ↥N, Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.res N.subtype C))) 2).hom
      ((groupCohomology.map N.subtype (𝟙 (Rep.res N.subtype C)) 2).hom u)} = ⊤) := by
  refine ⟨fun S => ?_, fun S _ => ?_, fun S => ?_⟩
  · exact Limits.IsZero.of_iso (h1 (up N S)) (upIso C N S 1).symm
  · letI : Fintype ↥(up N S) := Fintype.ofBijective _ (upHom_bijective N S)
    rw [Fintype.card_of_bijective (upHom_bijective N S), ← h2card (up N S)]
    exact Nat.card_congr (upIso C N S 2).toLinearEquiv.toEquiv.symm
  · set e := (upIso C N S 2).toLinearEquiv with he
    have key : (map S.subtype (𝟙 (Rep.res S.subtype (Rep.res N.subtype C))) 2).hom
        ((map N.subtype (𝟙 (Rep.res N.subtype C)) 2).hom u) = e ((map (up N S).subtype (𝟙 (Rep.res (up N S).subtype C)) 2).hom u) :=
      (upIso_hom_res C N S u).symm
    rw [key, Submodule.eq_top_iff']
    intro y
    have hy : e.symm y ∈ Submodule.span ℤ {(map (up N S).subtype (𝟙 (Rep.res (up N S).subtype C)) 2).hom u} := by
      rw [h2gen (up N S)]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hy
    refine Submodule.mem_span_singleton.2 ⟨a, ?_⟩
    rw [← LinearEquiv.map_smul, ha, LinearEquiv.apply_symm_apply]

theorem isIso_map_top (n : ℕ) :
    IsIso (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype C)) n) :=
  isIso_map_of_bijective _ ⟨Subtype.val_injective, fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩⟩ _ n

theorem card_H2_eq [Fintype G]
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S) :
    Nat.card (groupCohomology C 2) = Fintype.card G := by
  classical
  haveI := isIso_map_top C 2
  rw [Nat.card_congr (asIso (groupCohomology.map (⊤ : Subgroup G).subtype
    (𝟙 (Rep.res (⊤ : Subgroup G).subtype C)) 2)).toLinearEquiv.toEquiv, h2card ⊤]
  exact Fintype.card_congr Subgroup.topEquiv.toEquiv

theorem span_eq_top (u : groupCohomology C 2)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤) :
    Submodule.span ℤ {u} = ⊤ := by
  haveI := isIso_map_top C 2
  let e := (asIso (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype C)) 2)).toLinearEquiv
  rw [Submodule.eq_top_iff']
  intro y
  have hy : e y ∈ Submodule.span ℤ {e u} := by
    change e y ∈ Submodule.span ℤ {(map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype C)) 2).hom u}
    rw [h2gen ⊤]; trivial
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hy
  rw [← LinearEquiv.map_smul] at ha
  exact Submodule.mem_span_singleton.2 ⟨a, e.injective ha⟩

end resres

theorem cor_injective {G : Type} [Group G] [Fintype G] (C : Rep ℤ G) (u : groupCohomology C 2)
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (N : Subgroup G) [Fintype ↥N]
    (cor : groupCohomology (Rep.res N.subtype C) 2 →+ groupCohomology C 2)
    (hcor : ∀ x : groupCohomology C 2,
      cor ((groupCohomology.map N.subtype (𝟙 (Rep.res N.subtype C)) 2).hom x) = N.index • x) :
    Function.Injective cor := by
  classical
  set r := (groupCohomology.map N.subtype (𝟙 (Rep.res N.subtype C)) 2).hom with hr
  have hcardG : Nat.card (groupCohomology C 2) = Fintype.card G := card_H2_eq C h2card
  have hspanG : Submodule.span ℤ {u} = ⊤ := span_eq_top C u h2gen
  have hzm : AddSubgroup.zmultiples u = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (show y ∈ Submodule.span ℤ {u} by rw [hspanG]; trivial)
    rw [modsmul_eq_zsmul] at ha
    exact ⟨a, ha⟩
  have horder : addOrderOf u = Fintype.card G := by
    rw [← hcardG, ← Nat.card_zmultiples u, hzm, AddSubgroup.card_top]
  have hidx : Fintype.card ↥N * N.index = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact Subgroup.card_mul_index N
  have hidx0 : N.index ≠ 0 := fun h => by
    have := hidx; rw [h, mul_zero] at this; exact Fintype.card_ne_zero this.symm
  have hkill : ∀ x : groupCohomology (Rep.res N.subtype C) 2, (Fintype.card ↥N : ℤ) • x = 0 := fun x => by
    rw [← h2card N, natCast_zsmul]; exact card_nsmul_eq_zero'
  refine (injective_iff_map_eq_zero cor).2 fun z hz => ?_
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.1 (show z ∈ Submodule.span ℤ {r u} by rw [h2gen N]; trivial)
  rw [modsmul_eq_zsmul] at hk
  subst hk
  have h1 : cor (k • r u) = k • (N.index • u) := by rw [map_zsmul cor k, hcor u]
  rw [h1, ← natCast_zsmul, smul_smul, ← addOrderOf_dvd_iff_zsmul_eq_zero, horder, ← hidx] at hz
  push_cast at hz
  obtain ⟨m, rfl⟩ := (mul_dvd_mul_iff_right (by exact_mod_cast hidx0)).1 hz
  rw [mul_comm, ← smul_smul, hkill, zsmul_zero]

end helpers

set_option maxHeartbeats 6400000 in
theorem core {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (C : Rep ℤ G) (u : groupCohomology C 2)
    (h1 : ∀ (S : Subgroup G), CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : ∀ (S : Subgroup G),
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2).hom u} = ⊤)
    (p : ℕ) [Fact p.Prime] (N : Subgroup G) [N.Normal] [Fintype ↥N] (hpN : p ∣ Nat.card ↥N)
    (hnorm : ∀ c : C, ∃ d : C, (∀ g : ↥N, C.ρ g d = d) ∧ (∑ g : ↥N, C.ρ g c) = p • d)
    (B : Rep ℤ G) [Fintype B] (hB : ∀ b : B, p • b = 0) (hNB : ∀ g ∈ N, ∀ b : B, B.ρ g b = b)
    (hX : (Rep.relationSeqInt B).ShortExact) (φ : Rep.relationModuleInt B ⟶ C) :
    (∃ χ : Rep.free ℤ G B ⟶ C, Rep.relationModuleInt.ι B ≫ χ = φ) ∨
    (∃ y : groupCohomology B 1,
      (groupCohomology.map (MonoidHom.id G) φ 2).hom ((groupCohomology.δ hX 1 2 rfl).hom y) ≠ 0) := by
  classical

  obtain ⟨ι, B₁, instB₁, ρ, hinj, hexact, hsurjρ, hB₁, hNB₁, -⟩ :=
    Rep.exists_hom_ind_injective_exact_of_forall_rho_eq N B p hB hNB
  have hSB := shortExact_of_maps ι ρ hinj hexact hsurjρ

  obtain ⟨h1N, h2cardN, h2genN⟩ := classModule_res C N u h1 h2card h2gen

  haveI : Fintype (Rep.res N.subtype B) := inferInstanceAs (Fintype B)
  have hX₀ := Rep.relationSeqInt_shortExact (Rep.res N.subtype B)
  have hT_I := Rep.shortExact_map_indFunctor N hX₀
  have hT₁ := Rep.relationSeqInt_shortExact B₁

  have hP_B : ∀ (X Y : Rep ℤ G) (e : X ⟶ Y), Function.Surjective e.hom →
      ∀ χ : Rep.free ℤ G B ⟶ Y, ∃ χ' : Rep.free ℤ G B ⟶ X, χ' ≫ e = χ :=
    fun X Y e he χ => free_lift e he χ
  have hP_I : ∀ (X Y : Rep ℤ G) (e : X ⟶ Y), Function.Surjective e.hom →
      ∀ χ : (Rep.indFunctor ℤ N.subtype).obj (Rep.free ℤ ↥N (Rep.res N.subtype B)) ⟶ Y,
        ∃ χ' : (Rep.indFunctor ℤ N.subtype).obj (Rep.free ℤ ↥N (Rep.res N.subtype B)) ⟶ X, χ' ≫ e = χ :=
    fun X Y e he χ => ind_free_lift N e he χ

  have hgI : Function.Surjective ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).g.hom :=
    (Rep.epi_iff_surjective _).1 hT_I.epi_g
  obtain ⟨ιP, hιP⟩ := hP_B _ _ _ hgI (Rep.freeCover B ≫ ι)
  haveI := hT_I.mono_f
  have hιR0 : (Rep.relationModuleInt.ι B ≫ ιP) ≫ ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).g = 0 :=
    calc (Rep.relationModuleInt.ι B ≫ ιP) ≫ ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).g
        = Rep.relationModuleInt.ι B ≫ (ιP ≫ ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).g) := Category.assoc _ _ _
      _ = Rep.relationModuleInt.ι B ≫ (Rep.freeCover B ≫ ι) := congrArg (fun t => Rep.relationModuleInt.ι B ≫ t) hιP
      _ = 0 := by rw [← Category.assoc, Rep.relationModuleInt_ι_comp_freeCover, Limits.zero_comp]
  have sq₁ : Rep.relationModuleInt.ι B ≫ ιP = hT_I.exact.lift _ hιR0 ≫ ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).f :=
    (hT_I.exact.lift_f _ hιR0).symm
  have sq₂ : Rep.freeCover B ≫ ι = ιP ≫ ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).g := hιP.symm

  have hg₁ : Function.Surjective (Rep.freeCover B₁).hom := (Rep.epi_iff_surjective _).1 hT₁.epi_g
  obtain ⟨ρP, hρP⟩ := hP_I _ _ _ hg₁ (((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).g ≫ ρ)
  haveI := hT₁.mono_f
  have hρR0 : (((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).f ≫ ρP) ≫ Rep.freeCover B₁ = 0 :=
    calc (((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).f ≫ ρP) ≫ Rep.freeCover B₁
        = ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).f ≫ (ρP ≫ Rep.freeCover B₁) := Category.assoc _ _ _
      _ = ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).f ≫
            (((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).g ≫ ρ) := congrArg (fun t => _ ≫ t) hρP
      _ = 0 := by rw [← Category.assoc, ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).zero, Limits.zero_comp]
  have sq₃ : ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).f ≫ ρP =
      hT₁.exact.lift _ hρR0 ≫ Rep.relationModuleInt.ι B₁ := (hT₁.exact.lift_f _ hρR0).symm
  have sq₄ : ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).g ≫ ρ = ρP ≫ Rep.freeCover B₁ := hρP.symm

  have hker := fun φ' hφ' => Rep.exists_eq_comp_add_comp_of_forall_map_delta_eq_zero_of_shortExact_of_projective
      C u h1 h2card h2gen p hSB hB₁ N hpN hNB₁ (Rep.relationModuleInt.ι B) (Rep.freeCover B)
      (Rep.relationModuleInt_ι_comp_freeCover B) hX hP_B
      ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).f
      ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).g
      ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).zero hT_I hP_I
      (hT_I.exact.lift _ hιR0) ιP sq₁ sq₂ φ' hφ'
  have hsurj := fun θ => Rep.exists_hom_relationModuleInt_forall_map_delta_eq C u h1 h2card h2gen B₁ hT₁ θ

  have htriv : ∀ (g : ↥N) (b : Rep.res N.subtype B), (Rep.res N.subtype B).ρ g b = b := fun g b => hNB g g.2 b
  have hmid : ∀ ψ : ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).X₁ ⟶ C,
      (∃ χ : ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).X₂ ⟶ C,
        ψ = ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).f ≫ χ) ∨
      (∃ y : groupCohomology ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).X₃ 1,
        (groupCohomology.map (MonoidHom.id G) ψ 2).hom ((groupCohomology.δ hT_I 1 2 rfl).hom y) ≠ 0) := by
    intro ψ
    rcases Rep.exists_comp_eq_or_exists_map_delta_ne_zero_of_forall_sum_rho_eq_nsmul (Rep.res N.subtype C)
        ((groupCohomology.map N.subtype (𝟙 (Rep.res N.subtype C)) 2).hom u) h1N h2cardN h2genN p hnorm
        (Rep.res N.subtype B) hB htriv hX₀ ((Rep.indResAdjunction ℤ N.subtype).homEquiv _ _ ψ) with ⟨χ₀, hχ₀⟩ | ⟨y₀, hy₀⟩
    · left
      obtain ⟨χ, hχ⟩ := (Rep.exists_ind_map_comp_eq_iff_exists_comp_eq_homEquiv N
        (Rep.relationModuleInt.ι (Rep.res N.subtype B)) C ψ).2 ⟨χ₀, hχ₀⟩
      exact ⟨χ, hχ.symm⟩
    · right
      obtain ⟨Sh, cor, hcor, hSh⟩ := Rep.exists_shapiro_corestriction_map_delta_ind_eq N hX₀ hT_I C
      refine ⟨Sh y₀, ?_⟩
      rw [hSh ψ y₀]
      exact fun h => hy₀ (cor_injective C u h2card h2gen N cor hcor (h.trans (map_zero cor).symm))

  rcases Rep.exists_comp_eq_or_exists_map_delta_ne_zero_of_devissage C p hSB hB₁
      (Rep.relationModuleInt.ι B) (Rep.freeCover B) (Rep.relationModuleInt_ι_comp_freeCover B) hX
      ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).f
      ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).g
      ((Rep.relationSeqInt (Rep.res N.subtype B)).map (Rep.indFunctor ℤ N.subtype)).zero hT_I
      (Rep.relationModuleInt.ι B₁) (Rep.freeCover B₁) (Rep.relationModuleInt_ι_comp_freeCover B₁) hT₁
      (hT_I.exact.lift _ hιR0) ιP sq₁ sq₂ (hT₁.exact.lift _ hρR0) ρP sq₃ sq₄ hker hmid hsurj φ with ⟨χ, hχ⟩ | ⟨y, hy⟩
  · exact Or.inl ⟨χ, hχ.symm⟩
  · exact Or.inr ⟨y, hy⟩

end ReduceEXF
p2m_reactivate "P2MW.S_M4aHerbrand_exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero.ReduceEXF"

set_option maxHeartbeats 3200000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] [IsGalois ℚ ↥L] (hL : L.IsUnramifiedOutside S)
    (D : IdeleGaloisDescent (𝓞 ↥L) ℚ ↥L) (hD : D.StabilizesUnitIdeles (NumberField.placesOverPrimes ↥L (↑S : Set Nat.Primes)))
    [MulDistribMulAction (↥L ≃ₐ[ℚ] ↥L) (SIdeleClassGroup (𝓞 ↥L) ↥L (NumberField.placesOverPrimes ↥L (↑S : Set Nat.Primes)))]
    (hact : ∀ (g : ↥L ≃ₐ[ℚ] ↥L) (c : SIdeleClassGroup (𝓞 ↥L) ↥L (NumberField.placesOverPrimes ↥L (↑S : Set Nat.Primes))),
      g • c = D.sClassAct hD g c)
    (B : Rep ℤ (↥L ≃ₐ[ℚ] ↥L)) [Fintype B] (hB : ∀ b : B, p • b = 0) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : L ≤ F) (_ : NumberField ↥F) (_ : IsGalois ℚ ↥F),
      F.IsUnramifiedOutside S ∧
      ∀ (π : (↥F ≃ₐ[ℚ] ↥F) →* (↥L ≃ₐ[ℚ] ↥L))
        (_ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          π (AlgEquiv.restrictNormalHom ↥F σ) = AlgEquiv.restrictNormalHom ↥L σ)
        (D' : IdeleGaloisDescent (𝓞 ↥F) ℚ ↥F) (hD' : D'.StabilizesUnitIdeles (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes)))
        [MulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes)))]
        (_ : ∀ (g : ↥F ≃ₐ[ℚ] ↥F) (c : SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes))),
          g • c = D'.sClassAct hD' g c)
        (j : Rep.res π (Rep.ofMulDistribMulAction (↥L ≃ₐ[ℚ] ↥L)
              (SIdeleClassGroup (𝓞 ↥L) ↥L (NumberField.placesOverPrimes ↥L (↑S : Set Nat.Primes)))) ⟶
            Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F)
              (SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes))))
        (hX : (Rep.relationSeqInt (Rep.res π B)).ShortExact)
        (φ : Rep.relationModuleInt B ⟶ Rep.ofMulDistribMulAction (↥L ≃ₐ[ℚ] ↥L)
              (SIdeleClassGroup (𝓞 ↥L) ↥L (NumberField.placesOverPrimes ↥L (↑S : Set Nat.Primes)))),
        (∃ χ : Rep.free ℤ (↥F ≃ₐ[ℚ] ↥F) (Rep.res π B) ⟶ Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F)
              (SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes))),
            Rep.relationModuleInt.ι (Rep.res π B) ≫ χ =
              Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map φ ≫ j) ∨
        (∃ y : groupCohomology (Rep.res π B) 1,
            (groupCohomology.map (MonoidHom.id (↥F ≃ₐ[ℚ] ↥F))
                (Rep.relationModuleInt.resMap π B ≫ (Rep.resFunctor π).map φ ≫ j) 2).hom
              ((groupCohomology.δ hX 1 2 rfl).hom y) ≠ 0) := by
  classical

  have hp : (p : ℕ).Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero ((p : ℕ) : AlgebraicClosure ℚ) := NeZero.charZero
  obtain ⟨ζ0, hζ0⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ p := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p (AlgebraicClosure ℚ))
      (Polynomial.degree_cyclotomic_pos p _ hp.pos).ne'
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.1 hz⟩
  let K : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {ζ0}
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := L ⊔ K
  have hK : K.IsUnramifiedOutside S :=
    IntermediateField.adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow S hpS 0 ζ0 (by simpa using hζ0)
  have hL'S : L'.IsUnramifiedOutside S := hL.sup hK
  haveI : FiniteDimensional ℚ ↥L' := hL'S.1
  haveI : NumberField ↥L' := NumberField.mk
  haveI : Algebra.IsIntegral ℚ (AlgebraicClosure ℚ) :=
    ⟨fun x => ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral⟩
  haveI : IsCyclotomicExtension {p} ℚ ↥K := hζ0.intermediateField_adjoin_isCyclotomicExtension ℚ
  haveI : IsGalois ℚ ↥K := IsCyclotomicExtension.isGalois {p} ℚ ↥K
  haveI : Normal ℚ ↥L' := @IntermediateField.normal_sup ℚ (AlgebraicClosure ℚ) _ _ _ L K
    (@IsGalois.to_normal _ _ _ _ _ ‹IsGalois ℚ ↥L›) (@IsGalois.to_normal _ _ _ _ _ ‹IsGalois ℚ ↥K›)
  haveI : IsGalois ℚ ↥L' := IsGalois.mk
  have hζmem : ζ0 ∈ L' := (le_sup_right : K ≤ L ⊔ K) (IntermediateField.mem_adjoin_simple_self ℚ ζ0)
  have hζ' : IsPrimitiveRoot (⟨ζ0, hζmem⟩ : ↥L') p := IsPrimitiveRoot.coe_submonoidClass_iff.1 hζ0

  obtain ⟨F, hL'F, instNF, instGF, hFS, hpdvd, hW⟩ :=
    IntermediateField.exists_le_isGalois_dvd_finrank_forall_prod_fixingSubgroup_sClassAct_eq_pow S hpS L' hL'S ⟨ζ0, hζmem⟩ hζ'
  refine ⟨F, le_sup_left.trans hL'F, instNF, instGF, hFS, ?_⟩
  intro π hπ D' hD' _inst hact' j hX φ

  let M : IntermediateField ℚ ↥F := (IntermediateField.inclusion hL'F).fieldRange
  let N : Subgroup (↥F ≃ₐ[ℚ] ↥F) := M.fixingSubgroup
  let eM : ↥L' ≃ₐ[ℚ] ↥M := AlgEquiv.ofInjectiveField (IntermediateField.inclusion hL'F)
  haveI : IsGalois ℚ ↥M := IsGalois.of_algEquiv eM
  haveI hNn : N.Normal := @IsGalois.fixingSubgroup_normal_of_isGalois ℚ ↥F _ _ _ M instGF ‹IsGalois ℚ ↥M›
  have hpN : p ∣ Nat.card ↥N := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank M]
    have h1 := Module.finrank_mul_finrank ℚ ↥M ↥F
    have h2 := Module.finrank_mul_finrank ℚ ↥L' ↥(IntermediateField.extendScalars hL'F)
    have h3 : Module.finrank ℚ ↥(IntermediateField.extendScalars hL'F) = Module.finrank ℚ ↥F :=
      LinearEquiv.finrank_eq
        { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩, map_add' := fun _ _ => rfl,
          map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    have h4 : Module.finrank ℚ ↥L' = Module.finrank ℚ ↥M := eM.toLinearEquiv.finrank_eq
    have h5 : Module.finrank ↥M ↥F = Module.finrank ↥L' ↥(IntermediateField.extendScalars hL'F) := by
      apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := ℚ) (M := ↥L'))
      rw [h2, h3, h4, h1]
    rw [h5]; exact hpdvd
  have hNπ : ∀ g ∈ N, π g = 1 := by
    intro g hg
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ) g
    rw [hπ σ]
    ext x
    have hx' : (x : AlgebraicClosure ℚ) ∈ L' := (le_sup_left : L ≤ L ⊔ K) x.2
    have h1 : (algebraMap ↥L (AlgebraicClosure ℚ)) (AlgEquiv.restrictNormalHom ↥L σ x) = σ x :=
      AlgEquiv.restrictNormal_commutes σ ↥L x
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg (IntermediateField.inclusion hL'F ⟨x, hx'⟩) ⟨⟨x, hx'⟩, rfl⟩
    have h2 : (algebraMap ↥F (AlgebraicClosure ℚ)) (AlgEquiv.restrictNormalHom ↥F σ (IntermediateField.inclusion hL'F ⟨x, hx'⟩)) =
        σ (IntermediateField.inclusion hL'F ⟨x, hx'⟩ : ↥F) :=
      AlgEquiv.restrictNormal_commutes σ ↥F _
    rw [hfix] at h2
    change (algebraMap ↥L (AlgebraicClosure ℚ)) (AlgEquiv.restrictNormalHom ↥L σ x) = ((1 : ↥L ≃ₐ[ℚ] ↥L) x : AlgebraicClosure ℚ)
    rw [h1, AlgEquiv.one_apply]
    exact h2.symm
  have hNB : ∀ g ∈ N, ∀ b : (Rep.res π B), (Rep.res π B).ρ g b = b := by
    intro g hg b
    change B.ρ (π g) b = b
    rw [hNπ g hg, map_one]; rfl

  letI := D'.classMulDistribMulAction
  obtain ⟨u, h1, h2card, h2gen⟩ := M4aHerbrand.exists_fundamentalClass_sIdeleClassGroup ℚ ↥F D'
    (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes)) (Reduce95.hunr_F S F hFS) hD'
    (fun _ _ => rfl) (fun g c => by rw [hact', IdeleGaloisDescent.sClassAct_toSIdeleClass])

  have hnorm : ∀ c : Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes))),
      ∃ d : Rep.ofMulDistribMulAction (↥F ≃ₐ[ℚ] ↥F) (SIdeleClassGroup (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes))),
        (∀ g : ↥N, (Rep.ofMulDistribMulAction _ _).ρ g d = d) ∧ (∑ g : ↥N, (Rep.ofMulDistribMulAction _ _).ρ g c) = p • d := by
    intro c
    obtain ⟨d, hd1, hd2⟩ := hW D' hD' (Additive.toMul c)
    refine ⟨Additive.ofMul d, fun g => ?_, ?_⟩
    · rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Subgroup.smul_def, hact']
      exact congrArg Additive.ofMul (hd1 g.1 g.2)
    · calc (∑ g : ↥N, (Rep.ofMulDistribMulAction _ _).ρ g c)
          = ∑ g : ↥N, Additive.ofMul (D'.sClassAct hD' g.1 (Additive.toMul c)) :=
            Finset.sum_congr rfl (fun g _ => by rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Subgroup.smul_def, hact'])
        _ = Additive.ofMul (∏ g : ↥N, D'.sClassAct hD' g.1 (Additive.toMul c)) := (ofMul_prod _ _).symm
        _ = Additive.ofMul (d ^ p) := congrArg Additive.ofMul (by
            rw [← hd2]; exact Finset.prod_congr (Finset.ext fun g => ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩) fun _ _ => rfl)
        _ = p • Additive.ofMul d := ofMul_pow _ _

  haveI : Fintype (Rep.res π B) := inferInstanceAs (Fintype B)
  exact ReduceEXF.core _ u h1 h2card h2gen p N hpN hnorm (Rep.res π B) hB hNB hX _

end S_M4aHerbrand_exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero
end P2MW
export P2MW.S_M4aHerbrand_exists_level_forall_relationHom_sIdeleClassGroup_extends_or_map_delta_ne_zero (solution)
