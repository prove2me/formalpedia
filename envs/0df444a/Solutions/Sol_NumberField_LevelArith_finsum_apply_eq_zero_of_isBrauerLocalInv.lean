-- Prove2me | solution 1 for NumberField.LevelArith.finsum_apply_eq_zero_of_isBrauerLocalInv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3376489a-bdb3-5521-998a-02df1f3df82e

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantChar
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_NumberField_LevelArith_exists_layer_presentation_and_pow_smul_eq_zero
import Theorems.Thm_NumberField_LevelArith_map_prG_map_principalIdele_eq_zero_of_forall_comap_ne
import Theorems.Thm_groupCohomology_exists_continuousH2SrInflation_eq_of_nsmul_eq_zero
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Theorems.Thm_groupCohomology_continuousH2SrInflation_H2pi_eq_of_le
import Theorems.Thm_NumberField_LevelArith_exists_monoidHom_levelGal_exists_hom_res_quotientToInvariants_sUnitsRep_bijective
import Theorems.Thm_M4aHerbrand_nonempty_ideleGaloisDescent
import Theorems.Thm_NumberField_IdeleLocalInv_exists_hasLocalInv
import Theorems.Thm_NumberField_IdeleLocalInv_eq_of_hasLocalInv
import Theorems.Thm_M4aHerbrand_map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero
import Theorems.Thm_NumberField_PlaceDecomp_exists_forall_isLocalFundamentalClass_above
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_NumberField_PlaceDecomp_exists_eq_zsmul_map_of_isLocalFundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct
import Theorems.Thm_NumberField_LevelArith_ramificationIdx_eq_one_of_isUnramifiedOutside_of_under_not_mem_placesOverPrimesFinset
import Theorems.Thm_ExtCitation_LocalLevel_isSolvable_of_faithfulSMul_of_padic
import Theorems.Thm_NumberField_PlaceDecomp_mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
import Theorems.Thm_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_of_sq_eq_neg_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_finsum_apply_eq_zero_of_isBrauerLocalInv
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "instance" "NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq"
p2m_attr_erase "simp" "AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith P2MW.S_NumberField_LevelArith_finsum_apply_eq_zero_of_isBrauerLocalInv.NumberField.LevelArith"
p2m_open_scoped "Classical NumberField.LevelArith P2MW.S_NumberField_LevelArith_finsum_apply_eq_zero_of_isBrauerLocalInv.NumberField.LevelArith TensorProduct Pointwise"
p2m_open_scoped "NumberField P2MW.S_NumberField_LevelArith_finsum_apply_eq_zero_of_isBrauerLocalInv.NumberField NumberField.PlaceDecomp NumberField.InfPlaceDecomp"
open M4aHerbrand IsDedekindDomain

namespace NumberField
p2m_export "NumberField" "mk place InfinitePlace AdeleRing SUnits.loc SUnits.smul_loc PlaceAbove.above PlaceAbove.comap_above PlaceDecomp.decomp IdeleLocalInv.HasLocalInv placesOverPrimes InfPlaceDecomp.decomp LevelArith.exists_layer_presentation_and_pow_smul_eq_zero LevelArith.map_prG_map_principalIdele_eq_zero_of_forall_comap_ne PlaceDecomp.exists_forall_isLocalFundamentalClass_above PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv InfPlaceDecomp.eq_one_of_mem_decomp_of_sq_eq_neg_one"
namespace LevelArith
p2m_export "NumberField.LevelArith" "levelField placesOverPrimes placesOverPrimesFinset mem_placesOverPrimesFinset sUnitsMaxRep IsBrauerLocalInv exists_layer_presentation_and_pow_smul_eq_zero map_prG_map_principalIdele_eq_zero_of_forall_comap_ne"
namespace C3
p2m_open "NumberField.LevelArith NumberField"

universe u

theorem map_comp_id_apply {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]
    {A : Rep k H} {B C : Rep k G} (f : G →* H) (φ : Rep.res f A ⟶ B) (ψ : B ⟶ C) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map f (φ ≫ ψ) n) x = (groupCohomology.map (MonoidHom.id G) ψ n).hom ((groupCohomology.map f φ n) x) := by
  rw [show groupCohomology.map f (φ ≫ ψ) n = groupCohomology.map f φ n ≫ groupCohomology.map (MonoidHom.id G) ψ n from
    groupCohomology.map_comp f (MonoidHom.id G) φ ψ n]
  rfl

theorem map_id_zero {k G : Type u} [CommRing k] [Group G] {B C : Rep k G} (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) (0 : B ⟶ C) n = 0 := by
  rw [← groupCohomology.functor_map, Functor.map_zero]; rfl

theorem finsum_set_coe_eq_finsum_of_forall {α M : Type*} [AddCommMonoid M] (s : Set α) (g : α → M)
    (h : ∀ a, a ∉ s → g a = 0) : ∑ᶠ a : s, g a = ∑ᶠ a, g a := by
  rw [finsum_set_coe_eq_finsum_mem, finsum_mem_def, Set.indicator_eq_self.2]
  intro a ha
  by_contra has
  exact ha (h a has)

theorem coe_div_eq_zero_of_dvd (n : ℤ) (N : ℕ) (hN : N ≠ 0) (h : (N : ℤ) ∣ n) :
    ((((n : ℚ) / (N : ℚ) : ℚ)) : AddCircle (1 : ℚ)) = 0 := by
  obtain ⟨m, rfl⟩ := h
  have hq : (((N : ℤ) * m : ℤ) : ℚ) / (N : ℚ) = (m : ℚ) := by
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
    push_cast
    field_simp
  rw [hq, AddCircle.coe_eq_zero_iff]
  exact ⟨m, by rw [zsmul_one]⟩

theorem faithfulSMul_decomp_above (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
    (v : HeightOneSpectrum (𝓞 E)) :
    FaithfulSMul ↥(NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v))
      ((NumberField.PlaceAbove.above E K v).adicCompletion K) :=
  ⟨fun {σ τ} h => by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro x
    have hx := h (NumberField.SUnits.loc E K v x)
    rw [NumberField.SUnits.smul_loc, NumberField.SUnits.smul_loc] at hx
    exact (NumberField.SUnits.loc E K v).injective hx⟩

theorem faithfulSMul_of_equiv {G A B : Type*} [SMul G A] [SMul G B] [FaithfulSMul G A] (Φ : A ≃ B)
    (h : ∀ (g : G) (a : A), Φ (g • a) = g • Φ a) : FaithfulSMul G B :=
  ⟨fun {g₁ g₂} hg => FaithfulSMul.eq_of_smul_eq_smul fun a => Φ.injective (by rw [h, h, hg])⟩

end NumberField.LevelArith.C3

set_option maxHeartbeats 25600000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (inv : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))
        →ₗ[ℤ] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ)))
    (hinv : IsBrauerLocalInv p S L inv) (a : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))) :
    ∑ᶠ v, inv a v = 0 := by
  have _ := hpS

  obtain ⟨F, hLF, hFfd, hFn, hGalF, hF, ι, hι, φ, hbij, hval, D, instI, hactI, j, hj, f, k, ha, hfk⟩ :=
    NumberField.LevelArith.exists_layer_presentation_and_pow_smul_eq_zero S L hL a
  haveI := hFfd; haveI := hFn; haveI := hGalF; letI := instI

  obtain ⟨X, hXdef⟩ : ∃ X, X = (groupCohomology.map ι (φ ≫ j) 2) (H2π _ f) := ⟨_, rfl⟩
  obtain ⟨yS, hySdef⟩ : ∃ yS, yS = (groupCohomology.map ι φ 2) (H2π _ f) := ⟨_, rfl⟩
  have hXy : X = (groupCohomology.map (MonoidHom.id _) j 2).hom yS := by
    rw [hXdef, hySdef]
    exact NumberField.LevelArith.C3.map_comp_id_apply ι φ j 2 (H2π _ f)
  have hXk : (p ^ k : ℤ) • X = 0 := by
    have hX' : X = (groupCohomology.map ι (φ ≫ j) 2).hom (H2π _ f) := hXdef
    rw [hX', ← map_zsmul, hfk, map_zero]

  have hinv_eq : ∀ (v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes))) (t : AddCircle (1 : ℚ)),
      NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI X v.1 t → inv a v = t :=
    fun v t ht => hinv F hLF hF ι hι φ hbij hval D hactI j hj f a ha v t (hXdef ▸ ht)

  obtain ⟨q, hq, L', hL'fd, instMS, instMD, Φ, hΦ1, hΦ2, hΦ3, K₀, hK₀fd, hbase, θ, hθ, u', hu'⟩ :=
    NumberField.PlaceDecomp.exists_forall_isLocalFundamentalClass_above ↥L ↥(levelField L F hLF)

  obtain ⟨prG, hprG⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply ↥L ↥(levelField L F hLF) D hactI

  obtain ⟨instC, hact⟩ := M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct ↥L ↥(levelField L F hLF) D
  letI := instC
  have hequiv : ∀ (g : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (z : (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ),
      QuotientGroup.mk' (principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (g • z) =
        g • QuotientGroup.mk' (principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) z := by
    intro g z
    rw [hactI, hact]
    rfl
  let π : Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (NumberField.AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ ⟶
      Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) :=
    M4aHerbrand.repHomOfMulEquivariant (QuotientGroup.mk' (principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))) hequiv
  have hπv : ∀ z, π.hom (Additive.ofMul z) = Additive.ofMul (QuotientGroup.mk z : IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) :=
    fun z => rfl

  have hjπ : j ≫ π = 0 := by
    ext y
    change π.hom (j.hom y) = 0
    have hy := hj y
    have h1 : (QuotientGroup.mk' (principalIdeles (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (Additive.toMul (j.hom y)) :
        IdeleClassGroup (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ⟨_, hy.symm⟩
    exact congrArg Additive.ofMul h1
  have hπX : (groupCohomology.map (MonoidHom.id _) π 2).hom X = 0 := by
    rw [hXy, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← groupCohomology.map_id_comp, hjπ,
      NumberField.LevelArith.C3.map_id_zero]
    rfl

  have hsolv : ∀ v : HeightOneSpectrum (𝓞 ↥L), Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) := by
    intro v
    haveI := hq v; haveI := hL'fd v; letI := instMS v
    haveI := NumberField.LevelArith.C3.faithfulSMul_decomp_above ↥L ↥(levelField L F hLF) v
    haveI : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) ↥(L' v) :=
      NumberField.LevelArith.C3.faithfulSMul_of_equiv (Φ v).toEquiv (hΦ3 v)
    exact ExtCitation.LocalLevel.isSolvable_of_faithfulSMul_of_padic (q v) (L' v) _ (hΦ1 v)

  have hn : ∃ n : HeightOneSpectrum (𝓞 ↥L) → ℤ, ∀ v,
      (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).subtype
          (prG (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) 2).hom X =
        n v • (groupCohomology.map (MonoidHom.id _) (θ v) 2).hom (u' v) := by
    have key : ∀ v : HeightOneSpectrum (𝓞 ↥L), ∃ m : ℤ,
        (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).subtype
            (prG (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) 2).hom X =
          m • (groupCohomology.map (MonoidHom.id _) (θ v) 2).hom (u' v) := fun v => by
      haveI := hq v; haveI := hL'fd v; letI := instMS v; letI := instMD v; haveI := hK₀fd v
      exact NumberField.PlaceDecomp.exists_eq_zsmul_map_of_isLocalFundamentalClass ↥L ↥(levelField L F hLF)
        (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v) (hsolv v) (q v) (L' v) (Φ v) (hΦ1 v) (hΦ2 v) (hΦ3 v) (K₀ v) (hbase v)
        (θ v) (hθ v) (u' v) (hu' v) _
    choose n hn using key
    exact ⟨n, hn⟩
  obtain ⟨n, hn⟩ := hn

  have hinf2 : p = 2 → ∀ (w : NumberField.InfinitePlace ↥(levelField L F hLF)) (g : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)),
      g ∈ NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF) w → g = 1 := by
    intro h2 w g hg
    obtain ⟨i, hiL, hi⟩ := h4 h2
    exact NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_of_sq_eq_neg_one ↥L ↥(levelField L F hLF) ⟨i, hiL⟩
      (Subtype.ext (by simpa using hi)) w g hg

  have hsum : ∑ᶠ v : HeightOneSpectrum (𝓞 ↥L),
      ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) = 0 := by
    exact (M4aHerbrand.map_pi_eq_zero_iff_finsum_eq_zero_of_pow_smul_eq_zero ↥L ↥(levelField L F hLF) D hactI hact p hinf2
      prG hprG π hπv X q hq L' hL'fd instMS instMD Φ hΦ1 hΦ2 hΦ3 K₀ hK₀fd hbase θ hθ u' hu' n hn k hXk).1 hπX

  have hoff : ∀ v : HeightOneSpectrum (𝓞 ↥L), v ∉ placesOverPrimesFinset ↥L S →
      ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) = 0 := by
    intro v hv
    have h0 : (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)).subtype
          (prG (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) 2).hom X = 0 := by
      rw [hXdef]
      refine NumberField.LevelArith.map_prG_map_principalIdele_eq_zero_of_forall_comap_ne S L F hLF hF ι hι φ hbij hval D hactI
        j hj prG hprG f (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v) (fun v' hv' h => hv ?_)
      rw [NumberField.PlaceAbove.comap_above] at h
      rwa [IsDedekindDomain.HeightOneSpectrum.ext h]
    haveI := hq v; haveI := hL'fd v; letI := instMS v; letI := instMD v; haveI := hK₀fd v
    have hiff := NumberField.PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass ↥L ↥(levelField L F hLF)
      (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v) (hsolv v) (q v) (L' v) (Φ v) (hΦ1 v) (hΦ2 v) (hΦ3 v) (K₀ v) (hbase v)
      (θ v) (hθ v) (u' v) (hu' v) (n v)
    have h1 : n v • (groupCohomology.map (MonoidHom.id _) (θ v) 2).hom (u' v) = 0 := by
      rw [← hn v]
      exact h0
    exact NumberField.LevelArith.C3.coe_div_eq_zero_of_dvd (n v) _ Nat.card_pos.ne' (hiff.1 h1)

  have hon : ∀ v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)),
      inv a v = ((((n v.1 : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v.1)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by
    intro v
    apply hinv_eq
    haveI := hq v.1; haveI := hL'fd v.1; letI := instMS v.1; letI := instMD v.1; haveI := hK₀fd v.1
    haveI := NumberField.LevelArith.C3.faithfulSMul_decomp_above ↥L ↥(levelField L F hLF) v.1
    have hfaith : FaithfulSMul ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v.1)) ↥(L' v.1) :=
      NumberField.LevelArith.C3.faithfulSMul_of_equiv (Φ v.1).toEquiv (hΦ3 v.1)
    have hqmem := (NumberField.PlaceDecomp.mem_adicCompletionIntegers_iff_norm_le_one_and_natCast_mem_asIdeal_of_ringEquiv
      ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v.1) (q v.1) (L' v.1) (Φ v.1)).2
    exact ⟨prG, hprG, NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v.1, NumberField.PlaceAbove.comap_above _ _ _,
      q v.1, hq v.1, hqmem, L' v.1, hL'fd v.1, instMS v.1, hfaith, instMD v.1, Φ v.1, hΦ1 v.1, hΦ2 v.1, hΦ3 v.1,
      K₀ v.1, hK₀fd v.1, hbase v.1, θ v.1, hθ v.1, u' v.1, hu' v.1, n v.1, hn v.1, rfl⟩

  have hfin : ∑ᶠ v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)), inv a v =
      ∑ᶠ v : HeightOneSpectrum (𝓞 ↥L),
        ((((n v : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) (NumberField.PlaceAbove.above ↥L ↥(levelField L F hLF) v)) : ℚ) : ℚ) : AddCircle (1 : ℚ))) := by
    rw [finsum_congr hon]
    exact NumberField.LevelArith.C3.finsum_set_coe_eq_finsum_of_forall (placesOverPrimes ↥L (S : Set Nat.Primes)) _
      (fun v hv => hoff v (fun h => hv ((mem_placesOverPrimesFinset ↥L S v).1 h)))
  rw [hfin, hsum]

end S_NumberField_LevelArith_finsum_apply_eq_zero_of_isBrauerLocalInv
end P2MW
export P2MW.S_NumberField_LevelArith_finsum_apply_eq_zero_of_isBrauerLocalInv (solution)
