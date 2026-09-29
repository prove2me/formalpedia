-- Prove2me | solution 1 for NumberField.PlaceDecomp.sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2f499642-5200-50e6-942c-f8b83ee47fe0

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_NumberField_PlaceDecomp_finsum_inv_decomp_above_map_lam_rho_res_eq_zero_of_isPGroup_of_ne_two
import Theorems.Thm_NumberField_PlaceDecomp_map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one
import Theorems.Thm_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "instance" "RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal"
p2m_attr_erase "simp" "SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul IsLocalRing.principalUnits_zero GroupCohomology.RepPi.proj_hom_apply"
p2m_attr_erase "simp" "GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of"
p2m_attr_erase "simp" "IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory Module groupCohomology ExtCitation NumberField P2MW.S_NumberField_PlaceDecomp_sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside.NumberField IsDedekindDomain M4aHerbrand"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_PlaceDecomp_sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside.NumberField.PlaceDecomp"

namespace NumberField
p2m_export "NumberField" "mk place AdeleRing PlaceDecomp.decomp PlaceAbove.above PlaceAbove.comap_above PlaceDecomp.finsum_inv_decomp_above_map_lam_rho_res_eq_zero_of_isPGroup_of_ne_two PlaceDecomp.map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp finsum_inv_decomp_above_map_lam_rho_res_eq_zero_of_isPGroup_of_ne_two map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one"
namespace C7cBody
p2m_open "NumberField.PlaceDecomp NumberField"

theorem coe_mapCocycles₂' {G H : Type} [Group G] [Group H] {A : Rep ℤ H} {B : Rep ℤ G}
    (f : G →* H) (φ : Rep.res f A ⟶ B) (x : cocycles₂ A) :
    ((mapCocycles₂ f φ x : cocycles₂ B) : G × G → B) = fun gh => φ.hom (x (f gh.1, f gh.2)) := by
  funext gh
  exact congrFun (mapCocycles₂_comp_i_apply f φ x) gh
end NumberField.PlaceDecomp.C7cBody

open NumberField.PlaceDecomp.C7cBody in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hp2 : p ≠ 2)

    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F₀] [IsGalois ℚ ↥F₀] [NumberField ↥F₀]
    (hF₀ : F₀.IsUnramifiedOutside S)
    (E₀ : IntermediateField ℚ ↥F₀) [NumberField ↥E₀]
    (hG : IsPGroup p (↥F₀ ≃ₐ[↥E₀] ↥F₀))

    (D : IdeleGaloisDescent (𝓞 ↥F₀) ↥E₀ ↥F₀)
    (_ : MulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀))
    (_ : ∀ (g : ↥F₀ ≃ₐ[↥E₀] ↥F₀) (c : IdeleClassGroup (𝓞 ↥F₀) ↥F₀), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 ↥F₀), (w.adicCompletion ↥F₀)ˣ →* (AdeleRing (𝓞 ↥F₀) ↥F₀)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (x : (w.adicCompletion ↥F₀)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 ↥F₀), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 ↥F₀),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (w.adicCompletion ↥F₀)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
          (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)))
    (_ : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (x : (w.adicCompletion ↥F₀)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 ↥F₀) ↥F₀))
    (ρ : ∀ w : HeightOneSpectrum (𝓞 ↥F₀),
      Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (w.adicCompletion ↥F₀)ˣ)
    (_ : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (u : (↥F₀)ˣ),
      (ρ w).hom (Additive.ofMul u) =
        Additive.ofMul (Units.map (algebraMap ↥F₀ (w.adicCompletion ↥F₀)).toMonoidHom u))
    (V : ↥S → Finset (HeightOneSpectrum (𝓞 ↥E₀)))
    (_ : ∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 ↥E₀)), v ∈ V q ↔ (((q : Nat.Primes) : ℕ) : 𝓞 ↥E₀) ∈ v.asIdeal)

    (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ZMod p)
    (ζF : (↥F₀)ˣ) (hζp : ζF ^ p = 1)
    (b : (↥F₀ ≃ₐ[ℚ] ↥F₀) × (↥F₀ ≃ₐ[ℚ] ↥F₀) → Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[ℚ] ↥F₀) (↥F₀)ˣ)
    (hb : ∀ (g h : ↥F₀ ≃ₐ[ℚ] ↥F₀) (ĝ ĥ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (∀ y : ↥F₀, ĝ (y : AlgebraicClosure ℚ) = ((g y : ↥F₀) : AlgebraicClosure ℚ)) →
      (∀ y : ↥F₀, ĥ (y : AlgebraicClosure ℚ) = ((h y : ↥F₀) : AlgebraicClosure ℚ)) →
        b (g, h) = Additive.ofMul (ζF ^ ((f (ĝ, ĥ) : ZMod p).val)))
    (hbc : b ∈ cocycles₂ (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[ℚ] ↥F₀) (↥F₀)ˣ))
    (r : (↥F₀ ≃ₐ[↥E₀] ↥F₀) →* (↥F₀ ≃ₐ[ℚ] ↥F₀)) (hr : ∀ (g : ↥F₀ ≃ₐ[↥E₀] ↥F₀) (y : ↥F₀), r g y = g y)
    (φ : Rep.res r (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[ℚ] ↥F₀) (↥F₀)ˣ) ⟶ Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ)
    (hφ : ∀ u : (↥F₀)ˣ, φ.hom (Additive.ofMul u) = Additive.ofMul u)
    (x : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ))
    (hx : x = (groupCohomology.map r φ 2).hom ((H2π (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[ℚ] ↥F₀) (↥F₀)ˣ)).hom ⟨b, hbc⟩))

    (invG : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)) 2) →+
      AddCircle (1 : ℚ))
    (inv : ∀ H : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀),
      ↥(groupCohomology (Rep.res H.subtype (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀))) 2) →+
        AddCircle (1 : ℚ))

    (_ : Function.Injective invG)
    (_ : ∀ H : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀), Function.Injective (inv H))
    (_ : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (↥F₀ ≃ₐ[↥E₀] ↥F₀) • t = 0)
    (_ : ∀ (H : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0)

    (_ : ∀ (H : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀))
      (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)) 2)),
      inv H ((groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)))) 2).hom x) =
          H.index • invG x)

    (_ : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) L']
        [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (↥L')ˣ]
        (Φ : w.adicCompletion ↥F₀ ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (x : ℚ_[q]),
          g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (x : w.adicCompletion ↥F₀), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (w.adicCompletion ↥F₀)ˣ)
        (_ : ∀ v : (↥L')ˣ,
          ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion ↥F₀)ˣ) : w.adicCompletion ↥F₀) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) K₀ u'),
        inv (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (lam w) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) θ 2).hom u')) =
          (((1 : ℚ) / (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w) : ℚ) : ℚ) : AddCircle (1 : ℚ)))

    (_ : ∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)) 2),
        invG x = inv ⊤ ((groupCohomology.map (⊤ : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀)).subtype
          (𝟙 (Rep.res (⊤ : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀)).subtype
            (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)))) 2).hom x))

    (t : ↥S → ℕ)
    (ha : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (q : ↥S), (((q : Nat.Primes) : ℕ) : 𝓞 ↥F₀) ∈ w.asIdeal →
        inv (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (lam w) 2).hom
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (ρ w) 2).hom
              ((groupCohomology.map (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
                (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
                  (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ))) 2).hom x))) =
        ((((Ideal.ramificationIdx' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)})
              (Ideal.comap (algebraMap (𝓞 ↥E₀) (𝓞 ↥F₀)) w.asIdeal) *
            Ideal.inertiaDeg' (Ideal.span {(((q : Nat.Primes) : ℕ) : ℤ)})
              (Ideal.comap (algebraMap (𝓞 ↥E₀) (𝓞 ↥F₀)) w.asIdeal) * t q : ℕ) : ℚ) / (p : ℚ) : ℚ) : AddCircle (1 : ℚ))) :
    ∀ w : ↥S → HeightOneSpectrum (𝓞 ↥E₀) → HeightOneSpectrum (𝓞 ↥F₀),
        (∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 ↥E₀)), v ∈ V q →
          Ideal.comap (algebraMap (𝓞 ↥E₀) (𝓞 ↥F₀)) (w q v).asIdeal = v.asIdeal) →
        ∑ q : ↥S, ∑ v ∈ V q,
          inv (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ (w q v))
            ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ (w q v))) (lam (w q v)) 2).hom
              ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ (w q v))) (ρ (w q v)) 2).hom
                ((groupCohomology.map (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ (w q v)).subtype
                  (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ (w q v)).subtype
                    (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ))) 2).hom x))) = 0 := by
  classical
  intro wsel hwsel
  have hp : p.Prime := Fact.out

  have hact : ∀ (g : ↥F₀ ≃ₐ[↥E₀] ↥F₀) (c : IdeleClassGroup (𝓞 ↥F₀) ↥F₀), g • c = D.classAct g c := by assumption
  have hι : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (x : (w.adicCompletion ↥F₀)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 ↥F₀), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1 := by
    assumption
  have hlam : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (x : (w.adicCompletion ↥F₀)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 ↥F₀) ↥F₀) := by assumption
  have hρ : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (u : (↥F₀)ˣ),
      (ρ w).hom (Additive.ofMul u) = Additive.ofMul (Units.map (algebraMap ↥F₀ (w.adicCompletion ↥F₀)).toMonoidHom u) := by
    assumption
  have hV : ∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 ↥E₀)), v ∈ V q ↔ (((q : Nat.Primes) : ℕ) : 𝓞 ↥E₀) ∈ v.asIdeal := by assumption
  have hinjG : Function.Injective invG := by assumption
  have hinj : ∀ H : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀), Function.Injective (inv H) := by assumption
  have hrangeG : ∀ t : AddCircle (1 : ℚ), t ∈ invG.range ↔ Nat.card (↥F₀ ≃ₐ[↥E₀] ↥F₀) • t = 0 := by assumption
  have hrange : ∀ (H : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀)) (t : AddCircle (1 : ℚ)), t ∈ (inv H).range ↔ Nat.card ↥H • t = 0 := by
    assumption
  have hres : ∀ (H : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀))
      (x : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)) 2)),
      inv H ((groupCohomology.map H.subtype
        (𝟙 (Rep.res H.subtype (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)))) 2).hom x) =
          H.index • invG x := by assumption
  have htop : ∀ x : ↥(groupCohomology (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)) 2),
      invG x = inv ⊤ ((groupCohomology.map (⊤ : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀)).subtype
        (𝟙 (Rep.res (⊤ : Subgroup (↥F₀ ≃ₐ[↥E₀] ↥F₀)).subtype
          (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (IdeleClassGroup (𝓞 ↥F₀) ↥F₀)))) 2).hom x) := by assumption

  let T : HeightOneSpectrum (𝓞 ↥F₀) → AddCircle (1 : ℚ) := fun w =>
    inv (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)
      ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (lam w) 2).hom
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (ρ w) 2).hom
          ((groupCohomology.map (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
            (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
              (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ))) 2).hom x)))
  have hT : ∀ w, T w = inv (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)
      ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (lam w) 2).hom
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (ρ w) 2).hom
          ((groupCohomology.map (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
            (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
              (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ))) 2).hom x))) := fun _ => rfl
  show ∑ q : ↥S, ∑ v ∈ V q, T (wsel q v) = 0

  have exists_primes_cast_mem : ∀ w : HeightOneSpectrum (𝓞 ↥F₀), ∃ ℓ : Nat.Primes, ((ℓ : ℕ) : 𝓞 ↥F₀) ∈ w.asIdeal := by
    intro w
    haveI : Finite (𝓞 ↥F₀ ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
    refine ⟨⟨ringChar (𝓞 ↥F₀ ⧸ w.asIdeal), CharP.prime_ringChar (𝓞 ↥F₀ ⧸ w.asIdeal)⟩, ?_⟩
    show ((ringChar (𝓞 ↥F₀ ⧸ w.asIdeal) : ℕ) : 𝓞 ↥F₀) ∈ w.asIdeal
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (𝓞 ↥F₀ ⧸ w.asIdeal) (ringChar (𝓞 ↥F₀ ⧸ w.asIdeal))

  have natPrime_unique : ∀ (w : HeightOneSpectrum (𝓞 ↥F₀)) (a b : ℕ), a.Prime → b.Prime →
      ((a : ℕ) : 𝓞 ↥F₀) ∈ w.asIdeal → ((b : ℕ) : 𝓞 ↥F₀) ∈ w.asIdeal → a = b := by
    intro w a b ha' hb' hma hmb
    by_contra hne
    have hcop : Nat.Coprime a b := (Nat.coprime_primes ha' hb').2 hne
    obtain ⟨m, n, hmn⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have e1 : ((m : ℤ) : 𝓞 ↥F₀) * (a : 𝓞 ↥F₀) + ((n : ℤ) : 𝓞 ↥F₀) * (b : 𝓞 ↥F₀) = 1 := by
      exact_mod_cast congrArg (fun z : ℤ => (z : 𝓞 ↥F₀)) hmn
    have h1 : (1 : 𝓞 ↥F₀) ∈ w.asIdeal := by
      rw [← e1]; exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hma) (w.asIdeal.mul_mem_left _ hmb)
    exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

  have hoff : ∀ w : HeightOneSpectrum (𝓞 ↥F₀), (∀ q : ↥S, (((q : Nat.Primes) : ℕ) : 𝓞 ↥F₀) ∉ w.asIdeal) →
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w)) (ρ w) 2).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype
          (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ↥E₀ ↥F₀ w).subtype (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ))) 2).hom x) = 0 := by
    intro w hwS
    obtain ⟨ℓ, hℓw⟩ := exists_primes_cast_mem w
    have hℓS : ℓ ∉ S := fun h => hwS ⟨ℓ, h⟩ hℓw

    let φL : ↥E₀ →ₐ[ℚ] ↥F₀ := E₀.val
    have key := NumberField.ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
      ↥E₀ F₀ φL ℓ ℓ.2 (fun P hP => hF₀.2 ℓ hℓS P hP)
    have hA : (φL.toRingHom.toAlgebra : Algebra ↥E₀ ↥F₀) = (inferInstance : Algebra ↥E₀ ↥F₀) :=
      Algebra.algebra_ext _ _ fun r => rfl
    have key' := key w.asIdeal (inferInstance : w.asIdeal.IsMaximal) hℓw
    rw [hA] at key'
    have hunr : Ideal.ramificationIdx' (Ideal.comap (algebraMap (𝓞 ↥E₀) (𝓞 ↥F₀)) w.asIdeal) w.asIdeal = 1 := key'

    let bE := mapCocycles₂ r φ ⟨b, hbc⟩
    have hxE : x = (H2π (Rep.ofMulDistribMulAction (↥F₀ ≃ₐ[↥E₀] ↥F₀) (↥F₀)ˣ)).hom ⟨bE, bE.2⟩ := by
      rw [hx, groupCohomology.H2π_comp_map_apply]
      rfl
    have hfin : ∀ gh : (↥F₀ ≃ₐ[↥E₀] ↥F₀) × (↥F₀ ≃ₐ[↥E₀] ↥F₀), IsOfFinOrder (Additive.toMul ((bE : _ → _) gh) : (↥F₀)ˣ) := by
      intro gh
      have hcoe : (bE : _ → _) gh = φ.hom (b (r gh.1, r gh.2)) := congrFun (coe_mapCocycles₂' r φ ⟨b, hbc⟩) gh

      have hlift : ∀ g : ↥F₀ ≃ₐ[ℚ] ↥F₀, ∃ ĝ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          ∀ y : ↥F₀, ĝ (y : AlgebraicClosure ℚ) = ((g y : ↥F₀) : AlgebraicClosure ℚ) :=
        fun g => ⟨g.liftNormal (AlgebraicClosure ℚ), fun y => AlgEquiv.liftNormal_commutes g (AlgebraicClosure ℚ) y⟩
      obtain ⟨ĝ, hĝ⟩ := hlift (r gh.1)
      obtain ⟨ĥ, hĥ⟩ := hlift (r gh.2)
      rw [hcoe, hb (r gh.1) (r gh.2) ĝ ĥ hĝ hĥ]
      erw [hφ]
      show IsOfFinOrder (ζF ^ (f (ĝ, ĥ)).val)
      refine (isOfFinOrder_iff_pow_eq_one).2 ⟨p, hp.pos, ?_⟩
      rw [← pow_mul, mul_comm, pow_mul, hζp, one_pow]
    rw [hxE]
    exact NumberField.PlaceDecomp.map_map_res_H2_units_eq_zero_of_isOfFinOrder_of_ramificationIdx_eq_one ↥E₀ ↥F₀ w hunr
      (ρ w) (hρ w) bE bE.2 hfin

  have hF6 := NumberField.PlaceDecomp.finsum_inv_decomp_above_map_lam_rho_res_eq_zero_of_isPGroup_of_ne_two ↥E₀ ↥F₀ p hp2 hG
    D hact ι hι lam hlam x ρ hρ invG inv hinjG hinj hrangeG hrange hres (by assumption) htop S hoff

  have habove : ∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 ↥E₀)), v ∈ V q →
      (((q : Nat.Primes) : ℕ) : 𝓞 ↥F₀) ∈ (NumberField.PlaceAbove.above ↥E₀ ↥F₀ v).asIdeal := by
    intro q v hv
    have := (hV q v).1 hv
    rw [← NumberField.PlaceAbove.comap_above ↥E₀ ↥F₀ v, Ideal.mem_comap, map_natCast] at this
    exact this
  have hwsel_mem : ∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 ↥E₀)), v ∈ V q →
      (((q : Nat.Primes) : ℕ) : 𝓞 ↥F₀) ∈ (wsel q v).asIdeal := by
    intro q v hv
    have := (hV q v).1 hv
    rw [← hwsel q v hv, Ideal.mem_comap, map_natCast] at this
    exact this
  have hterm : ∀ (q : ↥S) (v : HeightOneSpectrum (𝓞 ↥E₀)), v ∈ V q →
      T (wsel q v) = T (NumberField.PlaceAbove.above ↥E₀ ↥F₀ v) := by
    intro q v hv
    rw [hT, hT, ha _ q (hwsel_mem q v hv), ha _ q (habove q v hv), hwsel q v hv, NumberField.PlaceAbove.comap_above]

  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset ↥S)) V := by
    intro q _ q' _ hqq'
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    apply hqq'
    have h1 := habove q v hv
    have h2 := habove q' v hv'
    have := natPrime_unique _ _ _ (q : Nat.Primes).2 (q' : Nat.Primes).2 h1 h2
    exact Subtype.ext (Subtype.ext this)
  have hsupp : (Function.support fun v : HeightOneSpectrum (𝓞 ↥E₀) => T (NumberField.PlaceAbove.above ↥E₀ ↥F₀ v)) ⊆
      ↑((Finset.univ : Finset ↥S).biUnion V) := by
    intro v hv
    rw [Function.mem_support] at hv
    rw [Finset.coe_biUnion, Set.mem_iUnion₂]
    by_contra hno
    apply hv
    rw [hT]
    have h0 := hoff (NumberField.PlaceAbove.above ↥E₀ ↥F₀ v) (fun q hq => hno ⟨q, Finset.mem_coe.2 (Finset.mem_univ q), ?_⟩)
    · rw [h0, map_zero, map_zero]
    · rw [Finset.mem_coe, hV q v, ← NumberField.PlaceAbove.comap_above ↥E₀ ↥F₀ v, Ideal.mem_comap, map_natCast]
      exact hq
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_biUnion hdisj] at hF6
  rw [← hF6]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun v hv => hterm q v hv

end S_NumberField_PlaceDecomp_sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside
end P2MW
export P2MW.S_NumberField_PlaceDecomp_sum_sum_inv_decomp_eq_zero_of_forall_inv_eq_of_isUnramifiedOutside (solution)
