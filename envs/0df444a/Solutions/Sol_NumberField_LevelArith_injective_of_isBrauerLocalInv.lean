-- Prove2me | solution 1 for NumberField.LevelArith.injective_of_isBrauerLocalInv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/263c8b3b-38be-5b0d-8d31-04922f7a4b04

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
import Definitions.Def_NumberField_BrauerLocalInvariantPresentation
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_NumberField_LevelArith_exists_layer_presentation_and_pow_smul_eq_zero
import Theorems.Thm_NumberField_LevelArith_map_prG_map_principalIdele_eq_zero_of_forall_comap_ne
import Theorems.Thm_M4aHerbrand_map_prInf_eq_zero_of_pow_smul_eq_zero
import Theorems.Thm_NumberField_IdeleLocalInv_exists_hasLocalInv
import Theorems.Thm_NumberField_PlaceDecomp_zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass
import Theorems.Thm_M4aHerbrand_map_prG_eq_map_map_prG_of_smul_eq
import Theorems.Thm_M4aHerbrand_injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles
import Theorems.Thm_M4aHerbrand_exists_hom_res_decomp_ideles_adicCompletion_apply
import Theorems.Thm_M4aHerbrand_exists_hom_res_infPlaceDecomp_ideles_localUnits_apply
import Theorems.Thm_NumberField_InfPlaceDecomp_eq_one_of_mem_decomp_of_sq_eq_neg_one
import Theorems.Thm_NumberField_LevelArith_continuousH2SrInflation_H2pi_eq_zero_of_map_principalIdele_eq_zero_of_pow_smul_eq_zero
import Theorems.Thm_NumberField_PlaceTransport_orbit_eq_setOf_under_eq
import Theorems.Thm_NumberField_PlaceTransport_stabilizer_eq_decomp
import Theorems.Thm_NumberField_PlaceTransport_transport_eq_actRingEquiv
import Theorems.Thm_NumberField_PlaceTransport_transport_trans_transport
import Theorems.Thm_IntermediateField_isSolvable_algEquiv_of_padic
import Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_injective_of_isBrauerLocalInv
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "instance" "NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe"
p2m_attr_erase "simp" "coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct Pointwise
open IsDedekindDomain M4aHerbrand
open scoped NumberField NumberField.PlaceDecomp NumberField.InfPlaceDecomp NumberField.PlaceTransport

namespace InjAux

section Solvable
open ExtCitation.LocalLevel

theorem isSolvable_layer (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀] (hK : IsBase q L G K₀) : Group.IsSolvable G := by
  classical
  haveI := Fintype.ofFinite G
  let E' : IntermediateField K₀ (PadicAlgCl q) := IntermediateField.extendScalars hK.le
  have memE : ∀ x : PadicAlgCl q, x ∈ E' ↔ x ∈ L := fun x => Iff.rfl
  let toL : E' → L := fun x => ⟨x.1, (memE x.1).1 x.2⟩
  let ofL : L → E' := fun y => ⟨y.1, (memE y.1).2 y.2⟩
  have hfix : ∀ (g : G) (r : K₀), g • toL (algebraMap K₀ E' r) = toL (algebraMap K₀ E' r) :=
    fun g r => (hK.mem_iff _).1 r.2 g

  let ψ₀ : G → (E' ≃ₐ[K₀] E') := fun g =>
    { toFun := fun x => ofL (g • toL x)
      invFun := fun x => ofL (g⁻¹ • toL x)
      left_inv := fun x => by
        change ofL (g⁻¹ • g • toL x) = x
        rw [← mul_smul, inv_mul_cancel, one_smul]
      right_inv := fun x => by
        change ofL (g • g⁻¹ • toL x) = x
        rw [← mul_smul, mul_inv_cancel, one_smul]
      map_mul' := fun x y => by
        change ofL (g • (toL x * toL y)) = ofL (g • toL x) * ofL (g • toL y)
        rw [smul_mul']
        rfl
      map_add' := fun x y => by
        change ofL (g • (toL x + toL y)) = ofL (g • toL x) + ofL (g • toL y)
        rw [smul_add]
        rfl
      commutes' := fun r => by
        change ofL (g • toL (algebraMap K₀ E' r)) = _
        rw [hfix] }
  have ψ₀_apply : ∀ (g : G) (x : E'), toL (ψ₀ g x) = g • toL x := fun g x => rfl
  let ψ : G →* (E' ≃ₐ[K₀] E') :=
    { toFun := ψ₀
      map_one' := by
        ext x
        change ((ofL ((1 : G) • toL x) : E') : PadicAlgCl q) = x
        rw [one_smul]
      map_mul' := fun g h => by
        ext x
        change ((ofL ((g * h) • toL x) : E') : PadicAlgCl q) = ((ofL (g • toL (ofL (h • toL x))) : E') : PadicAlgCl q)
        rw [mul_smul] }
  have hψ : Function.Injective ψ := by
    intro g h hgh
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro y
    have := congrArg (fun f : E' ≃ₐ[K₀] E' => toL (f (ofL y))) hgh
    exact this

  let eL : E' ≃ₗ[ℚ_[q]] L :=
    { toFun := toL, invFun := ofL, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  haveI : Module.Finite ℚ_[q] E' := Module.Finite.equiv eL.symm
  haveI : FiniteDimensional K₀ E' := Module.Finite.of_restrictScalars_finite ℚ_[q] K₀ E'
  have hdeg : Module.finrank K₀ E' = Fintype.card G := by
    have h1 := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L G hG K₀ hK.le hK.mem_iff
    have h2 := Module.finrank_mul_finrank ℚ_[q] K₀ E'
    rw [LinearEquiv.finrank_eq eL, h1, Nat.card_eq_fintype_card, mul_comm] at h2
    have hpos : 0 < Module.finrank ℚ_[q] K₀ := Module.finrank_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hcard : Fintype.card (E' ≃ₐ[K₀] E') = Module.finrank K₀ E' := by
    apply le_antisymm AlgEquiv.card_le
    rw [hdeg]
    exact Fintype.card_le_of_injective ψ hψ
  haveI : IsGalois K₀ E' := IsGalois.of_card_aut_eq_finrank K₀ E' (by rw [Nat.card_eq_fintype_card]; exact hcard)
  haveI := IntermediateField.isSolvable_algEquiv_of_padic q K₀ E'
  exact solvable_of_solvable_injective hψ

end Solvable

end InjAux

namespace E0Aux

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

noncomputable def conjD (σ : K ≃ₐ[E] K) {w w₁ : HeightOneSpectrum (𝓞 K)} (hσ : σ • w = w₁) :
    ↥(NumberField.PlaceDecomp.decomp E K w₁) →* ↥(NumberField.PlaceDecomp.decomp E K w) :=
  (((MulAut.conj σ⁻¹).toMonoidHom).comp (NumberField.PlaceDecomp.decomp E K w₁).subtype).codRestrict _ (fun τ => by
    rw [← NumberField.PlaceTransport.stabilizer_eq_decomp, MulAction.mem_stabilizer_iff]
    have hτ : (τ : K ≃ₐ[E] K) • w₁ = w₁ :=
      MulAction.mem_stabilizer_iff.mp (by rw [NumberField.PlaceTransport.stabilizer_eq_decomp]; exact τ.2)
    change (σ⁻¹ * (τ : K ≃ₐ[E] K) * σ⁻¹⁻¹) • w = w
    rw [inv_inv, mul_smul, mul_smul, hσ, hτ, ← hσ, inv_smul_smul])

theorem coe_conjD (σ : K ≃ₐ[E] K) {w w₁ : HeightOneSpectrum (𝓞 K)} (hσ : σ • w = w₁) (τ : ↥(NumberField.PlaceDecomp.decomp E K w₁)) :
    ((conjD σ hσ τ : ↥(NumberField.PlaceDecomp.decomp E K w)) : K ≃ₐ[E] K) = σ⁻¹ * (τ : K ≃ₐ[E] K) * σ := by
  change σ⁻¹ * (τ : K ≃ₐ[E] K) * σ⁻¹⁻¹ = _
  rw [inv_inv]

theorem transportUnits_conjD_smul (σ : K ≃ₐ[E] K) {w w₁ : HeightOneSpectrum (𝓞 K)} (hσ : σ • w = w₁)
    (τ : ↥(NumberField.PlaceDecomp.decomp E K w₁)) (u : (w.adicCompletion K)ˣ) :
    NumberField.PlaceTransport.transportUnits σ hσ (conjD σ hσ τ • u) = τ • NumberField.PlaceTransport.transportUnits σ hσ u := by
  have hp : ((conjD σ hσ τ : ↥(NumberField.PlaceDecomp.decomp E K w)) : K ≃ₐ[E] K) • w = w :=
    MulAction.mem_stabilizer_iff.mp (by rw [NumberField.PlaceTransport.stabilizer_eq_decomp]; exact (conjD σ hσ τ).2)
  have hq : (τ : K ≃ₐ[E] K) • w₁ = w₁ :=
    MulAction.mem_stabilizer_iff.mp (by rw [NumberField.PlaceTransport.stabilizer_eq_decomp]; exact τ.2)
  refine Units.ext ?_
  show NumberField.PlaceTransport.transport σ hσ (((conjD σ hσ τ) • u : (w.adicCompletion K)ˣ) : w.adicCompletion K) =
    ((τ • NumberField.PlaceTransport.transportUnits σ hσ u : (w₁.adicCompletion K)ˣ) : w₁.adicCompletion K)
  rw [NumberField.PlaceDecomp.coe_smul_units, NumberField.PlaceDecomp.coe_smul_units, NumberField.PlaceDecomp.smul_def,
    NumberField.PlaceDecomp.smul_def,
    ← NumberField.PlaceTransport.transport_eq_actRingEquiv E K w _ hp,
    ← NumberField.PlaceTransport.transport_eq_actRingEquiv E K w₁ _ hq]
  show NumberField.PlaceTransport.transport σ hσ (NumberField.PlaceTransport.transport _ hp (u : w.adicCompletion K)) =
    NumberField.PlaceTransport.transport _ hq (NumberField.PlaceTransport.transport σ hσ (u : w.adicCompletion K))
  have h3 : (σ * ((conjD σ hσ τ : ↥(NumberField.PlaceDecomp.decomp E K w)) : K ≃ₐ[E] K)) • w = w₁ := by rw [mul_smul, hp, hσ]
  have h3' : ((τ : K ≃ₐ[E] K) * σ) • w = w₁ := by rw [mul_smul, hσ, hq]
  rw [← RingEquiv.trans_apply, ← RingEquiv.trans_apply,
    NumberField.PlaceTransport.transport_trans_transport E K σ _ hp hσ h3,
    NumberField.PlaceTransport.transport_trans_transport E K (τ : K ≃ₐ[E] K) σ hσ hq h3']
  have heq : (τ : K ≃ₐ[E] K) * σ = σ * ((conjD σ hσ τ : ↥(NumberField.PlaceDecomp.decomp E K w)) : K ≃ₐ[E] K) := by
    rw [coe_conjD, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  simp only [heq]

def resRepHomOfMulEquivariant {P Q : Type} [Group P] [Group Q] {M N : Type} [CommGroup M] [CommGroup N]
    [MulDistribMulAction P M] [MulDistribMulAction Q N]
    (c : Q →* P) (f : M →* N) (hf : ∀ (q : Q) (m : M), f (c q • m) = q • f m) :
    Rep.res c (Rep.ofMulDistribMulAction P M) ⟶ Rep.ofMulDistribMulAction Q N :=
  Rep.ofHom ⟨(MonoidHom.toAdditive f).toIntLinearMap, fun q => LinearMap.ext fun (x : Additive M) => by
    change Additive.ofMul (f (c q • Additive.toMul x)) = Additive.ofMul (q • f (Additive.toMul x))
    rw [hf]⟩

theorem resRepHomOfMulEquivariant_hom_apply {P Q : Type} [Group P] [Group Q] {M N : Type} [CommGroup M] [CommGroup N]
    [MulDistribMulAction P M] [MulDistribMulAction Q N]
    (c : Q →* P) (f : M →* N) (hf : ∀ (q : Q) (m : M), f (c q • m) = q • f m) (x : Additive M) :
    (resRepHomOfMulEquivariant c f hf).hom x = Additive.ofMul (f (Additive.toMul x)) := rfl

noncomputable def Ttransport (σ : K ≃ₐ[E] K) {w w₁ : HeightOneSpectrum (𝓞 K)} (hσ : σ • w = w₁) :
    Rep.res (conjD σ hσ) (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w) (w.adicCompletion K)ˣ) ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp E K w₁) (w₁.adicCompletion K)ˣ :=
  resRepHomOfMulEquivariant (conjD σ hσ) (NumberField.PlaceTransport.transportUnits σ hσ).toMonoidHom
    (fun τ u => transportUnits_conjD_smul σ hσ τ u)

theorem Ttransport_apply (σ : K ≃ₐ[E] K) {w w₁ : HeightOneSpectrum (𝓞 K)} (hσ : σ • w = w₁) (x : (w.adicCompletion K)ˣ) :
    ((Additive.toMul ((Ttransport (E := E) σ hσ).hom (Additive.ofMul x)) : (w₁.adicCompletion K)ˣ) : w₁.adicCompletion K) =
      NumberField.PlaceTransport.transport σ hσ (x : w.adicCompletion K) := rfl

theorem exists_int_of_zsmul_coe_eq_zero {d : ℤ} (hd : d ≠ 0) {r : ℚ} (h : d • ((r : ℚ) : AddCircle (1 : ℚ)) = 0) :
    ∃ m : ℤ, r = (m : ℚ) / (d : ℚ) := by
  rw [← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  rw [zsmul_eq_mul, mul_one, zsmul_eq_mul] at hm
  rw [eq_div_iff (by exact_mod_cast hd : (d : ℚ) ≠ 0), mul_comm]
  exact hm.symm

end E0Aux

set_option maxHeartbeats 6400000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (inv : ↥(Submodule.torsion' ℤ (continuousH2Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (Submonoid.powers (p : ℤ)))
        →ₗ[ℤ] (↥(placesOverPrimes ↥L (S : Set Nat.Primes)) → AddCircle (1 : ℚ)))
    (hinv : IsBrauerLocalInv p S L inv) :
    Function.Injective inv := by
  classical
  refine (injective_iff_map_eq_zero inv).2 fun a ha => ?_

  have hP := NumberField.LevelArith.exists_layer_presentation_and_pow_smul_eq_zero S L hL a
  rcases hP with ⟨F, hLF, fdF, nF, galF, hF, ι, hι, φ, hφ, hφval, D, instI, hactI, j, hj, f, k, hfa, hk⟩
  haveI := fdF
  haveI := nF
  haveI := galF
  letI := instI
  haveI : FiniteDimensional ↥L ↥(levelField L F hLF) := Module.Finite.of_restrictScalars_finite ℚ ↥L ↥(levelField L F hLF)
  haveI : Finite (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := inferInstance

  have hxk : (p ^ k : ℤ) • ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) = 0 := by
    rw [← map_zsmul, hk, map_zero]

  have h0 : ∀ v : ↥(placesOverPrimes ↥L (S : Set Nat.Primes)),
      NumberField.IdeleLocalInv.HasLocalInv ↥L ↥(levelField L F hLF) D hactI ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) v.1 0 := by
    intro v
    obtain ⟨t, ht⟩ := NumberField.IdeleLocalInv.exists_hasLocalInv ↥L ↥(levelField L F hLF) D hactI ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) v.1
    have hread : inv a v = t := hinv F hLF hF ι hι φ hφ hφval D hactI j hj f a hfa v t ht
    have ht0 : t = 0 := by rw [← hread, ha]; rfl
    rwa [ht0] at ht

  obtain ⟨prG, hprG⟩ := M4aHerbrand.exists_hom_res_decomp_ideles_adicCompletion_apply ↥L ↥(levelField L F hLF) D hactI
  obtain ⟨prInf, hprInf⟩ := M4aHerbrand.exists_hom_res_infPlaceDecomp_ideles_localUnits_apply ↥L ↥(levelField L F hLF) D hactI

  have hfin : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (prG w) 2).hom ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) = 0 := by
    intro w
    by_cases hw : ∀ v ∈ placesOverPrimesFinset ↥L S, w.asIdeal.comap (algebraMap (𝓞 ↥L) (𝓞 ↥(levelField L F hLF))) ≠ v.asIdeal
    ·
      exact NumberField.LevelArith.map_prG_map_principalIdele_eq_zero_of_forall_comap_ne S L F hLF hF ι hι φ hφ hφval D hactI j hj
        prG hprG f w hw
    ·
      push Not at hw
      obtain ⟨v, hvS, hwv⟩ := hw
      have hvS' : v ∈ placesOverPrimes ↥L (S : Set Nat.Primes) := (mem_placesOverPrimesFinset ↥L S v).1 hvS
      obtain ⟨prG', hprG', w', hw', q, hq, hqw, L', fd', act', faith', actU', Φ', h1', h2', h3', K₀', fd₀', base', θ', hθ', u', hu', n,
        hcoord, ht⟩ := h0 ⟨v, hvS'⟩

      have hpr : prG' w' = prG w' := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro y
        exact (hprG' w' (Additive.toMul y)).trans (hprG w' (Additive.toMul y)).symm

      have hdvd : (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w') : ℤ) ∣ n := by
        have hz := ht.symm
        rw [AddCircle.coe_eq_zero_iff] at hz
        obtain ⟨z, hz⟩ := hz
        rw [zsmul_eq_mul, mul_one,
          eq_div_iff (by exact_mod_cast Nat.card_pos.ne' : (Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w') : ℚ) ≠ 0)] at hz
        exact ⟨z, by exact_mod_cast (hz.symm.trans (mul_comm _ _))⟩
      haveI := hq; haveI := fd'; letI := act'; haveI := faith'; letI := actU'; haveI := fd₀'
      have hsolv : Group.IsSolvable ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w') := InjAux.isSolvable_layer q L' (↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w')) h1' K₀' base'
      have hzero : n • (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w')) θ' 2).hom u' = 0 :=
        (NumberField.PlaceDecomp.zsmul_map_eq_zero_iff_natCard_decomp_dvd_of_isLocalFundamentalClass ↥L ↥(levelField L F hLF) w' hsolv q L' Φ' h1' h2' h3'
          K₀' base' θ' hθ' u' hu' n).2 hdvd
      have hw'0 : (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w').subtype (prG w') 2).hom ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) = 0 := by
        rw [← hpr, hcoord, hzero]

      have hmem : w ∈ MulAction.orbit (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) w' := by
        rw [NumberField.PlaceTransport.orbit_eq_setOf_under_eq ↥L ↥(levelField L F hLF)]
        change w.under (𝓞 ↥L) = w'.under (𝓞 ↥L)
        apply HeightOneSpectrum.ext
        rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
        exact hwv.trans hw'.symm
      obtain ⟨σ, hσ⟩ := hmem
      change σ • w' = w at hσ
      rw [M4aHerbrand.map_prG_eq_map_map_prG_of_smul_eq ↥L ↥(levelField L F hLF) D hactI prG hprG w' w σ hσ
        (E0Aux.conjD σ hσ) (fun τ => E0Aux.coe_conjD σ hσ τ) (E0Aux.Ttransport σ hσ) (fun y => E0Aux.Ttransport_apply σ hσ y) 2 ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)),
        hw'0, map_zero]

  have hinf2 : p = 2 → ∀ (v : NumberField.InfinitePlace ↥(levelField L F hLF)) (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))), g ∈ NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF) v → g = 1 := by
    intro hp2 v g hg
    obtain ⟨i, hiL, hi⟩ := h4 hp2
    have hi' : (⟨i, hiL⟩ : ↥L) ^ 2 = -1 := Subtype.ext hi
    exact NumberField.InfPlaceDecomp.eq_one_of_mem_decomp_of_sq_eq_neg_one ↥L ↥(levelField L F hLF) ⟨i, hiL⟩ hi' v g hg
  have hinf : ∀ v : NumberField.InfinitePlace ↥(levelField L F hLF),
      (groupCohomology.map (NumberField.InfPlaceDecomp.decomp ↥L ↥(levelField L F hLF) v).subtype (prInf v) 2).hom ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) = 0 := fun v =>
    M4aHerbrand.map_prInf_eq_zero_of_pow_smul_eq_zero ↥L ↥(levelField L F hLF) prInf p hinf2 ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) k hxk v

  have hx0 : ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) = 0 :=
    (M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles ↥L ↥(levelField L F hLF) D hactI prG hprG prInf hprInf 1).1
      ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f)) hfin hinf

  have hz := NumberField.LevelArith.continuousH2SrInflation_H2pi_eq_zero_of_map_principalIdele_eq_zero_of_pow_smul_eq_zero S hpS L hL F hLF hF
    ι hι φ hφ hφval D hactI j hj f k hk hx0
  exact Subtype.ext (hfa.trans hz)

end S_NumberField_LevelArith_injective_of_isBrauerLocalInv
end P2MW
export P2MW.S_NumberField_LevelArith_injective_of_isBrauerLocalInv (solution)
