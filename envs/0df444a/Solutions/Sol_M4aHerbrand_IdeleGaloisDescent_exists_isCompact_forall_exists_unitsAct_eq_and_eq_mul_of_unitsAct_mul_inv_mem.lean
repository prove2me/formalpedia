-- Prove2me | solution 1 for M4aHerbrand.IdeleGaloisDescent.exists_isCompact_forall_exists_unitsAct_eq_and_eq_mul_of_unitsAct_mul_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/96f4c84b-de5f-589e-888c-2da41996b20a

import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_isCompact_forall_exists_unitsAct_eq_and_eq_mul_of_unitsAct_mul_inv_mem
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply"
p2m_attr_erase "simp" "AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul"
p2m_attr_erase "simp" "NumberField.SUnits.val_add Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false

open NumberField Topology

namespace R1S9GL1Cob

theorem exists_isCompact_forall_exists_eq_mul {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [Group H] [TopologicalSpace H]
    (f : G →* H) (hopen : IsOpenMap f)
    (Ω : Set H) (hΩ : IsCompact Ω) (hΩr : Ω ⊆ Set.range f) :
    ∃ C : Set G, IsCompact C ∧ ∀ e : G, f e ∈ Ω → ∃ k c : G, f k = 1 ∧ c ∈ C ∧ e = k * c := by
  classical

  have hpre : ∀ h ∈ Ω, ∃ g : G, f g = h := fun h hh => hΩr hh
  choose g hg using hpre
  have hK : ∀ x : G, ∃ K : Set G, IsCompact K ∧ K ∈ 𝓝 x := fun x => exists_compact_mem_nhds x
  choose K hKc hKn using hK

  have hcov : Ω ⊆ ⋃ h : Ω, f '' interior (K (g h.1 h.2)) := by
    intro h hh
    refine Set.mem_iUnion.mpr ⟨⟨h, hh⟩, ?_⟩
    exact ⟨g h hh, mem_interior_iff_mem_nhds.mpr (hKn _), hg h hh⟩
  obtain ⟨T, hT⟩ := hΩ.elim_finite_subcover (fun h : Ω => f '' interior (K (g h.1 h.2)))
    (fun h => hopen _ isOpen_interior) hcov
  refine ⟨⋃ h ∈ T, K (g h.1 h.2), T.isCompact_biUnion fun h _ => hKc _, fun e he => ?_⟩
  obtain ⟨h, hhT, c, hc, hce⟩ : ∃ h ∈ T, ∃ c ∈ interior (K (g h.1 h.2)), f c = f e := by
    have := hT he
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at this
    obtain ⟨h, hhT, c, hc, hce⟩ := this
    exact ⟨h, hhT, c, hc, hce⟩
  refine ⟨e * c⁻¹, c, ?_, Set.mem_biUnion hhT (interior_subset hc), by group⟩
  rw [map_mul, map_inv, hce, mul_inv_cancel]

end R1S9GL1Cob

namespace R1S9GL1Cob

open M4aHerbrand

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
  (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)

theorem locallyCompactSpace_ideles : LocallyCompactSpace (AdeleRing (𝓞 L) L)ˣ := by
  haveI : LocallyCompactSpace (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountableTopology_ideles : SecondCountableTopology (AdeleRing (𝓞 L) L)ˣ := by
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L) := NumberField.AdeleRing.secondCountableTopology L
  haveI : SecondCountableTopology (AdeleRing (𝓞 L) L)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := AdeleRing (𝓞 L) L)).symm.isInducing.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

theorem continuous_unitsAct : Continuous (D.unitsAct σ) := by
  have : (D.unitsAct σ : (AdeleRing (𝓞 L) L)ˣ → (AdeleRing (𝓞 L) L)ˣ) =
      Units.map ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom.toMonoidHom) := by
    funext u
    rfl
  rw [this]
  exact Continuous.units_map _ (D.continuous_act σ)

noncomputable def cob : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ where
  toFun e := D.unitsAct σ e * e⁻¹
  map_one' := by simp
  map_mul' a b := by
    rw [map_mul, mul_inv]
    simp only [mul_assoc, mul_left_comm (D.unitsAct σ b) a⁻¹]

theorem cob_apply (e : (AdeleRing (𝓞 L) L)ˣ) : cob K L σ D e = D.unitsAct σ e * e⁻¹ := rfl

theorem continuous_cob : Continuous (cob K L σ D) :=
  (continuous_unitsAct K L σ D).mul continuous_inv

noncomputable def cycNorm : (AdeleRing (𝓞 L) L)ˣ →* (AdeleRing (𝓞 L) L)ˣ where
  toFun w := ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) w
  map_one' := by simp
  map_mul' a b := by
    simp only [map_mul]
    exact Finset.prod_mul_distrib

theorem cycNorm_apply (w : (AdeleRing (𝓞 L) L)ˣ) :
    cycNorm K L σ D w = ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) w := rfl

theorem continuous_cycNorm : Continuous (cycNorm K L σ D) := by
  show Continuous fun w => ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) w
  exact continuous_finsetProd _ fun k _ => continuous_unitsAct K L (σ ^ k) D

theorem unitsAct_pow_succ (k : ℕ) (w : (AdeleRing (𝓞 L) L)ˣ) :
    D.unitsAct (σ ^ (k + 1)) w = D.unitsAct (σ ^ k) (D.unitsAct σ w) := by
  rw [pow_succ, map_mul, MulAut.mul_apply]

theorem cycNorm_cob (w : (AdeleRing (𝓞 L) L)ˣ) : cycNorm K L σ D (cob K L σ D w) = 1 := by
  rw [cycNorm_apply, cob_apply]
  simp only [map_mul, map_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have htel : ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) (D.unitsAct σ w) =
      ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) w := by
    have h1 := Finset.prod_range_succ (fun k => D.unitsAct (σ ^ k) w) (orderOf σ)
    have h2 := Finset.prod_range_succ' (fun k => D.unitsAct (σ ^ k) w) (orderOf σ)
    simp only [← unitsAct_pow_succ] at h2 ⊢
    rw [pow_orderOf_eq_one, pow_zero] at *
    rw [h1] at h2

    exact mul_right_cancel h2.symm
  rw [htel, mul_inv_cancel]

theorem range_cob_eq_ker : (cob K L σ D).range = (cycNorm K L σ D).ker := by
  ext u
  constructor
  · rintro ⟨w, rfl⟩
    exact cycNorm_cob K L σ D w
  · intro hu
    obtain ⟨w, hw⟩ := M4aHerbrand.IdeleGaloisDescent.exists_eq_inv_mul_unitsAct_of_prod_unitsAct_pow_eq_one K L σ D u hu
    exact ⟨w, by rw [cob_apply, hw, mul_comm]⟩

theorem gl1cob (Ω : Set (AdeleRing (𝓞 L) L)ˣ) (hΩ : IsCompact Ω) :
    ∃ C : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact C ∧
      ∀ e : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ e * e⁻¹ ∈ Ω →
        ∃ f c : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ f = f ∧ c ∈ C ∧ e = f * c := by
  haveI := locallyCompactSpace_ideles L
  haveI := secondCountableTopology_ideles L
  set N : Subgroup (AdeleRing (𝓞 L) L)ˣ := (cycNorm K L σ D).ker with hN
  have hNc : IsClosed (N : Set (AdeleRing (𝓞 L) L)ˣ) := by
    rw [hN, MonoidHom.coe_ker]
    exact isClosed_singleton.preimage (continuous_cycNorm K L σ D)
  haveI : LocallyCompactSpace N := hNc.locallyCompactSpace
  have hmem : ∀ e, cob K L σ D e ∈ N := fun e => by
    rw [hN, ← range_cob_eq_ker]
    exact ⟨e, rfl⟩
  let f : (AdeleRing (𝓞 L) L)ˣ →* N := (cob K L σ D).codRestrict N hmem
  have hfc : Continuous f := (continuous_cob K L σ D).subtype_mk _
  have hfs : Function.Surjective f := by
    rintro ⟨u, hu⟩
    have hu' : u ∈ (cob K L σ D).range := by rwa [range_cob_eq_ker]
    obtain ⟨w, rfl⟩ := hu'
    exact ⟨w, rfl⟩
  have hfo : IsOpenMap f := MonoidHom.isOpenMap_of_sigmaCompact f hfs hfc
  have hΩ' : IsCompact ((Subtype.val : N → (AdeleRing (𝓞 L) L)ˣ) ⁻¹' Ω) :=
    hNc.isClosedEmbedding_subtypeVal.isCompact_preimage hΩ
  obtain ⟨C, hC, hlift⟩ := exists_isCompact_forall_exists_eq_mul f hfo _ hΩ' (fun x _ => hfs x)
  refine ⟨C, hC, fun e he => ?_⟩
  obtain ⟨k, c, hk, hc, hekc⟩ := hlift e he
  refine ⟨k, c, ?_, hc, hekc⟩
  have hk' : cob K L σ D k = 1 := by
    have := congrArg Subtype.val hk
    exact this
  rw [cob_apply, mul_inv_eq_one] at hk'
  exact hk'

end R1S9GL1Cob

theorem solution
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (Ω : Set (AdeleRing (𝓞 L) L)ˣ) (hΩ : IsCompact Ω) :
    ∃ C : Set (AdeleRing (𝓞 L) L)ˣ, IsCompact C ∧
      ∀ e : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ e * e⁻¹ ∈ Ω →
        ∃ f c : (AdeleRing (𝓞 L) L)ˣ, D.unitsAct σ f = f ∧ c ∈ C ∧ e = f * c :=
  R1S9GL1Cob.gl1cob K L σ D Ω hΩ

end S_M4aHerbrand_IdeleGaloisDescent_exists_isCompact_forall_exists_unitsAct_eq_and_eq_mul_of_unitsAct_mul_inv_mem
end P2MW
export P2MW.S_M4aHerbrand_IdeleGaloisDescent_exists_isCompact_forall_exists_unitsAct_eq_and_eq_mul_of_unitsAct_mul_inv_mem (solution)
