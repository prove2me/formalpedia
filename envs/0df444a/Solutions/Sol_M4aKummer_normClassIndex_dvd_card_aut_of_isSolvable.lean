-- Prove2me | solution 1 for M4aKummer.normClassIndex_dvd_card_aut_of_isSolvable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/424b2711-4940-509d-8a78-ef8db09e7e73

import Definitions.Def_NarrowRayClassGroup
import Theorems.Thm_M4aKummer_normClassIndex_dvd_card_aut_of_prime_pow
import Theorems.Thm_M4aKummer_normClassIndex_dvd_mul_of_tower
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.QuotientGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aKummer_normClassIndex_dvd_card_aut_of_isSolvable
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap"
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id"
p2m_attr_erase "simp" "TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply

universe u v

private def NormClassIndexDvdCard (k : Type u) (E : Type v) [Field k] [NumberField k] [Field E] [NumberField E]
    [Algebra k E] (𝔣 : Ideal (𝓞 k)) : Prop :=
  ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
      ((coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).map
        (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
          primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
        (coprimeToModulus k 𝔣)).index ∣ Nat.card (E ≃ₐ[k] E)

private theorem isPrimePow_card_or_exists_normal_ne (G : Type*) [Group G] [Finite G] [Group.IsSolvable G] :
    (∃ p m : ℕ, p.Prime ∧ Nat.card G = p ^ m) ∨ ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  by_cases hpp : ∃ p m : ℕ, p.Prime ∧ Nat.card G = p ^ m
  · exact Or.inl hpp
  right
  by_cases hc : commutator G = ⊥
  · haveI : IsMulCommutative G := (commutator_eq_bot_iff G).mp hc
    have h1 : Nat.card G ≠ 1 := fun h => hpp ⟨2, 0, Nat.prime_two, by rw [h, pow_zero]⟩
    have hp : (Nat.card G).minFac.Prime := Nat.minFac_prime h1
    haveI : Fact (Nat.card G).minFac.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (Nat.card G).minFac (Nat.minFac_dvd (Nat.card G))
    refine ⟨Subgroup.zpowers g, inferInstance, ?_, ?_⟩
    · intro hbot
      have hmem := Subgroup.mem_zpowers g
      rw [hbot] at hmem
      have hg1 : g = 1 := Subgroup.mem_bot.mp hmem
      rw [hg1, orderOf_one] at hg
      exact hp.one_lt.ne hg
    · intro htop
      exact hpp ⟨(Nat.card G).minFac, 1, hp, by rw [pow_one, ← hg, ← Nat.card_zpowers, htop, Subgroup.card_top]⟩
  · haveI : Nontrivial G := by
      rcases subsingleton_or_nontrivial G with h | h
      · exact absurd ((commutator_eq_bot_iff G).mpr ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩) hc
      · exact h
    exact ⟨commutator G, inferInstance, hc, (Group.IsSolvable.commutator_lt_top_of_nontrivial G).ne⟩

section Layer

variable (k : Type u) (E : Type v) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
  (N : Subgroup (E ≃ₐ[k] E))

private theorem card_aut_eq_card_aut_fixedField_mul [IsGalois k E] [N.Normal] :
    Nat.card (E ≃ₐ[k] E) =
      Nat.card (IntermediateField.fixedField N ≃ₐ[k] IntermediateField.fixedField N) *
        Nat.card (E ≃ₐ[IntermediateField.fixedField N] E) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N,
    Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv,
    Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv N).toEquiv]

private theorem one_lt_card_aut_fixedField [IsGalois k E] [N.Normal] (htop : N ≠ ⊤) :
    1 < Nat.card (IntermediateField.fixedField N ≃ₐ[k] IntermediateField.fixedField N) := by
  rw [← Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv, ← Subgroup.index_eq_card]
  exact Subgroup.one_lt_index_of_ne_top htop

private theorem one_lt_card_aut_of_fixedField (hbot : N ≠ ⊥) :
    1 < Nat.card (E ≃ₐ[IntermediateField.fixedField N] E) := by
  rw [← Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv N).toEquiv]
  exact (Subgroup.one_lt_card_iff_ne_bot N).mpr hbot

private theorem isSolvable_aut_fixedField [IsGalois k E] [N.Normal] [Group.IsSolvable (E ≃ₐ[k] E)] :
    Group.IsSolvable (IntermediateField.fixedField N ≃ₐ[k] IntermediateField.fixedField N) :=
  solvable_of_surjective (f := (IsGalois.normalAutEquivQuotient N).toMonoidHom)
    (IsGalois.normalAutEquivQuotient N).surjective

private theorem isSolvable_aut_of_fixedField [Group.IsSolvable (E ≃ₐ[k] E)] :
    Group.IsSolvable (E ≃ₐ[IntermediateField.fixedField N] E) :=
  solvable_of_surjective (f := (IntermediateField.subgroupEquivAlgEquiv N).toMonoidHom)
    (IntermediateField.subgroupEquivAlgEquiv N).surjective

private theorem normClassIndexDvdCard_of_fixedField [IsGalois k E] [N.Normal] (𝔣 : Ideal (𝓞 k))
    (h₁ : NormClassIndexDvdCard k (IntermediateField.fixedField N) 𝔣)
    (h₂ : NormClassIndexDvdCard (IntermediateField.fixedField N) E
      (𝔣.map (algebraMap (𝓞 k) (𝓞 (IntermediateField.fixedField N))))) :
    NormClassIndexDvdCard k E 𝔣 := by
  unfold NormClassIndexDvdCard at h₁ h₂ ⊢
  rw [card_aut_eq_card_aut_fixedField_mul k E N]
  exact (M4aKummer.normClassIndex_dvd_mul_of_tower k (IntermediateField.fixedField N) E 𝔣).trans
    (Nat.mul_dvd_mul h₁ h₂)

end Layer

private theorem normClassIndexDvdCard_of_card_eq (n : ℕ) :
    ∀ (k E : Type v) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E] [IsGalois k E]
      [Group.IsSolvable (E ≃ₐ[k] E)] (𝔣 : Ideal (𝓞 k)), Nat.card (E ≃ₐ[k] E) = n → NormClassIndexDvdCard k E 𝔣 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k E _ _ _ _ _ _ _ 𝔣 hn
    rcases isPrimePow_card_or_exists_normal_ne (E ≃ₐ[k] E) with ⟨p, m, hp, hm⟩ | ⟨N, hN, hbot, htop⟩
    · exact M4aKummer.normClassIndex_dvd_card_aut_of_prime_pow k E p hp m hm 𝔣
    · haveI := hN
      haveI := isSolvable_aut_fixedField k E N
      haveI := isSolvable_aut_of_fixedField k E N
      have hmul := card_aut_eq_card_aut_fixedField_mul k E N
      refine normClassIndexDvdCard_of_fixedField k E N 𝔣 ?_ ?_
      · refine ih _ ?_ k (IntermediateField.fixedField N) 𝔣 rfl
        rw [← hn, hmul]
        exact lt_mul_of_one_lt_right Nat.card_pos (one_lt_card_aut_of_fixedField k E N hbot)
      · refine ih _ ?_ (IntermediateField.fixedField N) E _ rfl
        rw [← hn, hmul]
        exact lt_mul_of_one_lt_left Nat.card_pos (one_lt_card_aut_fixedField k E N htop)

private theorem normClassIndexDvdCard_of_card_eq' (n : ℕ) :
    ∀ (k : Type u) (E : Type v) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E] [IsGalois k E]
      [Group.IsSolvable (E ≃ₐ[k] E)] (𝔣 : Ideal (𝓞 k)), Nat.card (E ≃ₐ[k] E) = n → NormClassIndexDvdCard k E 𝔣 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro k E _ _ _ _ _ _ _ 𝔣 hn
    rcases isPrimePow_card_or_exists_normal_ne (E ≃ₐ[k] E) with ⟨p, m, hp, hm⟩ | ⟨N, hN, hbot, _⟩
    · exact M4aKummer.normClassIndex_dvd_card_aut_of_prime_pow k E p hp m hm 𝔣
    · haveI := hN
      haveI := isSolvable_aut_fixedField k E N
      haveI := isSolvable_aut_of_fixedField k E N
      have hmul := card_aut_eq_card_aut_fixedField_mul k E N
      refine normClassIndexDvdCard_of_fixedField k E N 𝔣 ?_ ?_
      · refine ih _ ?_ k (IntermediateField.fixedField N) 𝔣 rfl
        rw [← hn, hmul]
        exact lt_mul_of_one_lt_right Nat.card_pos (one_lt_card_aut_of_fixedField k E N hbot)
      · exact normClassIndexDvdCard_of_card_eq _ (IntermediateField.fixedField N) E _ rfl

theorem solution
    (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E] [IsGalois k E]
    [Group.IsSolvable (E ≃ₐ[k] E)] (𝔣 : Ideal (𝓞 k)) :
    ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
      ((coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).map
        (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
          primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
        (coprimeToModulus k 𝔣)).index ∣ Nat.card (E ≃ₐ[k] E) := by
  exact normClassIndexDvdCard_of_card_eq' _ k E 𝔣 rfl

end S_M4aKummer_normClassIndex_dvd_card_aut_of_isSolvable
end P2MW
export P2MW.S_M4aKummer_normClassIndex_dvd_card_aut_of_isSolvable (solution)
