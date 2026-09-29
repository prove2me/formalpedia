-- Prove2me | solution 1 for M4aKummer.normClassIndex_dvd_card_aut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a8881552-a637-5dea-89cf-b2db06e39240

import Definitions.Def_NarrowRayClassGroup
import Theorems.Thm_M4aKummer_normClassIndex_dvd_mul_of_tower
import Theorems.Thm_M4aKummer_normClassIndex_dvd_two
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.NumberTheory.RamificationInertia.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aKummer_normClassIndex_dvd_card_aut
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.primeAbove_finite instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass"
p2m_attr_erase "instance" "instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply"
p2m_attr_erase "simp" "IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff"
p2m_attr_erase "simp" "RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk"

set_option Elab.async false
set_option autoImplicit false
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Deep.NTSupply
open scoped nonZeroDivisors

noncomputable section SegNorm

namespace M4aKummer
p2m_export "M4aKummer" "normClassIndex_dvd_mul_of_tower normClassIndex_dvd_two"
namespace SolH1
p2m_open "M4aKummer"

universe u v

section TwoFields

variable (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]

abbrev nrm : (FractionalIdeal ((𝓞 E)⁰) E)ˣ →* (FractionalIdeal ((𝓞 k)⁰) k)ˣ :=
  raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
    primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal))

theorem nrm_primeUnit (w : HeightOneSpectrum (𝓞 E)) :
    nrm k E (primeUnit E w) = primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal) := by
  show raySymbol E _ ((primeUnit E w : (FractionalIdeal ((𝓞 E)⁰) E)ˣ) : FractionalIdeal ((𝓞 E)⁰) E) = _
  rw [raySymbol_primeUnit]

theorem val_finprod {ι α : Type*} [CommMonoid α] (f : ι → αˣ) (hf : Function.HasFiniteMulSupport f) :
    (((∏ᶠ i, f i : αˣ)) : α) = ∏ᶠ i, (f i : α) :=
  MonoidHom.map_finprod (Units.coeHom α) hf

theorem finprod_primeUnit_zpow_count (I : (FractionalIdeal ((𝓞 k)⁰) k)ˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 k),
        primeUnit k v ^ FractionalIdeal.count k v (I : FractionalIdeal ((𝓞 k)⁰) k) = I := by
  apply Units.ext
  rw [val_finprod _ (hasFiniteMulSupport_raySymbol_factors k (primeUnit k) _)]
  simp only [Units.val_zpow_eq_zpow_val, primeUnit_val]
  exact FractionalIdeal.finprod_heightOneSpectrum_factorization' k I.ne_zero

theorem coprimeToModulus_le_closure (𝔣 : Ideal (𝓞 k)) :
    coprimeToModulus k 𝔣 ≤ Subgroup.closure
      {I : (FractionalIdeal ((𝓞 k)⁰) k)ˣ | ∃ v : HeightOneSpectrum (𝓞 k), ¬ v.asIdeal ∣ 𝔣 ∧ I = primeUnit k v} := by
  intro I hI
  rw [← finprod_primeUnit_zpow_count k I]
  refine finprod_induction (· ∈ Subgroup.closure _) (one_mem _) (fun _ _ => mul_mem) fun v => ?_
  by_cases hv : v.asIdeal ∣ 𝔣
  · rw [(mem_coprimeToModulus_iff k).mp hI v hv, zpow_zero]
    exact one_mem _
  · have hmem : primeUnit k v ∈ ({I : (FractionalIdeal ((𝓞 k)⁰) k)ˣ |
        ∃ v : HeightOneSpectrum (𝓞 k), ¬ v.asIdeal ∣ 𝔣 ∧ I = primeUnit k v} : Set _) := ⟨v, hv, rfl⟩
    exact zpow_mem (Subgroup.subset_closure hmem) _

theorem normSub_eq_top_of_finrank_eq_one (h1 : Module.finrank k E = 1) (𝔣 : Ideal (𝓞 k)) :
    ((coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).map (nrm k E)).subgroupOf
        (coprimeToModulus k 𝔣) = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨I, hI⟩ -
  refine Subgroup.mem_subgroupOf.mpr ?_
  refine (Subgroup.closure_le _).mpr ?_ (coprimeToModulus_le_closure k 𝔣 hI)
  rintro _ ⟨v, hv, rfl⟩
  haveI := v.isMaximal
  obtain ⟨Q, hQmax, hQover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hQne : Q ≠ ⊥ := by
    intro hQ
    apply v.ne_bot
    rw [hQover.over, hQ]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 E))
  let w : HeightOneSpectrum (𝓞 E) := ⟨Q, hQmax.isPrime, hQne⟩
  have hpu : w.under (𝓞 k) = v := HeightOneSpectrum.ext hQover.over.symm
  have hw : ¬ w.asIdeal ∣ 𝔣.map (algebraMap (𝓞 k) (𝓞 E)) := by
    intro h
    apply hv
    rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at h
    rw [Ideal.dvd_iff_le, ← hpu]
    exact h
  refine ⟨primeUnit E w, primeUnit_mem_coprimeToModulus E hw, ?_⟩
  rw [nrm_primeUnit k E w]
  haveI : w.asIdeal.IsMaximal := hQmax
  haveI : w.asIdeal.LiesOver (w.under (𝓞 k)).asIdeal := ⟨rfl⟩
  haveI := (w.under (𝓞 k)).isMaximal
  haveI : NoZeroSMulDivisors (𝓞 k) (𝓞 E) := ⟨fun {c x} h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left fun hc => FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 E) (by rw [hc, map_zero])⟩
  have hle := Ideal.inertiaDeg_le_finrank (S := 𝓞 E) (K := k) (L := E) (P := w.asIdeal)
    (hp0 := (w.under (𝓞 k)).ne_bot)
  have hne := Ideal.inertiaDeg_ne_zero (w.under (𝓞 k)).asIdeal w.asIdeal
  have hf : (w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal = 1 := by omega
  rw [hf, pow_one, hpu]

end TwoFields

def normClassIdx (k : Type u) (E : Type v) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E]
    (𝔣 : Ideal (𝓞 k)) : ℕ :=
  ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
      ((coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).map
        (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
          primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
        (coprimeToModulus k 𝔣)).index

theorem normClassIdx_eq_one_of_finrank_eq_one (k : Type u) (E : Type v) [Field k] [NumberField k]
    [Field E] [NumberField E] [Algebra k E] (h1 : Module.finrank k E = 1) (𝔣 : Ideal (𝓞 k)) :
    normClassIdx k E 𝔣 = 1 := by
  unfold normClassIdx
  rw [normSub_eq_top_of_finrank_eq_one k E h1, sup_top_eq, Subgroup.index_top]

section Step

variable (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]

theorem exists_normal_subgroup_card_two (m : ℕ) (hm : Nat.card (E ≃ₐ[k] E) = 2 ^ (m + 1)) :
    ∃ H : Subgroup (E ≃ₐ[k] E), H.Normal ∧ Nat.card H = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : IsPGroup 2 (E ≃ₐ[k] E) := IsPGroup.of_card hm
  haveI : Nontrivial (E ≃ₐ[k] E) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hm]
    exact Nat.one_lt_two_pow (Nat.succ_ne_zero m)
  haveI : Nontrivial (Subgroup.center (E ≃ₐ[k] E)) := hG.center_nontrivial
  have hZ : IsPGroup 2 (Subgroup.center (E ≃ₐ[k] E)) := hG.to_subgroup _
  have h2 : 2 ∣ Nat.card (Subgroup.center (E ≃ₐ[k] E)) := by
    rcases hZ.card_eq_or_dvd with h | h
    · exact absurd h (Finite.one_lt_card.ne')
    · exact h
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨Subgroup.zpowers (c : E ≃ₐ[k] E), ⟨fun h hh g => ?_⟩, ?_⟩
  · have hcen : h ∈ Subgroup.center (E ≃ₐ[k] E) := (Subgroup.zpowers_le.mpr c.2) hh
    rw [(Subgroup.mem_center_iff.mp hcen g), mul_inv_cancel_right]
    exact hh
  · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hc]

end Step

theorem normClassIdx_dvd_two_pow (k : Type u) [Field k] [NumberField k] :
    ∀ (m : ℕ) (E : Type v) [Field E] [NumberField E] [Algebra k E] [IsGalois k E],
      Nat.card (E ≃ₐ[k] E) = 2 ^ m → ∀ 𝔣 : Ideal (𝓞 k), normClassIdx k E 𝔣 ∣ 2 ^ m := by
  intro m
  induction m with
  | zero =>
    intro E _ _ _ _ hcard 𝔣
    have h1 : Module.finrank k E = 1 := by rw [← IsGalois.card_aut_eq_finrank, hcard, pow_zero]
    rw [normClassIdx_eq_one_of_finrank_eq_one k E h1 𝔣, pow_zero]
  | succ m ih =>
    intro E _ _ _ _ hcard 𝔣
    obtain ⟨H, hN, hH2⟩ := exists_normal_subgroup_card_two k E m hcard
    haveI := hN
    haveI : IsGalois k (IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
    have hME : Module.finrank (IntermediateField.fixedField H) E = 2 := by
      rw [IntermediateField.finrank_fixedField_eq_card]; exact hH2
    have htot : Module.finrank k E = 2 ^ (m + 1) := by rw [← IsGalois.card_aut_eq_finrank, hcard]
    have hcardM : Nat.card ((IntermediateField.fixedField H) ≃ₐ[k] (IntermediateField.fixedField H)) = 2 ^ m := by
      rw [IsGalois.card_aut_eq_finrank]
      have hmul := Module.finrank_mul_finrank k (IntermediateField.fixedField H) E
      rw [hME, htot, pow_succ] at hmul
      exact Nat.eq_of_mul_eq_mul_right two_pos hmul
    have h3 : normClassIdx k E 𝔣 ∣ normClassIdx k (IntermediateField.fixedField H) 𝔣 *
        normClassIdx (IntermediateField.fixedField H) E
          (𝔣.map (algebraMap (𝓞 k) (𝓞 (IntermediateField.fixedField H)))) :=
      M4aKummer.normClassIndex_dvd_mul_of_tower k (IntermediateField.fixedField H) E 𝔣
    have h2 : normClassIdx (IntermediateField.fixedField H) E
        (𝔣.map (algebraMap (𝓞 k) (𝓞 (IntermediateField.fixedField H)))) ∣ 2 :=
      M4aKummer.normClassIndex_dvd_two (IntermediateField.fixedField H) E hME _
    calc normClassIdx k E 𝔣
        ∣ normClassIdx k (IntermediateField.fixedField H) 𝔣 *
            normClassIdx (IntermediateField.fixedField H) E
              (𝔣.map (algebraMap (𝓞 k) (𝓞 (IntermediateField.fixedField H)))) := h3
      _ ∣ 2 ^ m * 2 := mul_dvd_mul (ih (IntermediateField.fixedField H) hcardM 𝔣) h2
      _ = 2 ^ (m + 1) := (pow_succ 2 m).symm

end M4aKummer.SolH1

end SegNorm

open NumberField IsDedekindDomain Deep.NTSupply

theorem solution
    (k E : Type*) [Field k] [NumberField k] [Field E] [NumberField E] [Algebra k E] [IsGalois k E]
    (m : ℕ) (hm : Nat.card (E ≃ₐ[k] E) = 2 ^ m) (𝔣 : Ideal (𝓞 k)) :
    ((narrowRaySubgroup k 𝔣).subgroupOf (coprimeToModulus k 𝔣) ⊔
      ((coprimeToModulus E (𝔣.map (algebraMap (𝓞 k) (𝓞 E)))).map
        (raySymbolUnitsHom E (fun w : HeightOneSpectrum (𝓞 E) =>
          primeUnit k (w.under (𝓞 k)) ^ ((w.under (𝓞 k)).asIdeal.inertiaDeg' w.asIdeal)))).subgroupOf
        (coprimeToModulus k 𝔣)).index ∣ Nat.card (E ≃ₐ[k] E) := by
  rw [hm]
  exact M4aKummer.SolH1.normClassIdx_dvd_two_pow k m E hm 𝔣

#print axioms solution

end S_M4aKummer_normClassIndex_dvd_card_aut
end P2MW
export P2MW.S_M4aKummer_normClassIndex_dvd_card_aut (solution)
