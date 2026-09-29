-- Prove2me | solution 1 for M4aHerbrand.AdeleBaseChange.isOpen_range_idelicNorm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/11424101-617f-555b-ba45-fd3ef8959378

import Mathlib
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_TaylorWiles_Primes
import Theorems.Thm_M4aHerbrand_AdeleBaseChange_ideleBox_le_range_idelicNorm
import Theorems.Thm_NumberField_isOpen_range_powMonoidHom_units_adicCompletion
import Theorems.Thm_NumberField_InfinitePlace_isOpen_range_powMonoidHom_units_completion
import Theorems.Thm_LanglandsTunnell_exists_finset_forall_inertia_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_AdeleBaseChange_isOpen_range_idelicNorm
p2m_attr_erase "instance" "FLT.InfiniteAdeleBaseChange.uniqueSelfExtension NumberField.InfinitePlace.RamifiedExtension.instCoeExtension NumberField.InfinitePlace.UnramifiedExtension.instCoeExtension IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion M4aHerbrand.Bridge.instT2SpaceAdeleRing instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.ArchSemilocal.psiFactor_tmul M4aHerbrand.ArchSemilocal.psi_apply FLT.InfiniteAdeleBaseChange.evalAlgHom_apply FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_tmul_apply FLT.InfiniteAdeleBaseChange.collapsePlaces_apply FLT.InfiniteAdeleBaseChange.tensorPiAlgEquiv_tmul_apply FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.sizeOf_spec FLT.InfiniteAdeleBaseChange.InfinitePlaceData.mk.injEq FLT.InfiniteAdeleBaseChange.BaseChangeData.mk.injEq M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe"
p2m_attr_erase "simp" "Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open NumberField IsDedekindDomain FrobeniusDensity
open scoped Topology

namespace R2FafNAOpen

section RatPrime

variable (K : Type) [Field K] [NumberField K]

omit [NumberField K] in

theorem exists_liesOver_ratPrimeIdeal (v : HeightOneSpectrum (𝓞 K)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.asIdeal.LiesOver (ratPrimeIdeal ℓ) := by
  have hprime : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  rcases Ideal.isPrime_int_iff.1 hprime with h | ⟨p, hp, hpe⟩
  · exact absurd (Ideal.eq_bot_of_comap_eq_bot h) v.ne_bot
  · exact ⟨p, hp, ⟨hpe.symm⟩⟩

end RatPrime

section Ramification

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem restrictScalars_smul (σ : L ≃ₐ[K] L) (x : 𝓞 L) :
    (σ.restrictScalars ℚ) • x = σ • x := by
  ext
  rfl

theorem inertia_eq_bot_of_rat (Q : Ideal (𝓞 L)) (hQ : Q.inertia (L ≃ₐ[ℚ] L) = ⊥) :
    Q.inertia (L ≃ₐ[K] L) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  have h1 : σ.restrictScalars ℚ ∈ Q.inertia (L ≃ₐ[ℚ] L) := by
    intro x
    rw [restrictScalars_smul]
    exact hσ x
  rw [hQ, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  apply AlgEquiv.restrictScalars_injective ℚ
  rw [h1]
  rfl

theorem exists_finset_forall_extension_inertia_eq_bot :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ S, ∀ w : v.Extension (𝓞 L),
      w.1.asIdeal.inertia (L ≃ₐ[K] L) = ⊥ := by
  classical
  obtain ⟨B, hB⟩ := LanglandsTunnell.exists_finset_forall_inertia_eq_bot L

  let T : Set (HeightOneSpectrum (𝓞 K)) :=
    {v | ∃ ℓ ∈ B, ℓ.Prime ∧ v.asIdeal.LiesOver (ratPrimeIdeal ℓ)}
  have hT : T.Finite := by
    have hsub : T ⊆ ⋃ ℓ ∈ B, {v : HeightOneSpectrum (𝓞 K) | ℓ.Prime ∧
        v ∈ (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) ⁻¹' ((ratPrimeIdeal ℓ).primesOver (𝓞 K))} := by
      rintro v ⟨ℓ, hℓB, hℓ, hover⟩
      exact Set.mem_biUnion hℓB ⟨hℓ, ⟨v.isPrime, hover⟩⟩
    refine Set.Finite.subset (Set.Finite.biUnion B.finite_toSet fun ℓ _ => ?_) hsub
    by_cases hℓ : ℓ.Prime
    · haveI := Fact.mk hℓ
      exact (Set.Finite.preimage (fun x _ y _ hxy => HeightOneSpectrum.ext hxy)
        (IsDedekindDomain.primesOver_finite (ratPrimeIdeal ℓ) (𝓞 K))).subset fun v hv => hv.2
    · exact Set.finite_empty.subset fun v hv => absurd hv.1 hℓ
  refine ⟨hT.toFinset, fun v hv w => ?_⟩
  rw [Set.Finite.mem_toFinset] at hv
  obtain ⟨ℓ, hℓ, hover⟩ := exists_liesOver_ratPrimeIdeal K v
  have hℓB : ℓ ∉ B := fun h => hv ⟨ℓ, h, hℓ, hover⟩
  haveI := hover

  have hw : w.1.asIdeal.under (𝓞 K) = v.asIdeal := by
    rw [← HeightOneSpectrum.under_asIdeal, w.2]
  haveI : w.1.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  haveI : w.1.asIdeal.LiesOver (ratPrimeIdeal ℓ) := Ideal.LiesOver.trans w.1.asIdeal v.asIdeal _
  exact inertia_eq_bot_of_rat K L _ (hB hℓ hℓB w.1.asIdeal w.1.isPrime inferInstance)

end Ramification

section Box

variable (K : Type) [Field K] [NumberField K]

theorem continuous_finiteUnitsComponent (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v) := by
  show Continuous ((IsDedekindDomain.FiniteAdeleRing.unitsComponent (𝓞 K) K v) ∘
    (NumberField.AdeleRing.finitePartUnits (𝓞 K) K))
  refine Continuous.comp ?_ ?_
  · exact Continuous.units_map _ (RestrictedProduct.continuous_eval v)
  · exact Continuous.units_map _ continuous_snd

theorem continuous_infiniteUnitsComponent (w : InfinitePlace K) :
    Continuous (NumberField.AdeleRing.infiniteUnitsComponent (𝓞 K) K w) :=
  Continuous.units_map _ ((continuous_apply w).comp continuous_fst)

theorem isOpen_setOf_forall_not_mem_integer (S : Set (HeightOneSpectrum (𝓞 K))) :
    IsOpen {f : FiniteAdeleRing (𝓞 K) K | ∀ v, v ∉ S → f v ∈ v.adicCompletionIntegers K} :=
  RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum (𝓞 K) => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    (fun _ => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ S)

theorem ideleBox_mem_nhds_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (H : (v : HeightOneSpectrum (𝓞 K)) → Subgroup (v.adicCompletion K)ˣ)
    (Hinf : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ)
    (hH : ∀ v ∈ S, IsOpen (H v : Set (v.adicCompletion K)ˣ))
    (hHinf : ∀ w, IsOpen (Hinf w : Set (w.Completion)ˣ)) :
    (NumberField.AdeleRing.ideleBox (𝓞 K) K ↑S H Hinf : Set (AdeleRing (𝓞 K) K)ˣ) ∈
      𝓝 (1 : (AdeleRing (𝓞 K) K)ˣ) := by

  let U : Set (FiniteAdeleRing (𝓞 K) K) :=
    {f | ∀ v, v ∉ (↑S : Set (HeightOneSpectrum (𝓞 K))) → f v ∈ v.adicCompletionIntegers K}
  have hU : IsOpen U := isOpen_setOf_forall_not_mem_integer K ↑S
  let W : Set (AdeleRing (𝓞 K) K)ˣ :=
    ((fun x : (AdeleRing (𝓞 K) K)ˣ => ((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K)) ⁻¹' U ∩
      (fun x : (AdeleRing (𝓞 K) K)ˣ => (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 :
        FiniteAdeleRing (𝓞 K) K)) ⁻¹' U) ∩
    ((⋂ v ∈ S, (NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v) ⁻¹' (H v : Set _)) ∩
      ⋂ w : InfinitePlace K, (NumberField.AdeleRing.infiniteUnitsComponent (𝓞 K) K w) ⁻¹' (Hinf w : Set _))
  have hc1 : Continuous fun x : (AdeleRing (𝓞 K) K)ˣ =>
      ((x : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) :=
    continuous_snd.comp Units.continuous_val
  have hc2 : Continuous fun x : (AdeleRing (𝓞 K) K)ˣ =>
      (((x⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) :=
    continuous_snd.comp (Units.continuous_val.comp continuous_inv)
  have hW : IsOpen W := by
    refine ((hU.preimage hc1).inter (hU.preimage hc2)).inter (IsOpen.inter ?_ ?_)
    · exact isOpen_biInter_finset fun v hv =>
        (hH v hv).preimage (continuous_finiteUnitsComponent K v)
    · exact isOpen_iInter_of_finite fun w =>
        (hHinf w).preimage (continuous_infiniteUnitsComponent K w)
  have h1W : (1 : (AdeleRing (𝓞 K) K)ˣ) ∈ W := by
    refine ⟨⟨fun v _ => ?_, fun v _ => ?_⟩, ⟨Set.mem_iInter₂.2 fun v _ => ?_, Set.mem_iInter.2 fun w => ?_⟩⟩
    · change (1 : v.adicCompletion K) ∈ v.adicCompletionIntegers K
      exact one_mem _
    · show ((((1 : (AdeleRing (𝓞 K) K)ˣ)⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 :
        FiniteAdeleRing (𝓞 K) K) v ∈ _
      rw [inv_one]
      change (1 : v.adicCompletion K) ∈ v.adicCompletionIntegers K
      exact one_mem _
    · show NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v 1 ∈ (H v : Set _)
      rw [map_one]; exact one_mem _
    · show NumberField.AdeleRing.infiniteUnitsComponent (𝓞 K) K w 1 ∈ (Hinf w : Set _)
      rw [map_one]; exact one_mem _
  have hWbox : W ⊆ (NumberField.AdeleRing.ideleBox (𝓞 K) K ↑S H Hinf : Set (AdeleRing (𝓞 K) K)ˣ) := by
    rintro x ⟨⟨hx1, hx2⟩, ⟨hx3, hx4⟩⟩
    rw [SetLike.mem_coe, NumberField.AdeleRing.mem_ideleBox_iff]
    refine ⟨⟨fun v hv => Set.mem_iInter₂.1 hx3 v hv, fun v hv => ⟨hx1 v hv, hx2 v hv⟩⟩,
      fun w => Set.mem_iInter.1 hx4 w⟩
  exact Filter.mem_of_superset (hW.mem_nhds h1W) hWbox

end Box

end R2FafNAOpen

open R2FafNAOpen M4aHerbrand in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) :
    IsOpen (Set.range B.idelicNorm) := by
  classical

  set n : ℕ := Module.finrank K L with hn
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  have hnpos : 0 < n := Module.finrank_pos
  obtain ⟨S, hS⟩ := exists_finset_forall_extension_inertia_eq_bot K L

  let H : (v : HeightOneSpectrum (𝓞 K)) → Subgroup (v.adicCompletion K)ˣ :=
    fun v => (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range
  let Hinf : (w : InfinitePlace K) → Subgroup (w.Completion)ˣ :=
    fun w => (powMonoidHom n : (w.Completion)ˣ →* (w.Completion)ˣ).range
  have hbox : NumberField.AdeleRing.ideleBox (𝓞 K) K ↑S H Hinf ≤ B.idelicNorm.range :=
    M4aHerbrand.AdeleBaseChange.ideleBox_le_range_idelicNorm K L B (dvd_refl n) S H Hinf
      (fun v _ => Or.inl le_rfl) hS (fun w _ => le_rfl)
  have hnhds := ideleBox_mem_nhds_one K S H Hinf
    (fun v _ => NumberField.isOpen_range_powMonoidHom_units_adicCompletion v hnpos)
    (fun w => NumberField.InfinitePlace.isOpen_range_powMonoidHom_units_completion w hnpos)
  have hopen : IsOpen (B.idelicNorm.range : Set (AdeleRing (𝓞 K) K)ˣ) :=
    Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset hnhds hbox)
  rwa [MonoidHom.coe_range] at hopen

end S_M4aHerbrand_AdeleBaseChange_isOpen_range_idelicNorm
end P2MW
export P2MW.S_M4aHerbrand_AdeleBaseChange_isOpen_range_idelicNorm (solution)
