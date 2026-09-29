-- Prove2me | solution 1 for LanglandsTunnell.CubicLambda.localChar_comp_idelicArtinMap_eq_one_of_mem_higherUnitsAt_of_factorization_discr_le_of_prime_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/63f3aee9-0a02-5ec6-a275-66c6d0ebd07a

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Theorems.Thm_M4aHerbrand_idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow
import Theorems.Thm_ArtinL_Abelian_forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le
import Theorems.Thm_NumberField_card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicLambda_localChar_comp_idelicArtinMap_eq_one_of_mem_higherUnitsAt_of_factorization_discr_le_of_prime_finrank
p2m_attr_erase "instance" "FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite"
p2m_attr_erase "instance" "LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl Rep.coe_invariantsMap_apply Rep.tateH0Map_mk"
p2m_attr_erase "simp" "Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

namespace X1bAux

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin ArtinL.Abelian

section Finiteness

variable {F : Type} [Field F] [NumberField F]

theorem exists_smul_ne_of_ne_one (σ : F ≃ₐ[ℚ] F) (hσ : σ ≠ 1) : ∃ x : 𝓞 F, σ • x ≠ x := by
  by_contra h
  push_neg at h
  apply hσ
  ext z
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) z
  have ha : σ (algebraMap (𝓞 F) F a) = algebraMap (𝓞 F) F a := by
    have := congrArg (algebraMap (𝓞 F) F) (h a)
    exact this
  have hb : σ (algebraMap (𝓞 F) F b) = algebraMap (𝓞 F) F b := by
    have := congrArg (algebraMap (𝓞 F) F) (h b)
    exact this
  rw [map_div₀, ha, hb, AlgEquiv.one_apply]

theorem exists_forall_inertia_pow_eq_bot (P : Ideal (𝓞 F)) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ N : ℕ, ∀ i : ℕ, N ≤ i → (P ^ (i + 1)).inertia (F ≃ₐ[ℚ] F) = ⊥ := by
  classical
  have key : ∀ σ : F ≃ₐ[ℚ] F, ∃ n : ℕ, σ ≠ 1 → ∀ i : ℕ, n ≤ i →
      σ ∉ (P ^ (i + 1)).inertia (F ≃ₐ[ℚ] F) := by
    intro σ
    by_cases hσ : σ = 1
    · exact ⟨0, fun h => (h hσ).elim⟩
    obtain ⟨x, hx⟩ := exists_smul_ne_of_ne_one σ hσ
    have hy : Ideal.span {σ • x - x} ≠ (⊥ : Ideal (𝓞 F)) := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact sub_ne_zero.mpr hx
    have hfin : FiniteMultiplicity P (Ideal.span {σ • x - x}) :=
      FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime hP ‹_›) hy
    obtain ⟨n, hn⟩ := hfin
    refine ⟨n, fun _ i hi hmem => hn ?_⟩
    rw [Ideal.dvd_span_singleton]
    have h1 : σ • x - x ∈ P ^ (i + 1) := AddSubgroup.mem_inertia.mp hmem x
    exact Ideal.pow_le_pow_right (by omega) h1
  choose n hn using key
  obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
  refine ⟨N, fun i hi => ?_⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  by_contra hne
  exact hn σ hne i (le_trans (hN ⟨σ, rfl⟩) hi) hσ

end Finiteness

section Bound

variable (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]

theorem ramificationGroup_le_inertiaGroup (v : HeightOneSpectrum (𝓞 ℚ)) (i : ℕ) :
    ramificationGroup ℚ F v i ≤ inertiaGroup ℚ F v := by
  intro σ hσ
  rw [ramificationGroup] at hσ
  rw [inertiaGroup]
  refine AddSubgroup.mem_inertia.mpr fun x => ?_
  exact Ideal.pow_le_self (by omega) (AddSubgroup.mem_inertia.mp hσ x)

theorem conductorExponent_le_finsum (χ : (F ≃ₐ[ℚ] F) →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    conductorExponent χ v ≤ ∑ᶠ j : ℕ, (Nat.card (ramificationGroup ℚ F v j) - 1) := by
  classical
  obtain ⟨N, hN⟩ := exists_forall_inertia_pow_eq_bot (F := F) (primeAbove ℚ F v) (primeAbove_ne_bot ℚ F v)
  have hN' : ∀ i : ℕ, N ≤ i → ramificationGroup ℚ F v i = ⊥ := fun i hi => hN i hi
  have hsuppA : (Function.support fun j : ℕ => Nat.card (ramificationGroup ℚ F v j) - 1) ⊆
      ((Finset.range (N + 1) : Finset ℕ) : Set ℕ) := by
    intro j hj
    rw [Function.mem_support] at hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    push_neg at h
    exact hj (by rw [hN' j (by omega), Subgroup.card_bot, Nat.sub_self])
  rw [finsum_eq_sum_of_support_subset _ hsuppA, Finset.sum_range_succ', add_comm, conductorExponent]
  refine add_le_add ?_ ?_
  ·
    split_ifs with hunr
    · exact Nat.zero_le _
    · have hex : ∃ σ ∈ inertiaGroup ℚ F v, χ σ ≠ 1 := by
        simpa [IsUnramifiedAt] using hunr
      obtain ⟨σ, hσ, hχσ⟩ := hex
      have hσ1 : σ ≠ 1 := fun h => hχσ (by rw [h, map_one])
      have hmem : σ ∈ ramificationGroup ℚ F v 0 := by rwa [ramificationGroup_zero]
      have hne : ramificationGroup ℚ F v 0 ≠ ⊥ := fun h => hσ1 (by rw [h] at hmem; exact hmem)
      have h2 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
      omega
  ·
    rw [Nat.ceil_le, Nat.cast_sum, swanConductor]
    have hsuppC : (Function.support fun i : ℕ =>
        (Nat.card (ramificationGroup ℚ F v (i + 1)) : ℚ) / (Nat.card (inertiaGroup ℚ F v) : ℚ) *
          (if ∀ σ ∈ ramificationGroup ℚ F v (i + 1), χ σ = 1 then 0 else 1)) ⊆
        ((Finset.range N : Finset ℕ) : Set ℕ) := by
      intro i hi
      rw [Function.mem_support] at hi
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      push_neg at h
      apply hi
      have hbot : ramificationGroup ℚ F v (i + 1) = ⊥ := hN' (i + 1) (by omega)
      rw [if_pos (fun σ hσ => by rw [hbot] at hσ; rw [Subgroup.mem_bot.mp hσ, map_one]), mul_zero]
    rw [finsum_eq_sum_of_support_subset _ hsuppC]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with htriv
    · rw [mul_zero]; exact Nat.cast_nonneg _
    · rw [mul_one]
      have hne : ramificationGroup ℚ F v (i + 1) ≠ ⊥ := by
        intro h
        exact htriv fun σ hσ => by rw [h] at hσ; rw [Subgroup.mem_bot.mp hσ, map_one]
      have h2 : 1 < Nat.card (ramificationGroup ℚ F v (i + 1)) :=
        (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
      have hle : Nat.card (ramificationGroup ℚ F v (i + 1)) ≤ Nat.card (inertiaGroup ℚ F v) :=
        Subgroup.card_le_of_le (ramificationGroup_le_inertiaGroup F v (i + 1))
      have hpos : (0 : ℚ) < (Nat.card (inertiaGroup ℚ F v) : ℚ) := by
        exact_mod_cast lt_of_lt_of_le (lt_trans zero_lt_one h2) hle
      calc (Nat.card (ramificationGroup ℚ F v (i + 1)) : ℚ) / (Nat.card (inertiaGroup ℚ F v) : ℚ)
          ≤ 1 := (div_le_one hpos).mpr (by exact_mod_cast hle)
        _ ≤ ((Nat.card (ramificationGroup ℚ F v (i + 1)) - 1 : ℕ) : ℚ) := by
          exact_mod_cast Nat.le_sub_one_of_lt h2

noncomputable def fixedFieldBotEquiv :
    ↥(IntermediateField.fixedField (⊥ : Subgroup (F ≃ₐ[ℚ] F))) ≃ₐ[ℚ] F :=
  (IntermediateField.equivOfEq (IntermediateField.fixedField_bot (F := ℚ) (E := F))).trans
    IntermediateField.topEquiv

theorem finsum_le_factorization (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) (hp : p.Prime)
    (hP : (primeAbove ℚ F v).under ℤ = Ideal.span {(p : ℤ)}) :
    ∑ᶠ j : ℕ, (Nat.card (ramificationGroup ℚ F v j) - 1) ≤ (discr F).natAbs.factorization p := by
  classical
  have H := NumberField.card_mul_factorization_discr_fixedField_eq_inertiaDeg_mul_finsum_u0 F ⊥ p hp
    (primeAbove ℚ F v) hP
  rw [Subgroup.card_bot, one_mul, NumberField.discr_eq_discr_of_algEquiv _ (fixedFieldBotEquiv F)] at H
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  haveI : (primeAbove ℚ F v).LiesOver (Ideal.span {(p : ℤ)}) := ⟨hP.symm⟩
  haveI : Finite ↥((Ideal.span {(p : ℤ)}).primesOver (𝓞 F)) :=
    (IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) (𝓞 F)).to_subtype
  have hf : 0 < (Ideal.span {(p : ℤ)}).inertiaDeg' (primeAbove ℚ F v) := Ideal.inertiaDeg'_pos _ _
  let 𝔓₀ : ↥((Ideal.span {(p : ℤ)}).primesOver (𝓞 F)) :=
    ⟨primeAbove ℚ F v, inferInstance, inferInstance⟩
  simp only [inf_bot_eq, Subgroup.card_bot] at H
  rw [H]
  calc ∑ᶠ j : ℕ, (Nat.card (ramificationGroup ℚ F v j) - 1)
      = ∑ᶠ j : ℕ, (Nat.card (((𝔓₀ : Ideal (𝓞 F)) ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) - 1) := rfl
    _ ≤ ∑ᶠ 𝔔 : ↥((Ideal.span {(p : ℤ)}).primesOver (𝓞 F)),
          ∑ᶠ j : ℕ, (Nat.card (((𝔔 : Ideal (𝓞 F)) ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) - 1) :=
        single_le_finsum (f := fun 𝔔 : ↥((Ideal.span {(p : ℤ)}).primesOver (𝓞 F)) =>
          ∑ᶠ j : ℕ, (Nat.card (((𝔔 : Ideal (𝓞 F)) ^ (j + 1)).inertia (F ≃ₐ[ℚ] F)) - 1))
          𝔓₀ (Set.toFinite _) (fun _ => Nat.zero_le _)
    _ ≤ _ := Nat.le_mul_of_pos_left _ hf

theorem conductorExponent_le_factorization_discr (χ : (F ≃ₐ[ℚ] F) →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    conductorExponent χ v ≤ (discr F).natAbs.factorization (Ideal.absNorm v.asIdeal) := by
  obtain ⟨p, hp, hv⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat v
  have habs : Ideal.absNorm v.asIdeal = p := by
    rw [hv, Ideal.absNorm_span_singleton]
    have : ((p : ℕ) : 𝓞 ℚ) = algebraMap ℤ (𝓞 ℚ) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self, pow_one,
      Int.natAbs_natCast]
  have hunder : (primeAbove ℚ F v).under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← Ideal.under_under (B := 𝓞 ℚ), under_primeAbove, hv]
    haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
        (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
    refine (hmax.eq_of_le ?_ ?_).symm
    · haveI : (Ideal.span {((p : ℕ) : 𝓞 ℚ)}).IsPrime := hv ▸ v.isPrime
      exact Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      have : algebraMap ℤ (𝓞 ℚ) (p : ℤ) = ((p : ℕ) : 𝓞 ℚ) := by simp
      rw [this]
      exact Ideal.mem_span_singleton_self _
  rw [habs]
  exact (conductorExponent_le_finsum F χ v).trans (finsum_le_factorization F v p hp hunder)

end Bound

end X1bAux

namespace X1bAux

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal HeckeCharacter M4aHerbrand M4aHerbrand.GenuineDescent LanglandsTunnell.P2.Artin LanglandsTunnell.Converse LanglandsTunnell.TateLocal AutomorphicForm

open scoped IsMulCommutative

noncomputable def locIdele (𝔮 : HeightOneSpectrum (𝓞 ℚ)) (s : (𝔮.adicCompletion ℚ)ˣ) :
    (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ 𝔮 s)

theorem localChar_eq (θ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (𝔮 : HeightOneSpectrum (𝓞 ℚ))
    (t : (𝔮.adicCompletion ℚ)ˣ) : localChar θ 𝔮 t = θ (locIdele 𝔮 t) := rfl

theorem locIdele_mem_idelesTrivialOn (𝔮 : HeightOneSpectrum (𝓞 ℚ)) (s : (𝔮.adicCompletion ℚ)ˣ) :
    locIdele 𝔮 s ∈ idelesTrivialOn (𝓞 ℚ) ℚ ({𝔮}ᶜ : Set (HeightOneSpectrum (𝓞 ℚ))) := by
  refine ⟨?_, fun w hw => ?_⟩
  · exact Units.ext rfl
  · refine Units.ext ?_
    show ((localUnit (𝓞 ℚ) ℚ 𝔮 s : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1
    exact localUnit_apply_of_ne (𝓞 ℚ) ℚ 𝔮 s hw

theorem eq_of_dvd_pow {v 𝔮 : HeightOneSpectrum (𝓞 ℚ)} {m : ℕ} (h : v.asIdeal ∣ 𝔮.asIdeal ^ m) : v = 𝔮 := by
  have h1 : v.asIdeal ∣ 𝔮.asIdeal := v.prime.dvd_of_dvd_pow h
  have h2 : 𝔮.asIdeal ≤ v.asIdeal := Ideal.le_of_dvd h1
  exact (HeightOneSpectrum.ext (𝔮.isMaximal.eq_of_le v.isPrime.ne_top h2)).symm

theorem count_pow_self (𝔮 : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ) :
    (Associates.mk 𝔮.asIdeal).count (Associates.mk (𝔮.asIdeal ^ m)).factors = m := by
  classical
  rw [Associates.mk_pow, Associates.count_pow (Associates.mk_ne_zero.mpr 𝔮.ne_bot) 𝔮.associates_irreducible,
    Associates.count_self 𝔮.associates_irreducible, mul_one]

theorem isAdjuster_locIdele (𝔮 : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ) (hm : 1 ≤ m)
    (u : (𝔮.adicCompletion ℚ)ˣ) (hu : u ∈ higherUnitsAt ℚ 𝔮 m) :
    IsAdjuster ℚ (𝔮.asIdeal ^ m) (locIdele 𝔮 u) 1 := by
  refine ⟨fun v hv => ?_, fun τ => ?_⟩
  · obtain rfl := eq_of_dvd_pow hv
    simp only [map_one, inv_one, mul_one]
    show Valued.v (((localUnit (𝓞 ℚ) ℚ v u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 ∧
      Valued.v (((localUnit (𝓞 ℚ) ℚ v u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v - 1)
        ≤ WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk (v.asIdeal ^ m)).factors : ℤ))
    rw [localUnit_apply_self (𝓞 ℚ) ℚ v u, count_pow_self]
    rcases hu with ⟨h1, h2 | h2⟩
    · omega
    · exact ⟨h1, h2⟩
  · simp only [map_one, inv_one, mul_one]
    exact archSign_of_fst_eq_one ℚ τ rfl

end X1bAux

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal HeckeCharacter M4aHerbrand M4aHerbrand.GenuineDescent LanglandsTunnell.P2.Artin LanglandsTunnell.Converse LanglandsTunnell.TateLocal AutomorphicForm

open scoped IsMulCommutative

theorem solution
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] [IsMulCommutative (F ≃ₐ[ℚ] F)]
    (hℓ : (Module.finrank ℚ F).Prime)
    (𝔣 : Ideal (𝓞 ℚ)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree ℚ F (Module.finrank ℚ F) 𝔣)
    (r : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* (F ≃ₐ[ℚ] F))
    (hr₁ : principalIdeles (𝓞 ℚ) ℚ ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 ℚ) ℚ ⊔ (genuineBaseChange ℚ F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ, IsAdjuster ℚ 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), artinFrob ℚ F v ^ placeOrd ℚ (projFin ℚ u) v)
    (χ : (F ≃ₐ[ℚ] F) →* ℂˣ) (hχ : Function.Injective χ)
    (𝔮 : HeightOneSpectrum (𝓞 ℚ)) (m : ℕ) (hm : 1 ≤ m)
    (hdisc : (discr F).natAbs.factorization (Ideal.absNorm 𝔮.asIdeal) ≤ m)
    (u : (𝔮.adicCompletion ℚ)ˣ) (hu : u ∈ higherUnitsAt ℚ 𝔮 m) :
    localChar (χ.comp r) 𝔮 u = 1 := by
  have hf : ArtinL.Abelian.conductorExponent χ 𝔮 ≤ m :=
    (X1bAux.conductorExponent_le_factorization_discr F χ 𝔮).trans hdisc
  have hw : (⟨primeAbove ℚ F 𝔮, inferInstance, primeAbove_ne_bot ℚ F 𝔮⟩ : HeightOneSpectrum (𝓞 F)).under (𝓞 ℚ)
      = 𝔮 :=
    HeightOneSpectrum.ext (by rw [HeightOneSpectrum.under_asIdeal]; exact under_primeAbove ℚ F 𝔮)
  have hmem := M4aHerbrand.idelicArtinMap_mem_upperRamificationGroup_of_isAdjuster_pow ℚ F 𝔣 hadm r
    hr₁ hr₂ hr₃ hr₄ 𝔮 ⟨primeAbove ℚ F 𝔮, inferInstance, primeAbove_ne_bot ℚ F 𝔮⟩ hw m hm
    (X1bAux.locIdele 𝔮 u) (X1bAux.locIdele_mem_idelesTrivialOn 𝔮 u) (X1bAux.isAdjuster_locIdele 𝔮 m hm u hu)
  obtain ⟨σ, hσ, hσx⟩ := Subgroup.mem_map.mp hmem
  have key := ArtinL.Abelian.forall_mem_upperRamificationGroup_apply_eq_one_of_conductorExponent_le ℚ F χ 𝔮 m hf
    σ hσ
  rw [X1bAux.localChar_eq, MonoidHom.comp_apply, ← hσx]
  exact key

end S_LanglandsTunnell_CubicLambda_localChar_comp_idelicArtinMap_eq_one_of_mem_higherUnitsAt_of_factorization_discr_le_of_prime_finrank
end P2MW
export P2MW.S_LanglandsTunnell_CubicLambda_localChar_comp_idelicArtinMap_eq_one_of_mem_higherUnitsAt_of_factorization_discr_le_of_prime_finrank (solution)
