-- Prove2me | solution 1 for M4aHerbrand.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ca391d4c-6caf-5da2-bb38-30915ab380a1

import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_M4aHerbrand_AdeleBaseChange_ideleBox_le_range_idelicNorm
import Theorems.Thm_ClassGroup_exists_finset_forall_exists_mk0_eq_of_dvd
import Theorems.Thm_NumberField_AdeleRing_principalIdeles_sup_unitIdelesOutside_eq_top
import Theorems.Thm_NumberField_exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top
import Theorems.Thm_NumberField_finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map
import Theorems.Thm_M4aHerbrand_inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_of_isPrimitiveRoot
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv JacobiSumStickelberger.instModuleZModModP WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk IsLocalRing.principalUnits_zero groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity ExtCitation.LocalLevel.coe_smul_OO ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq"
p2m_attr_erase "simp" "Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin

theorem solution
    (E : Type) [Field E] [NumberField E] (p : ℕ) [Fact p.Prime] (ζ : E) (hζ : IsPrimitiveRoot ζ p)
    (S : Finset Nat.Primes) (hpS : (⟨p, Fact.out⟩ : Nat.Primes) ∈ S) :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : Algebra E F) (_ : IsGalois E F),
      (∀ σ τ : F ≃ₐ[E] F, σ * τ = τ * σ) ∧ (∀ σ : F ≃ₐ[E] F, σ ^ p = 1) ∧
      (∀ w : HeightOneSpectrum (𝓞 F), w ∉ NumberField.placesOverPrimes F (↑S : Set Nat.Primes) →
        Ideal.ramificationIdx' (w.asIdeal.under (𝓞 E)) w.asIdeal = 1) ∧
      principalIdeles (𝓞 E) E ⊔ ((genuineBaseChange E F).idelicNorm).range
        = principalIdeles (𝓞 E) E
            ⊔ (powMonoidHom p : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ).range
            ⊔ unitIdelesTrivialOn (𝓞 E) E (NumberField.placesOverPrimes E (↑S : Set Nat.Primes)) := by
  classical
  have hp : p.Prime := Fact.out
  have hζ' : (primitiveRoots p E).Nonempty := ⟨ζ, (mem_primitiveRoots hp.pos).mpr hζ⟩

  set T : Set (HeightOneSpectrum (𝓞 E)) := NumberField.placesOverPrimes E (↑S : Set Nat.Primes) with hTdef
  have hTfin : T.Finite := by
    have : T = ⋃ q ∈ (↑S : Set Nat.Primes), {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {((q : ℕ) : 𝓞 E)}} := by
      ext v
      simp only [hTdef, NumberField.mem_placesOverPrimes_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop,
        Ideal.dvd_span_singleton]
    rw [this]
    refine Set.Finite.biUnion S.finite_toSet fun q _ => Ideal.finite_factors ?_
    have hq0 : ((q : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast q.2.ne_zero
    simpa [Ideal.span_singleton_eq_bot] using hq0

  obtain ⟨S₀, hS₀⟩ := ClassGroup.exists_finset_forall_exists_mk0_eq_of_dvd (𝓞 E)
  set S' : Finset (HeightOneSpectrum (𝓞 E)) := S₀ ∪ hTfin.toFinset with hS'def
  have hTS' : T ⊆ (↑S' : Set (HeightOneSpectrum (𝓞 E))) := by
    intro v hv; simp [hS'def, hv]
  have hS'top : principalIdeles (𝓞 E) E ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 E) E (↑S' : Set (HeightOneSpectrum (𝓞 E))) = ⊤ :=
    NumberField.AdeleRing.principalIdeles_sup_unitIdelesOutside_eq_top (𝓞 E) E _ (fun c => by
      obtain ⟨I, hI, hIS⟩ := hS₀ c
      exact ⟨I, hI, fun v hv => by simp [hS'def, hIS v hv]⟩)
  have hSp' : ∀ v : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ v.asIdeal → v ∈ S' := by
    intro v hv
    have : v ∈ T := ⟨⟨p, hp⟩, hpS, by simpa using hv⟩
    exact_mod_cast hTS' this

  obtain ⟨F', _i1, _i2, _i3, _i4, hcomm', hexp', hunr', hnorm'⟩ :=
    NumberField.exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_unitIdelesTrivialOn_of_sup_unitIdelesOutside_eq_top
      E hp hζ' S' hSp' hS'top
  haveI : IsMulCommutative (F' ≃ₐ[E] F') := ⟨⟨hcomm'⟩⟩

  have hS'ne : (∏ v ∈ S', v.asIdeal : Ideal (𝓞 E)) ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
    push Not
    intro v _
    rw [Ideal.zero_eq_bot]
    exact v.ne_bot
  have hram' : ∀ v : HeightOneSpectrum (𝓞 E), (primeAbove E F' v).inertia (F' ≃ₐ[E] F') ≠ ⊥ →
      v.asIdeal ∣ ∏ v ∈ S', v.asIdeal := by
    intro v hv
    by_contra hdvd
    have hvS' : v ∉ S' := fun h => hdvd (Finset.dvd_prod_of_mem _ h)
    apply hv

    have hmax := LanglandsTunnell.P2.Artin.primeAbove_isMaximal E F' v
    let w : HeightOneSpectrum (𝓞 F') := ⟨primeAbove E F' v, hmax.isPrime, LanglandsTunnell.P2.Artin.primeAbove_ne_bot E F' v⟩
    exact hunr' v hvS' w (LanglandsTunnell.P2.Artin.under_primeAbove E F' v)
  obtain ⟨𝔣', -, -, hadm'⟩ := LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E F'
    (∏ v ∈ S', v.asIdeal) hS'ne hram' (Module.finrank E F')
  obtain ⟨r', hr'₁, hr'₂, hr'₃, hr'₄⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
      E F' 𝔣' hadm'

  set H₀ : Subgroup (AdeleRing (𝓞 E) E)ˣ := principalIdeles (𝓞 E) E
      ⊔ (powMonoidHom p : (AdeleRing (𝓞 E) E)ˣ →* (AdeleRing (𝓞 E) E)ˣ).range
      ⊔ unitIdelesTrivialOn (𝓞 E) E T with hH₀def
  have hkerH₀ : r'.ker ≤ H₀ := by
    rw [hr'₂, hnorm', hH₀def]
    exact sup_le_sup le_rfl (unitIdelesTrivialOn_antitone hTS')

  set Γ : Subgroup (F' ≃ₐ[E] F') := H₀.map r' with hΓdef
  haveI hΓn : Γ.Normal := Subgroup.normal_of_isMulCommutative Γ
  set F : IntermediateField E F' := IntermediateField.fixedField Γ with hFdef
  haveI : IsGalois E F := IsGalois.of_fixedField_normal_subgroup Γ
  haveI : FiniteDimensional ℚ F := Module.Finite.trans E F
  haveI : NumberField F := ⟨⟩
  haveI : IsMulCommutative (F ≃ₐ[E] F) := by
    refine ⟨⟨fun σ τ => ?_⟩⟩
    obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective F' σ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective F' τ
    rw [← map_mul, ← map_mul, hcomm']
  have hΓker : (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker = Γ := by
    rw [IntermediateField.restrictNormalHom_ker, hFdef, IntermediateField.fixingSubgroup_fixedField]

  obtain ⟨hdeg, hker, hunrF⟩ :=
    NumberField.finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map
      E F F' r' hr'₃ H₀ hkerH₀ hΓker

  have hinert : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ T →
      ∀ w' : HeightOneSpectrum (𝓞 F'), w'.asIdeal.under (𝓞 E) = v.asIdeal →
        w'.asIdeal.inertia (F' ≃ₐ[E] F') ≤ Γ := by
    intro v hvT w' hw'
    by_cases hvS' : v ∈ S'
    ·
      have hw'' : w'.under (𝓞 E) = v := HeightOneSpectrum.ext (by simpa using hw')
      refine le_trans (M4aHerbrand.inertia_le_map_unitIdelesTrivialOn_compl_singleton_of_idelicArtinMap
        E F' 𝔣' hadm' r' hr'₁ hr'₂ hr'₃ hr'₄ v w' hw'') (Subgroup.map_mono ?_)

      refine le_trans (unitIdelesTrivialOn_antitone ?_) le_sup_right
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl; exact hvT ht
    · rw [hunr' v hvS' w' hw']; exact bot_le
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · exact fun σ τ => IsMulCommutative.is_comm.comm σ τ
  · intro σ
    obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective F' σ
    rw [← map_pow, hexp', map_one]
  ·
    intro w hw
    have hvT : w.under (𝓞 E) ∉ T := by
      rintro ⟨q, hq, hqw⟩
      refine hw ⟨q, hq, ?_⟩
      have : (algebraMap (𝓞 E) (𝓞 F)) ((q : ℕ) : 𝓞 E) ∈ w.asIdeal := by
        simpa [Ideal.mem_comap] using hqw
      simpa using this
    exact hunrF (w.under (𝓞 E)) (hinert _ hvT) w (by simp)
  ·

    have hunr_all : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ T → ∀ w : HeightOneSpectrum (𝓞 F),
        w.asIdeal.under (𝓞 E) = v.asIdeal → Ideal.ramificationIdx' (w.asIdeal.under (𝓞 E)) w.asIdeal = 1 :=
      fun v hv => hunrF v (hinert v hv)
    have hinertF : ∀ v : HeightOneSpectrum (𝓞 E), v ∉ T → ∀ w : HeightOneSpectrum (𝓞 F),
        w.asIdeal.under (𝓞 E) = v.asIdeal → w.asIdeal.inertia (F ≃ₐ[E] F) = ⊥ := by
      intro v hv w hw
      have h1 := hunr_all v hv w hw
      haveI : w.asIdeal.IsMaximal := w.isMaximal
      haveI hlo : w.asIdeal.LiesOver (w.asIdeal.under (𝓞 E)) := ⟨rfl⟩
      have hpb : w.asIdeal.under (𝓞 E) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot
      haveI : (w.asIdeal.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) w.asIdeal
      haveI : Finite (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) := Ideal.finiteQuotientOfFreeOfNeBot _ hpb
      letI : Field (𝓞 E ⧸ w.asIdeal.under (𝓞 E)) := Ideal.Quotient.field _
      letI : Field (𝓞 F ⧸ w.asIdeal) := Ideal.Quotient.field _
      have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := F ≃ₐ[E] F) (w.asIdeal.under (𝓞 E)) w.asIdeal
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx (w.asIdeal.under (𝓞 E)) w.asIdeal (F ≃ₐ[E] F),
        ← Ideal.ramificationIdx'_eq_ramificationIdx (w.asIdeal.under (𝓞 E)) w.asIdeal hpb, h1] at hcard
      exact Subgroup.eq_bot_of_card_eq _ hcard

    have hTne : (∏ v ∈ hTfin.toFinset, v.asIdeal : Ideal (𝓞 E)) ≠ ⊥ := by
      rw [Ne, ← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
      push Not
      intro v _
      rw [Ideal.zero_eq_bot]
      exact v.ne_bot
    have hramF : ∀ v : HeightOneSpectrum (𝓞 E), (primeAbove E F v).inertia (F ≃ₐ[E] F) ≠ ⊥ →
        v.asIdeal ∣ ∏ v ∈ hTfin.toFinset, v.asIdeal := by
      intro v hv
      by_contra hdvd
      have hvT : v ∉ T := fun h => hdvd (Finset.dvd_prod_of_mem _ (hTfin.mem_toFinset.mpr h))
      apply hv
      have hmax := LanglandsTunnell.P2.Artin.primeAbove_isMaximal E F v
      let w : HeightOneSpectrum (𝓞 F) := ⟨primeAbove E F v, hmax.isPrime, LanglandsTunnell.P2.Artin.primeAbove_ne_bot E F v⟩
      exact hinertF v hvT w (LanglandsTunnell.P2.Artin.under_primeAbove E F v)
    obtain ⟨𝔣F, -, -, hadmF⟩ := LanglandsTunnell.P2.Artin.exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E F
      (∏ v ∈ hTfin.toFinset, v.asIdeal) hTne hramF (Module.finrank E F)
    obtain ⟨rF, hrF₁, hrF₂, hrF₃, hrF₄⟩ :=
      NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
        E F 𝔣F hadmF

    have hexpF : ∀ σ : F ≃ₐ[E] F, σ ^ p = 1 := by
      intro σ
      obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective F' σ
      rw [← map_pow, hexp', map_one]
    have hUT : unitIdelesTrivialOn (𝓞 E) E T ≤ ((genuineBaseChange E F).idelicNorm).range := by
      refine le_trans ?_ (M4aHerbrand.AdeleBaseChange.ideleBox_le_range_idelicNorm E F (genuineBaseChange E F)
        (dvd_refl (Module.finrank E F)) hTfin.toFinset (fun _ => ⊥) (fun _ => ⊥)
        (fun v _ => Or.inl bot_le) (fun v hv w => ?_) (fun w _ => bot_le))
      ·
        intro x hx
        obtain ⟨hxU, hxinf, hxT⟩ := (mem_unitIdelesTrivialOn_iff T x).mp hx
        rw [NumberField.AdeleRing.mem_ideleBox_iff]
        refine ⟨⟨fun v hv => ?_, fun v hv => hxU v (by simpa using hv)⟩, fun w => ?_⟩
        · rw [Subgroup.mem_bot]
          ext
          rw [NumberField.AdeleRing.val_finiteUnitsComponent, Units.val_one, ← coe_finPart_apply,
            hxT v (by simpa using hv), Units.val_one]
        · rw [Subgroup.mem_bot]
          ext
          rw [NumberField.AdeleRing.val_infiniteUnitsComponent, Units.val_one, ← coe_infPart_apply, hxinf,
            Units.val_one]
          rfl
      · exact hinertF v (fun h => hv (hTfin.mem_toFinset.mpr h)) w.1 (by
          have := w.2; simpa using congrArg HeightOneSpectrum.asIdeal this)
    have hH₀F : H₀ ≤ rF.ker := by
      rw [hH₀def, hrF₂]
      refine sup_le (sup_le le_sup_left ?_) (le_trans hUT le_sup_right)
      rintro _ ⟨y, rfl⟩
      rw [← hrF₂, MonoidHom.mem_ker, powMonoidHom_apply, map_pow, hexpF]

    have := hker rF hrF₃ hH₀F
    rw [hrF₂] at this
    rw [this]

end S_M4aHerbrand_exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_of_isPrimitiveRoot
end P2MW
export P2MW.S_M4aHerbrand_exists_isGalois_principalIdeles_sup_range_idelicNorm_eq_of_isPrimitiveRoot (solution)
