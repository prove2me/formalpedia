-- Prove2me | solution 1 for NumberField.exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/82cdf9e2-f8c4-5f24-b801-04a476d09cf6

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_FiniteConorm
import Theorems.Thm_NumberField_exists_le_isGalois_forall_classGroup_map_eq_one_of_pow_eq_one
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff
import Theorems.Thm_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq
import Theorems.Thm_NumberField_denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem
p2m_attr_erase "instance" "groupCohomology.normal_comap_fixingSubgroup groupCohomology.finiteIndex_comap_fixingSubgroup ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete NumberField.LevelArith.instCommGroupUnitsModPow"
p2m_attr_erase "simp" "groupCohomology.continuousH2Inflation_H2π groupCohomology.levelInflate₂_apply groupCohomology.coe_levelInflateCocycles₂ groupCohomology.levelInflate₁_apply NumberField.LevelArith.coe_levelFieldEquiv NumberField.LevelArith.modP_apply_mk NumberField.LevelArith.coe_levelFieldEquiv_symm NumberField.LevelArith.torsionP_apply_coe NumberField.LevelArith.repTorsionPMap_hom_apply_coe NumberField.LevelArith.toZMod_apply NumberField.LevelArith.repModPMap_hom_mk NumberField.SUnits.val_zsmul NumberField.SUnits.val_add ExtCitation.LocalLevel.coe_smul_OO WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply groupCohomology.coe_continuousH1SrMap_apply groupCohomology.continuousH2SrMap_continuousH2Srπ groupCohomology.coe_levelCocyclesSr₂Map NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk"

set_option autoImplicit false
p2m_open "NumberField P2MW.S_NumberField_exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem.NumberField IsDedekindDomain ExtCitation"
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.ext placesOverPrimes exists_le_isGalois_forall_classGroup_map_eq_one_of_pow_eq_one denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext"
namespace CapFin
p2m_open "NumberField"

open scoped nonZeroDivisors

section ClassMap
variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S] (f : R →+* S) (hf : Function.Injective f)

include hf in
theorem map_mem_nonZeroDivisors (I : (Ideal R)⁰) : (I : Ideal R).map f ∈ (Ideal S)⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  have hI : (I : Ideal R) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  exact hI ((Ideal.map_eq_bot_iff_of_injective hf).mp h)

noncomputable def mapIdeal0 (I : (Ideal R)⁰) : (Ideal S)⁰ := ⟨(I : Ideal R).map f, map_mem_nonZeroDivisors f hf I⟩

theorem coe_mapIdeal0 (I : (Ideal R)⁰) : ((mapIdeal0 f hf I : (Ideal S)⁰) : Ideal S) = (I : Ideal R).map f := rfl

include hf in
theorem mk0_map_eq_of_mk0_eq {I J : (Ideal R)⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (mapIdeal0 f hf I) = ClassGroup.mk0 (mapIdeal0 f hf J) := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h ⊢
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ⟨f x, f y, fun h0 => hx (hf (by rw [h0, map_zero])), fun h0 => hy (hf (by rw [h0, map_zero])), ?_⟩
  have := congrArg (Ideal.map f) hxy
  rwa [Ideal.map_mul, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at this

noncomputable def classMap : ClassGroup R →* ClassGroup S where
  toFun c := ClassGroup.mk0 (mapIdeal0 f hf (Classical.choose (ClassGroup.mk0_surjective c)))
  map_one' := by
    have h1 : ClassGroup.mk0 (Classical.choose (ClassGroup.mk0_surjective (1 : ClassGroup R))) = ClassGroup.mk0 (1 : (Ideal R)⁰) := by
      rw [Classical.choose_spec (ClassGroup.mk0_surjective (1 : ClassGroup R)), map_one]
    rw [mk0_map_eq_of_mk0_eq f hf h1]
    have : mapIdeal0 f hf (1 : (Ideal R)⁰) = 1 := Subtype.ext (by rw [coe_mapIdeal0]; simp [Ideal.map_top])
    rw [this, map_one]
  map_mul' c c' := by
    have hcc : ClassGroup.mk0 (Classical.choose (ClassGroup.mk0_surjective (c * c'))) =
        ClassGroup.mk0 (Classical.choose (ClassGroup.mk0_surjective c) * Classical.choose (ClassGroup.mk0_surjective c')) := by
      rw [map_mul, Classical.choose_spec (ClassGroup.mk0_surjective c), Classical.choose_spec (ClassGroup.mk0_surjective c'),
        Classical.choose_spec (ClassGroup.mk0_surjective (c * c'))]
    rw [mk0_map_eq_of_mk0_eq f hf hcc, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [coe_mapIdeal0, Submonoid.coe_mul, Ideal.map_mul]

theorem classMap_mk0 (I : (Ideal R)⁰) : classMap f hf (ClassGroup.mk0 I) = ClassGroup.mk0 (mapIdeal0 f hf I) := by
  show ClassGroup.mk0 (mapIdeal0 f hf (Classical.choose (ClassGroup.mk0_surjective (ClassGroup.mk0 I)))) = _
  exact mk0_map_eq_of_mk0_eq f hf (Classical.choose_spec (ClassGroup.mk0_surjective (ClassGroup.mk0 I)))

end ClassMap

theorem exists_mul_of_pow_mem {G : Type*} [CommGroup G] [Finite G] {p : ℕ} (hp : p.Prime) (H : Subgroup G)
    (c : G) (k : ℕ) (hck : c ^ p ^ k ∈ H) :
    ∃ c₁ h : G, c = c₁ * h ∧ (∃ j : ℕ, c₁ ^ p ^ j = 1) ∧ h ∈ H := by
  classical
  by_cases hk : k = 0
  · subst hk
    exact ⟨1, c, by rw [one_mul], ⟨0, one_pow _⟩, by simpa using hck⟩

  obtain ⟨a, m, hm, hG⟩ : ∃ a m : ℕ, ¬ p ∣ m ∧ Nat.card G = p ^ a * m :=
    ⟨(Nat.card G).factorization p, Nat.card G / p ^ (Nat.card G).factorization p,
      Nat.not_dvd_ordCompl hp Nat.card_pos.ne', (Nat.ordProj_mul_ordCompl_eq_self _ _).symm⟩

  have hcop : Nat.Coprime m (p ^ k) := Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  obtain ⟨w, -, hw⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Nat.one_lt_pow hk hp.one_lt)
  set q := m * w / p ^ k with hq
  have hmw : m * w = 1 + p ^ k * q := by
    have h0 := Nat.mod_add_div (m * w) (p ^ k)
    rw [hw] at h0
    rw [hq]
    exact h0.symm
  have hcG : c ^ (p ^ a * m) = 1 := by rw [← hG]; exact pow_card_eq_one'
  refine ⟨c ^ (m * w), ((c ^ p ^ k) ^ q)⁻¹, ?_, ⟨a, ?_⟩, H.inv_mem (H.pow_mem hck q)⟩
  · rw [hmw, pow_add, pow_one, pow_mul, mul_inv_cancel_right]
  · rw [← pow_mul, show m * w * p ^ a = (p ^ a * m) * w by ring, pow_mul, hcG, one_pow]

end NumberField.CapFin

namespace NumberField
p2m_export "NumberField" "mk place RingOfIntegers RingOfIntegers.ext placesOverPrimes exists_le_isGalois_forall_classGroup_map_eq_one_of_pow_eq_one denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext"
namespace CapFin
p2m_open "NumberField"

open scoped nonZeroDivisors

section Classes
variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

noncomputable def ideal0 (v : HeightOneSpectrum R) : (Ideal R)⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.2 v.ne_bot⟩

@[scoped simp] theorem coe_ideal0 (v : HeightOneSpectrum R) : ((ideal0 R v : (Ideal R)⁰) : Ideal R) = v.asIdeal := rfl

theorem mk_eq_finprod_of_coe_eq {ι : Type*} (U : (FractionalIdeal R⁰ K)ˣ) (u : ι → (FractionalIdeal R⁰ K)ˣ) (n : ι → ℤ)
    (hfin : {i | n i ≠ 0}.Finite) (h : (U : FractionalIdeal R⁰ K) = ∏ᶠ i, (u i : FractionalIdeal R⁰ K) ^ n i) :
    ClassGroup.mk K U = ∏ᶠ i, ClassGroup.mk K (u i) ^ n i := by
  have hsupp : (Function.mulSupport fun i => u i ^ n i).Finite := by
    refine hfin.subset fun i hi => ?_
    intro h0
    exact hi (by simp [h0])
  have hU : U = ∏ᶠ i, u i ^ n i := by
    apply Units.ext
    rw [h, show ((∏ᶠ i, u i ^ n i : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
      ∏ᶠ i, ((u i ^ n i : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) from (Units.coeHom (FractionalIdeal R⁰ K)).map_finprod hsupp]
    simp only [Units.val_zpow_eq_zpow_val]
  have hsupp' : (Function.mulSupport fun i => ClassGroup.mk K (u i) ^ n i).Finite := by
    refine hfin.subset fun i hi => ?_
    intro h0
    exact hi (by simp [h0])
  rw [hU, MonoidHom.map_finprod _ hsupp]
  simp only [map_zpow]

theorem mk_mk0_ideal0 (v : HeightOneSpectrum R) :
    ClassGroup.mk K (FractionalIdeal.mk0 K (ideal0 R v)) = ClassGroup.mk0 (ideal0 R v) := ClassGroup.mk_mk0 K _

include K in

theorem mk0_mem_of_forall_dvd (H : Subgroup (ClassGroup R)) (J : (Ideal R)⁰)
    (hJ : ∀ w : HeightOneSpectrum R, w.asIdeal ∣ (J : Ideal R) → ClassGroup.mk0 (ideal0 R w) ∈ H) :
    ClassGroup.mk0 J ∈ H := by
  classical
  have hJ0 : ((J : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact mem_nonZeroDivisors_iff_ne_zero.1 J.2
  have hJ0' : (J : Ideal R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 J.2

  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ0
  have hfin : {w : HeightOneSpectrum R | FractionalIdeal.count K w ((J : Ideal R) : FractionalIdeal R⁰ K) ≠ 0}.Finite :=
    (FractionalIdeal.finite_factors ((J : Ideal R) : FractionalIdeal R⁰ K))
  have hmk := mk_eq_finprod_of_coe_eq R K (FractionalIdeal.mk0 K J) (fun w => FractionalIdeal.mk0 K (ideal0 R w))
    (fun w => FractionalIdeal.count K w ((J : Ideal R) : FractionalIdeal R⁰ K)) hfin
    (by rw [FractionalIdeal.coe_mk0]; exact hfac.symm.trans (finprod_congr fun w => by rw [FractionalIdeal.coe_mk0]; rfl))
  rw [← ClassGroup.mk_mk0 K, hmk]
  refine finprod_induction (fun c => c ∈ H) H.one_mem (fun _ _ => H.mul_mem) fun w => ?_
  by_cases hc : FractionalIdeal.count K w ((J : Ideal R) : FractionalIdeal R⁰ K) = 0
  · rw [hc, zpow_zero]; exact H.one_mem
  · refine H.zpow_mem ?_ _
    rw [mk_mk0_ideal0]
    apply hJ
    rw [FractionalIdeal.count_coe K w hJ0'] at hc
    exact (Associates.count_ne_zero_iff_dvd hJ0' w.irreducible).1 (by exact_mod_cast hc)

end Classes

section FiniteIdele
variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

theorem finite_valued_ne_one (x : (FiniteAdeleRing R K)ˣ) :
    {v : HeightOneSpectrum R | Valued.v ((x : FiniteAdeleRing R K) v) ≠ 1}.Finite := by
  have h1 : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, (x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
    (x : FiniteAdeleRing R K).2
  have h2 : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
    ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K).2
  have h3 : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, Valued.v ((x : FiniteAdeleRing R K) v) = 1 := by
    filter_upwards [h1, h2] with v hv hv'
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv hv'
    have hmul : (x : FiniteAdeleRing R K) v * ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = 1 := by
      have e : ((x : FiniteAdeleRing R K) * ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)) v = (1 : FiniteAdeleRing R K) v := by
        rw [x.mul_inv]
      exact e
    have hvm := congrArg Valued.v hmul
    rw [map_mul, map_one] at hvm
    apply le_antisymm hv
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((x : FiniteAdeleRing R K) v) * Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) := hvm.symm
      _ ≤ Valued.v ((x : FiniteAdeleRing R K) v) * 1 := mul_le_mul_right hv' _
      _ = Valued.v ((x : FiniteAdeleRing R K) v) := mul_one _
  exact Filter.eventually_cofinite.1 h3

theorem finite_log_valued_ne_zero (x : (FiniteAdeleRing R K)ˣ) :
    {v : HeightOneSpectrum R | -(WithZero.log (Valued.v ((x : FiniteAdeleRing R K) v))) ≠ 0}.Finite := by
  refine (finite_valued_ne_one R K x).subset fun v hv => ?_
  intro h1
  apply hv
  simp [h1]

end FiniteIdele

end NumberField.CapFin
p2m_reactivate "P2MW.S_NumberField_exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem.NumberField P2MW.S_NumberField_exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem.NumberField.CapFin"
p2m_reactivate "P2MW.S_NumberField_exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem.NumberField"

open NumberField.CapFin in
open scoped nonZeroDivisors RestrictedProduct in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] (hF : F.IsUnramifiedOutside S) :
    ∃ (F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : F ≤ F'') (_ : NumberField ↥F''),
      F''.IsUnramifiedOutside S ∧ IsGalois ℚ ↥F'' ∧
      ∀ (Ψ : FiniteAdeleRing (𝓞 ↥F) ↥F →+* FiniteAdeleRing (𝓞 ↥F'') ↥F'') (_ : Continuous Ψ)
        (_ : ∀ a : ↥F, Ψ (algebraMap ↥F (FiniteAdeleRing (𝓞 ↥F) ↥F) a) =
          algebraMap ↥F'' (FiniteAdeleRing (𝓞 ↥F'') ↥F'') (IntermediateField.inclusion h a))
        (x : (FiniteAdeleRing (𝓞 ↥F) ↥F)ˣ),
        (∃ k : ℕ, x ^ p ^ k ∈ (Units.map (algebraMap ↥F (FiniteAdeleRing (𝓞 ↥F) ↥F) : ↥F →* FiniteAdeleRing (𝓞 ↥F) ↥F)).range ⊔
            IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥F) ↥F (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes))) →
        Units.map (Ψ : FiniteAdeleRing (𝓞 ↥F) ↥F →* FiniteAdeleRing (𝓞 ↥F'') ↥F'') x ∈ (Units.map (algebraMap ↥F'' (FiniteAdeleRing (𝓞 ↥F'') ↥F'') : ↥F'' →* FiniteAdeleRing (𝓞 ↥F'') ↥F'')).range ⊔
            IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 ↥F'') ↥F'' (NumberField.placesOverPrimes ↥F'' (↑S : Set Nat.Primes)) := by
  classical

  obtain ⟨F'', h, NF, hunr, hGal, hkill⟩ :=
    NumberField.exists_le_isGalois_forall_classGroup_map_eq_one_of_pow_eq_one (p := p) S hpS F hF
  haveI := NF
  refine ⟨F'', h, NF, hunr, hGal, ?_⟩
  intro Ψ hΨc hΨa x hx
  obtain ⟨k, hxk⟩ := hx

  letI algF : Algebra ↥F ↥F'' := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : FiniteDimensional ↥F ↥F'' := Module.Finite.of_restrictScalars_finite ℚ ↥F ↥F''
  haveI : T2Space (FiniteAdeleRing (𝓞 ↥F'') ↥F'') := inferInstanceAs <|
    T2Space <| Πʳ v : HeightOneSpectrum (𝓞 ↥F''), [v.adicCompletion ↥F'', v.adicCompletionIntegers ↥F'']
  have hΨ : Ψ = M4aHerbrand.Bridge.finiteConorm (𝓞 ↥F) ↥F ↥F'' (𝓞 ↥F'') :=
    (NumberField.denseRange_algebraMap_finiteAdeleRing_and_ringHom_ext ↥F).2 (FiniteAdeleRing (𝓞 ↥F'') ↥F'') Ψ
      (M4aHerbrand.Bridge.finiteConorm (𝓞 ↥F) ↥F ↥F'' (𝓞 ↥F'')) hΨc (M4aHerbrand.Bridge.continuous_finiteConorm (𝓞 ↥F) ↥F ↥F'' (𝓞 ↥F''))
      (fun a => by rw [hΨa, M4aHerbrand.Bridge.finiteConorm_algebraMap]; rfl)
  have hΨx : Units.map (Ψ : (FiniteAdeleRing (𝓞 ↥F) ↥F) →* (FiniteAdeleRing (𝓞 ↥F'') ↥F'')) x = Units.map (M4aHerbrand.Bridge.finiteConorm (𝓞 ↥F) ↥F ↥F'' (𝓞 ↥F'')).toMonoidHom x := by
    apply Units.ext
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, hΨ]

  obtain ⟨φ₁, hφ₁, -, -, -, hcrit₁⟩ := IsDedekindDomain.FiniteAdeleRing.exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff (𝓞 ↥F) ↥F
  obtain ⟨φ₂, hφ₂, -, -, -, hcrit₂⟩ := IsDedekindDomain.FiniteAdeleRing.exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff (𝓞 ↥F'') ↥F''
  have hinj : Function.Injective (algebraMap (𝓞 ↥F) (𝓞 ↥F'')) := by
    intro a b hab
    apply RingOfIntegers.ext
    have := congrArg (fun z : (𝓞 ↥F'') => ((z : ↥F'') : AlgebraicClosure ℚ)) hab
    exact Subtype.ext this
  let cm : ClassGroup (𝓞 ↥F) →* ClassGroup (𝓞 ↥F'') := classMap (algebraMap (𝓞 ↥F) (𝓞 ↥F'')) hinj

  set e : HeightOneSpectrum (𝓞 ↥F) → ℤ := fun v => -(WithZero.log (Valued.v ((x : (FiniteAdeleRing (𝓞 ↥F) ↥F)) v))) with he
  have hefin : {v | e v ≠ 0}.Finite := finite_log_valued_ne_zero (𝓞 ↥F) ↥F x
  have hc1 : ClassGroup.mk ↥F (φ₁ x) = ∏ᶠ v, ClassGroup.mk0 (ideal0 (𝓞 ↥F) v) ^ e v := by
    rw [mk_eq_finprod_of_coe_eq (𝓞 ↥F) ↥F (φ₁ x) (fun v => FractionalIdeal.mk0 ↥F (ideal0 (𝓞 ↥F) v)) e hefin
      (by rw [hφ₁ x]; exact finprod_congr fun v => by rw [FractionalIdeal.coe_mk0]; rfl)]
    exact finprod_congr fun v => by rw [mk_mk0_ideal0]
  have hc2 : ClassGroup.mk ↥F'' (φ₂ (Units.map (M4aHerbrand.Bridge.finiteConorm (𝓞 ↥F) ↥F ↥F'' (𝓞 ↥F'')).toMonoidHom x)) =
      cm (ClassGroup.mk ↥F (φ₁ x)) := by
    have hb := (M4aHerbrand.Bridge.valued_finiteConorm_apply_and_finprod_pow_eq (𝓞 ↥F) ↥F ↥F'' (𝓞 ↥F'') x).2
    have hval : (φ₂ (Units.map (M4aHerbrand.Bridge.finiteConorm (𝓞 ↥F) ↥F ↥F'' (𝓞 ↥F'')).toMonoidHom x) : FractionalIdeal (𝓞 ↥F'')⁰ ↥F'') =
        ∏ᶠ v, ((FractionalIdeal.mk0 ↥F'' (mapIdeal0 (algebraMap (𝓞 ↥F) (𝓞 ↥F'')) hinj (ideal0 (𝓞 ↥F) v)) : (FractionalIdeal (𝓞 ↥F'')⁰ ↥F'')ˣ) :
          FractionalIdeal (𝓞 ↥F'')⁰ ↥F'') ^ e v := by
      rw [hφ₂, hb]
      exact finprod_congr fun v => by rw [FractionalIdeal.coe_mk0]; rfl
    rw [mk_eq_finprod_of_coe_eq (𝓞 ↥F'') ↥F'' _ _ e hefin hval, hc1]
    have hsupp : (Function.mulSupport fun v => ClassGroup.mk0 (ideal0 (𝓞 ↥F) v) ^ e v).Finite := by
      refine hefin.subset fun v hv => ?_
      intro h0
      exact hv (by simp [h0])
    rw [MonoidHom.map_finprod _ hsupp]
    refine finprod_congr fun v => ?_
    rw [map_zpow, ClassGroup.mk_mk0, classMap_mk0]

  have hmem1 := (hcrit₁ (NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes)) (x ^ p ^ k)).1 hxk
  rw [map_pow, map_pow] at hmem1
  obtain ⟨c₁, hh, hc, ⟨j, hj⟩, hhmem⟩ := exists_mul_of_pow_mem (Fact.out : p.Prime) _ (ClassGroup.mk ↥F (φ₁ x)) k hmem1

  rw [hcrit₂, hΨx, hc2, hc, map_mul]
  refine Subgroup.mul_mem _ ?_ ?_
  ·
    rw [hkill cm (fun I J hJ => ?_) c₁ ⟨j, hj⟩]
    · exact Subgroup.one_mem _
    · rw [classMap_mk0]
      congr 1
      apply Subtype.ext
      rw [coe_mapIdeal0, hJ]
      rfl
  ·
    have hle : (Subgroup.closure {c : ClassGroup (𝓞 ↥F) | ∃ v ∈ NumberField.placesOverPrimes ↥F (↑S : Set Nat.Primes),
        ∃ h0 : v.asIdeal ∈ (Ideal (𝓞 ↥F))⁰, ClassGroup.mk0 ⟨v.asIdeal, h0⟩ = c}).map cm ≤
        Subgroup.closure {c : ClassGroup (𝓞 ↥F'') | ∃ v ∈ NumberField.placesOverPrimes ↥F'' (↑S : Set Nat.Primes),
          ∃ h0 : v.asIdeal ∈ (Ideal (𝓞 ↥F''))⁰, ClassGroup.mk0 ⟨v.asIdeal, h0⟩ = c} := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_le _ |>.2
      rintro _ ⟨c', ⟨v, hvT, hv0, rfl⟩, rfl⟩
      rw [show (⟨v.asIdeal, hv0⟩ : (Ideal (𝓞 ↥F))⁰) = ideal0 (𝓞 ↥F) v from rfl, classMap_mk0]
      apply mk0_mem_of_forall_dvd (𝓞 ↥F'') ↥F'' _ (mapIdeal0 (algebraMap (𝓞 ↥F) (𝓞 ↥F'')) hinj (ideal0 (𝓞 ↥F) v))
      intro w hw
      apply Subgroup.subset_closure
      refine ⟨w, ?_, (ideal0 (𝓞 ↥F'') w).2, rfl⟩
      obtain ⟨q, hqS, hqv⟩ := hvT
      refine ⟨q, hqS, ?_⟩
      have hle := Ideal.le_of_dvd hw
      have hq : ((q : ℕ) : (𝓞 ↥F'')) = algebraMap (𝓞 ↥F) (𝓞 ↥F'') ((q : ℕ) : (𝓞 ↥F)) := (map_natCast _ q).symm
      rw [hq]
      exact hle (Ideal.mem_map_of_mem _ hqv)
    exact hle ⟨hh, hhmem, rfl⟩

end S_NumberField_exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem
end P2MW
export P2MW.S_NumberField_exists_le_isGalois_forall_mem_range_sup_unitIdelesOutside_of_pow_mem (solution)
