-- Prove2me | solution 1 for HenselianLocalRing.moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e8ce3a28-236d-5992-a0e7-9f7eb0f13415

import Mathlib
import Theorems.Thm_HenselianLocalRing_moduleFinite_localizationAtPrime_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HenselianLocalRing_moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 12800000

open IsLocalRing

theorem solution
    {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A] [HenselianLocalRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (𝔫 : Ideal B) [𝔫.IsPrime] (h𝔫 : 𝔫.comap (algebraMap A B) = maximalIdeal A)
    {S : Type*} [CommRing S] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    [IsLocalization.AtPrime S 𝔫] [Module.Flat A S]
    (h T : S) (hT : ¬IsUnit T)
    (hreg : Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A S)) h ∈
      nonZeroDivisors (S ⧸ (maximalIdeal A).map (algebraMap A S)))
    (hfin : Module.Finite A (S ⧸ (Ideal.span ({h} : Set S) ⊔ (maximalIdeal A).map (algebraMap A S)))) :
    Module.Finite A (S ⧸ Ideal.span ({h} : Set S)) ∧
      ∃ k : ℕ, (Ideal.Quotient.mk (Ideal.span ({h} : Set S)) T) ^ k ∈
        (maximalIdeal A).map (algebraMap A (S ⧸ Ideal.span ({h} : Set S))) := by
  classical
  let I : Ideal S := Ideal.span ({h} : Set S)
  let Q := S ⧸ I
  let mk : S →+* Q := Ideal.Quotient.mk I
  haveI hSloc : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S 𝔫

  by_cases hhu : IsUnit h
  · have hI : I = ⊤ := Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_span_singleton_self h) hhu
    haveI : Subsingleton Q := Ideal.Quotient.subsingleton_iff.mpr hI
    refine ⟨Module.Finite.of_surjective (0 : A →ₗ[A] Q) (fun q => ⟨0, Subsingleton.elim _ _⟩), 1, ?_⟩
    rw [Subsingleton.elim ((Ideal.Quotient.mk (Ideal.span ({h} : Set S)) T) ^ 1) 0]
    exact Ideal.zero_mem _

  have hIne : I ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
    exact fun hd => hhu (isUnit_of_dvd_one hd)
  haveI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hIne
  haveI hQloc : IsLocalRing Q := IsLocalRing.of_surjective' mk Ideal.Quotient.mk_surjective
  have halgQ : ∀ a : A, algebraMap A Q a = mk (algebraMap A S a) := fun _ => rfl

  have hmS : ∀ a ∈ maximalIdeal A, algebraMap A S a ∈ maximalIdeal S := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply A B S]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔫 _).mpr
    show algebraMap A B a ∈ 𝔫
    have : a ∈ 𝔫.comap (algebraMap A B) := by rw [h𝔫]; exact ha
    exact this
  have hh𝔪 : h ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hhu
  have hmkunit : ∀ s : S, IsUnit (mk s) → IsUnit s := by
    intro s hs
    by_contra hns
    obtain ⟨y, hy⟩ := hs.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one mk, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
    obtain ⟨d, hd⟩ := hy
    have h1 : (1 : S) ∈ maximalIdeal S := by
      have : (1 : S) = s * y - h * d := by rw [← hd]; ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hns))
        (Ideal.mul_mem_right _ _ hh𝔪)
    exact (Ideal.ne_top_iff_one _).mp (maximalIdeal.isMaximal S).ne_top h1
  have hmQ : ∀ a ∈ maximalIdeal A, algebraMap A Q a ∈ maximalIdeal Q := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, halgQ]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp (hmS a ha) (hmkunit _ hu)
  have hunderQ : (maximalIdeal Q).comap (algebraMap A Q) = maximalIdeal A :=
    ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.ne_top inferInstance) (fun a ha => hmQ a ha)).symm

  haveI : Algebra.EssFiniteType B S := Algebra.EssFiniteType.of_isLocalization S 𝔫.primeCompl
  haveI : Algebra.EssFiniteType A S := Algebra.EssFiniteType.comp A B S
  haveI : Algebra.EssFiniteType A Q :=
    Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ A I) Ideal.Quotient.mk_surjective
  obtain ⟨C, M, hCft, hCloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra (R := A) (S := Q)).mp inferInstance
  haveI := hCft
  haveI := hCloc
  let 𝔭 : Ideal C := (maximalIdeal Q).comap C.val
  haveI h𝔭p : 𝔭.IsPrime := Ideal.comap_isPrime C.val (maximalIdeal Q)
  have hM𝔭 : M ≤ 𝔭.primeCompl := by
    intro m hm h𝔭m
    have hu : IsUnit (algebraMap C Q m) := IsLocalization.map_units Q ⟨m, hm⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h𝔭m) hu
  haveI hloc𝔭 : IsLocalization 𝔭.primeCompl Q := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      by_contra hu
      exact hc (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu))
    · intro q
      obtain ⟨⟨c, m⟩, e⟩ := IsLocalization.surj M q
      exact ⟨⟨c, ⟨m.1, hM𝔭 m.2⟩⟩, e⟩
    · intro c₁ c₂ e
      obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := M) e
      exact ⟨⟨m.1, hM𝔭 m.2⟩, hm⟩
  have hunder : 𝔭.comap (algebraMap A C) = maximalIdeal A := by
    rw [← hunderQ]; ext a
    simp only [Ideal.mem_comap]
    show C.val (algebraMap A C a) ∈ maximalIdeal Q ↔ _
    rw [AlgHom.commutes]

  let L := Localization.AtPrime 𝔭
  let e : L ≃ₐ[↥C] Q := IsLocalization.algEquiv 𝔭.primeCompl L Q
  let J : Ideal L := (𝔭.under A).map (algebraMap A L)
  let mkJ : L →+* L ⧸ J := Ideal.Quotient.mk J
  let θ : S →+* L ⧸ J := mkJ.comp (e.symm.toAlgHom.toRingHom.comp mk)
  have hθ : ∀ s : S, θ s = mkJ (e.symm (mk s)) := fun _ => rfl
  have hθsurj : Function.Surjective θ := by
    intro z
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (I := I) (e l)
    exact ⟨s, by rw [hθ]; show mkJ (e.symm (mk s)) = mkJ l; rw [show mk s = e l from hs, AlgEquiv.symm_apply_apply]⟩
  have hθA : ∀ a : A, θ (algebraMap A S a) = algebraMap A (L ⧸ J) a := by
    intro a
    rw [hθ, ← halgQ, IsScalarTower.algebraMap_apply A (↥C) Q, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply A (↥C) L, IsScalarTower.algebraMap_apply A L (L ⧸ J)]
    rfl
  have hθker : I ⊔ (maximalIdeal A).map (algebraMap A S) ≤ RingHom.ker θ := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hθ,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self h), map_zero, map_zero]
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, hθA, IsScalarTower.algebraMap_apply A L (L ⧸ J),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.mem_map_of_mem _ ?_
      show a ∈ 𝔭.comap (algebraMap A ↥C)
      rw [hunder]; exact ha

  let θbar : (S ⧸ (I ⊔ (maximalIdeal A).map (algebraMap A S))) →ₐ[A] (L ⧸ J) :=
    Ideal.Quotient.liftₐ _ (({ toRingHom := θ, commutes' := hθA } : S →ₐ[A] L ⧸ J)) (fun s hs => hθker hs)
  have hθbar : Function.Surjective θbar := by
    intro z
    obtain ⟨s, rfl⟩ := hθsurj z
    exact ⟨Ideal.Quotient.mk _ s, rfl⟩
  haveI : Module.Finite A (L ⧸ J) := Module.Finite.of_surjective θbar.toLinearMap hθbar
  haveI : Algebra.WeaklyQuasiFiniteAt A 𝔭 := (Algebra.weaklyQuasiFiniteAt_iff 𝔭).mpr inferInstance

  obtain ⟨S', hS'fg, r, hr𝔭, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := A) 𝔭
  haveI hS'fin : Module.Finite A ↥S' := ⟨(Submodule.fg_top _).mpr hS'fg⟩
  set ψ := Localization.awayMap S'.val.toRingHom r with hψ
  set β : ↥C →+* Localization.Away (S'.val.toRingHom r) :=
    algebraMap ↥C (Localization.Away (S'.val.toRingHom r)) with hβ
  have hawayC : ∀ x : ↥S', ψ (algebraMap ↥S' (Localization.Away r) x) = β (x : ↥C) := fun x =>
    IsLocalization.map_eq _ x
  have hpow : ∀ c : ↥C, ∃ (N : ℕ) (s' : ↥S'), (r : ↥C) ^ N * c = (s' : ↥C) := by
    intro c
    obtain ⟨z, hz⟩ := hbij.2 (β c)
    obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, haz⟩ := IsLocalization.surj (Submonoid.powers r) z
    have haz' : z * algebraMap ↥S' (Localization.Away r) (r ^ k) = algebraMap ↥S' (Localization.Away r) a := haz
    have e1 : ((r ^ k : ↥S') : ↥C) = (r : ↥C) ^ k := by simp
    have h2 : β (c * (r : ↥C) ^ k) = β ((a : ↥S') : ↥C) := by
      rw [← e1, map_mul, ← hz, ← hawayC (r ^ k), ← map_mul, haz', hawayC]
    rw [hβ, IsLocalization.eq_iff_exists (Submonoid.powers (S'.val.toRingHom r))] at h2
    obtain ⟨⟨_, j, rfl⟩, hj⟩ := h2
    refine ⟨j + k, ⟨r ^ j * a, S'.mul_mem (pow_mem r.2 j) a.2⟩, ?_⟩
    have e2 : (((⟨r ^ j * a, S'.mul_mem (pow_mem r.2 j) a.2⟩ : ↥S')) : ↥C) = (r : ↥C) ^ j * (a : ↥C) := by simp
    rw [e2, pow_add]
    have hj' : (r : ↥C) ^ j * (c * (r : ↥C) ^ k) = (r : ↥C) ^ j * (a : ↥C) := hj
    linear_combination hj'
  let 𝔫' : Ideal ↥S' := 𝔭.comap S'.val.toRingHom
  haveI : 𝔫'.IsPrime := Ideal.comap_isPrime S'.val.toRingHom 𝔭
  have h𝔫'A : 𝔫'.comap (algebraMap A ↥S') = maximalIdeal A := by
    rw [← hunder]; ext a
    simp only [Ideal.mem_comap]
    show S'.val (algebraMap A ↥S' a) ∈ 𝔭 ↔ algebraMap A ↥C a ∈ 𝔭
    rw [AlgHom.commutes]
  haveI : 𝔫'.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) 𝔫' (h𝔫'A.symm ▸ maximalIdeal.isMaximal A)
  let L' := Localization.AtPrime 𝔫'
  haveI : Module.Finite A L' := HenselianLocalRing.moduleFinite_localizationAtPrime_of_moduleFinite 𝔫'
  let g₀ : ↥S' →+* Q := (algebraMap ↥C Q).comp S'.val.toRingHom
  have hg₀ : ∀ s : ↥S', g₀ s = algebraMap ↥C Q (s : ↥C) := fun _ => rfl
  have hg₀u : ∀ y : 𝔫'.primeCompl, IsUnit (g₀ y) := by
    rintro ⟨y, hy⟩
    rw [hg₀]
    exact IsLocalization.map_units Q (⟨(y : ↥C), hy⟩ : 𝔭.primeCompl)
  let g' : L' →+* Q := IsLocalization.lift (M := 𝔫'.primeCompl) hg₀u
  have hg' : ∀ s : ↥S', g' (algebraMap ↥S' L' s) = g₀ s := fun s => IsLocalization.lift_eq hg₀u s
  let gA : L' →ₐ[A] Q :=
    { toRingHom := g'
      commutes' := fun a => by
        show g' (algebraMap A L' a) = algebraMap A Q a
        rw [IsScalarTower.algebraMap_apply A ↥S' L', hg', hg₀, Subalgebra.coe_algebraMap,
          ← IsScalarTower.algebraMap_apply A ↥C Q] }
  have hgAsurj : Function.Surjective gA := by
    intro q
    obtain ⟨⟨c, m⟩, hcm⟩ := IsLocalization.surj M q
    obtain ⟨N₁, s₁, hs₁⟩ := hpow c
    obtain ⟨N₂, s₂, hs₂⟩ := hpow m
    let t₁ : ↥S' := r ^ N₂ * s₁
    let t₂ : ↥S' := r ^ N₁ * s₂
    have ht₁ : (t₁ : ↥C) = (r : ↥C) ^ (N₁ + N₂) * c := by
      show ((r ^ N₂ * s₁ : ↥S') : ↥C) = _; simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, ← hs₁]; ring
    have ht₂ : (t₂ : ↥C) = (r : ↥C) ^ (N₁ + N₂) * m := by
      show ((r ^ N₁ * s₂ : ↥S') : ↥C) = _; simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, ← hs₂]; ring
    have ht₂𝔫 : t₂ ∈ 𝔫'.primeCompl := by
      show t₂ ∉ 𝔫'
      intro hh
      have h' : (t₂ : ↥C) ∈ 𝔭 := hh
      rw [ht₂] at h'
      rcases h𝔭p.mem_or_mem h' with h1 | h1
      · exact hr𝔭 (h𝔭p.mem_of_pow_mem _ h1)
      · exact hM𝔭 m.2 h1
    refine ⟨IsLocalization.mk' L' t₁ ⟨t₂, ht₂𝔫⟩, ?_⟩
    show g' (IsLocalization.mk' L' t₁ ⟨t₂, ht₂𝔫⟩) = q
    have h1 : g' (IsLocalization.mk' L' t₁ ⟨t₂, ht₂𝔫⟩) * g₀ t₂ = g₀ t₁ := by
      rw [← hg' t₂, ← map_mul, IsLocalization.mk'_spec, hg']
    have h2 : q * g₀ t₂ = g₀ t₁ := by
      rw [hg₀, hg₀, ht₁, ht₂, map_mul, map_mul, ← hcm]; ring
    exact (hg₀u ⟨t₂, ht₂𝔫⟩).mul_right_cancel (h1.trans h2.symm)
  have hfinQ : Module.Finite A Q := Module.Finite.of_surjective gA.toLinearMap hgAsurj
  refine ⟨hfinQ, ?_⟩

  let K : Ideal Q := (maximalIdeal A).map (algebraMap A Q)
  by_cases hK : K = ⊤
  · exact ⟨1, by rw [show (maximalIdeal A).map (algebraMap A (S ⧸ Ideal.span ({h} : Set S))) = K from rfl, hK]; trivial⟩
  let R := Q ⧸ K
  haveI : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr hK
  haveI : IsLocalRing R := IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  haveI : Module.Finite A R := Module.Finite.of_surjective (Ideal.Quotient.mkₐ A K).toLinearMap Ideal.Quotient.mk_surjective

  haveI : IsArtinianRing R := by
    letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
    letI algκ : Algebra (A ⧸ maximalIdeal A) R :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    haveI : IsScalarTower A (A ⧸ maximalIdeal A) R := IsScalarTower.of_algebraMap_eq fun a => rfl
    haveI : Module.Finite (A ⧸ maximalIdeal A) R := Module.Finite.of_restrictScalars_finite A _ _
    exact IsArtinianRing.of_finite (A ⧸ maximalIdeal A) R
  have hKle : K ≤ maximalIdeal Q := by
    show (maximalIdeal A).map (algebraMap A Q) ≤ maximalIdeal Q
    rw [Ideal.map_le_iff_le_comap]; exact fun a ha => hmQ a ha
  let Tt : R := Ideal.Quotient.mk K (mk T)
  have hTt : Tt ∈ maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hT
    apply hmkunit
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk K), Ideal.Quotient.eq] at hy

    have hmem : mk T * y - 1 ∈ maximalIdeal Q := hKle hy
    by_contra hnu
    have : mk T * y ∈ maximalIdeal Q := Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    have h1 : (1 : Q) ∈ maximalIdeal Q := by
      have := Ideal.sub_mem _ this hmem
      rwa [sub_sub_cancel] at this
    exact (Ideal.ne_top_iff_one _).mp (maximalIdeal.isMaximal Q).ne_top h1
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hjac : maximalIdeal R ≤ Ideal.jacobson (⊥ : Ideal R) := IsLocalRing.maximalIdeal_le_jacobson _
  refine ⟨k, ?_⟩
  show (mk T) ^ k ∈ K
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  show Tt ^ k = 0
  have : Tt ^ k ∈ (Ideal.jacobson (⊥ : Ideal R)) ^ k := Ideal.pow_mem_pow (hjac hTt) k
  rw [hk] at this
  exact this

end S_HenselianLocalRing_moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors
end P2MW
export P2MW.S_HenselianLocalRing_moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors (solution)
