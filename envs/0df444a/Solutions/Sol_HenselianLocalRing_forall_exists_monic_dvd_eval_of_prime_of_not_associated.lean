-- Prove2me | solution 1 for HenselianLocalRing.forall_exists_monic_dvd_eval_of_prime_of_not_associated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9647b983-9b87-5d9c-9a68-a2d0a0e1fa85

import Mathlib
import Theorems.Thm_HenselianLocalRing_moduleFinite_localizationAtPrime_of_moduleFinite
import Theorems.Thm_IsLocalRing_exists_forall_sub_sum_mem_span_pair_of_prime_of_not_associated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HenselianLocalRing_forall_exists_monic_dvd_eval_of_prime_of_not_associated

set_option autoImplicit false

open IsLocalRing

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 12800000

theorem solution
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (φ : Polynomial A →+* S) (hφf : φ.EssFiniteType)
    (hm : maximalIdeal S = Ideal.span {φ (Polynomial.C ϖ), φ Polynomial.X})
    (hprime : Prime (φ (Polynomial.C ϖ)))
    (χ₀ : S →+* ResidueField A) (hχ₀ : RingHom.ker χ₀ = maximalIdeal S)
    (hχ₀C : ∀ a : A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue A a) :
    ∀ p : S, Prime p → ¬ Associated p (φ (Polynomial.C ϖ)) →
      ∀ x : S, ∃ r : Polynomial A, r.Monic ∧ p ∣ (r.map (φ.comp Polynomial.C)).eval x := by
  classical
  intro p hp hpϖ x

  let I : Ideal S := Ideal.span {p}
  let Q := S ⧸ I
  let mk : S →+* Q := Ideal.Quotient.mk I
  letI algAS : Algebra A S := (φ.comp Polynomial.C).toAlgebra
  letI algPS : Algebra (Polynomial A) S := φ.toAlgebra
  haveI : IsScalarTower A (Polynomial A) S := IsScalarTower.of_algebraMap_eq fun _ => rfl

  have halgQ : ∀ a : A, algebraMap A Q a = mk (φ (Polynomial.C a)) := fun _ => rfl

  suffices hint : IsIntegral A (mk x) by
    obtain ⟨r, hr, hr0⟩ := hint
    refine ⟨r, hr, ?_⟩
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    have : mk ((r.map (φ.comp Polynomial.C)).eval x) = Polynomial.eval₂ (algebraMap A Q) (mk x) r := by
      rw [Polynomial.eval_map, Polynomial.hom_eval₂]; rfl
    exact this.trans hr0

  obtain ⟨n, hgen⟩ :=
    IsLocalRing.exists_forall_sub_sum_mem_span_pair_of_prime_of_not_associated ϖ hϖ φ hm hprime χ₀ hχ₀ hχ₀C p hp hpϖ

  haveI : Algebra.EssFiniteType (Polynomial A) S := hφf
  haveI : Algebra.EssFiniteType A S := Algebra.EssFiniteType.comp A (Polynomial A) S
  haveI : Algebra.EssFiniteType A Q :=
    Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ A I) Ideal.Quotient.mk_surjective
  obtain ⟨C, M, hCft, hCloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra (R := A) (S := Q)).mp inferInstance
  haveI := hCft
  haveI := hCloc

  have hIne : I ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
    exact fun h => hp.not_unit (isUnit_of_dvd_one h)
  haveI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hIne
  haveI hQloc : IsLocalRing Q := IsLocalRing.of_surjective' mk Ideal.Quotient.mk_surjective
  let 𝔫 : Ideal C := (maximalIdeal Q).comap C.val
  haveI h𝔫p : 𝔫.IsPrime := Ideal.comap_isPrime C.val (maximalIdeal Q)
  have hCval : ∀ c : C, algebraMap C Q c = (c : Q) := fun _ => rfl
  have hM𝔫 : M ≤ 𝔫.primeCompl := by
    intro m hm h𝔫m
    have hu : IsUnit (algebraMap C Q m) := IsLocalization.map_units Q ⟨m, hm⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h𝔫m) hu
  haveI hloc𝔫 : IsLocalization 𝔫.primeCompl Q := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      by_contra hu
      exact hc (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu))
    · intro q
      obtain ⟨⟨c, m⟩, h⟩ := IsLocalization.surj M q
      exact ⟨⟨c, ⟨m.1, hM𝔫 m.2⟩⟩, h⟩
    · intro c₁ c₂ h
      obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := M) h
      exact ⟨⟨m.1, hM𝔫 m.2⟩, hm⟩

  have hϖQ : algebraMap A Q ϖ ∈ maximalIdeal Q := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, halgQ]
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one mk, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
    obtain ⟨d, hd⟩ := hy

    have h1 : (1 : S) ∈ maximalIdeal S := by
      have : (1 : S) = φ (Polynomial.C ϖ) * y - p * d := by rw [← hd]; ring
      rw [this, hm]
      refine Ideal.sub_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))) ?_
      have hp𝔪 : p ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hp.not_unit
      rw [hm] at hp𝔪
      exact Ideal.mul_mem_right _ _ hp𝔪
    exact (Ideal.ne_top_iff_one _).mp (maximalIdeal.isMaximal S).ne_top h1
  have hunder : 𝔫.comap (algebraMap A C) = maximalIdeal A := by
    refine ((maximalIdeal.isMaximal A).eq_of_le ?_ ?_).symm
    · exact Ideal.IsPrime.ne_top inferInstance
    · intro a ha
      rw [hϖ, Ideal.mem_span_singleton] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [Ideal.mem_comap, Ideal.mem_comap]
      show algebraMap C Q (algebraMap A C (ϖ * b)) ∈ maximalIdeal Q
      rw [← IsScalarTower.algebraMap_apply, map_mul]
      exact Ideal.mul_mem_right _ _ hϖQ

  let L := Localization.AtPrime 𝔫
  let e : L ≃ₐ[↥C] Q := IsLocalization.algEquiv 𝔫.primeCompl L Q
  let J : Ideal L := (𝔫.under A).map (algebraMap A L)
  let mkJ : L →+* L ⧸ J := Ideal.Quotient.mk J
  let θ : S →+* L ⧸ J := mkJ.comp (e.symm.toAlgHom.toRingHom.comp mk)
  have hθ : ∀ s : S, θ s = mkJ (e.symm (mk s)) := fun _ => rfl
  have hθsurj : Function.Surjective θ := by
    intro z
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (I := I) (e l)
    refine ⟨s, ?_⟩
    rw [hθ]
    show mkJ (e.symm (mk s)) = mkJ l
    rw [show mk s = e l from hs, AlgEquiv.symm_apply_apply]
  have hθA : ∀ a : A, θ (φ (Polynomial.C a)) = algebraMap A (L ⧸ J) a := by
    intro a
    rw [hθ, ← halgQ, IsScalarTower.algebraMap_apply A (↥C) Q, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply A (↥C) L, IsScalarTower.algebraMap_apply A L (L ⧸ J)]
    rfl
  have hθp : θ p = 0 := by
    rw [hθ, show mk p = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p),
      map_zero, map_zero]
  have hθϖ : θ (φ (Polynomial.C ϖ)) = 0 := by
    rw [hθA, IsScalarTower.algebraMap_apply A L (L ⧸ J), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_map_of_mem _ ?_
    show ϖ ∈ 𝔫.comap (algebraMap A ↥C)
    rw [hunder, hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hθker : Ideal.span {p, φ (Polynomial.C ϖ)} ≤ RingHom.ker θ := by
    rw [Ideal.span_le]
    rintro y hy
    rcases hy with hy | hy
    · rw [hy]; exact hθp
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hθϖ
  haveI hfinJ : Module.Finite A (L ⧸ J) := by
    let g : Fin n → L ⧸ J := fun i => θ (φ Polynomial.X) ^ (i : ℕ)
    have hg : ∀ i : Fin n, g i = θ (φ Polynomial.X) ^ (i : ℕ) := fun _ => rfl
    refine ⟨Submodule.fg_def.mpr ⟨Set.range g, Set.finite_range g, ?_⟩⟩
    refine eq_top_iff.mpr fun z _ => ?_
    obtain ⟨s, rfl⟩ := hθsurj z
    obtain ⟨c, hc⟩ := hgen s
    have h0 : θ (s - ∑ i, φ (Polynomial.C (c i)) * φ Polynomial.X ^ (i : ℕ)) = 0 := hθker hc
    rw [RingHom.map_sub, sub_eq_zero, map_sum θ] at h0
    rw [h0]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [RingHom.map_mul, RingHom.map_pow, hθA, ← hg, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Algebra.WeaklyQuasiFiniteAt A 𝔫 := (Algebra.weaklyQuasiFiniteAt_iff 𝔫).mpr inferInstance

  obtain ⟨S', hS'fg, r, hr𝔫, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := A) 𝔫
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

  let 𝔫' : Ideal ↥S' := 𝔫.comap S'.val.toRingHom
  haveI : 𝔫'.IsPrime := Ideal.comap_isPrime S'.val.toRingHom 𝔫
  have h𝔫'A : 𝔫'.comap (algebraMap A ↥S') = maximalIdeal A := by
    rw [← hunder]
    ext a
    simp only [Ideal.mem_comap]
    show S'.val (algebraMap A ↥S' a) ∈ 𝔫 ↔ algebraMap A ↥C a ∈ 𝔫
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
    exact IsLocalization.map_units Q (⟨(y : ↥C), hy⟩ : 𝔫.primeCompl)
  let g' : L' →+* Q := IsLocalization.lift (M := 𝔫'.primeCompl) hg₀u
  have hg' : ∀ s : ↥S', g' (algebraMap ↥S' L' s) = g₀ s := fun s => IsLocalization.lift_eq hg₀u s
  let gA : L' →ₐ[A] Q :=
    { toRingHom := g'
      commutes' := fun a => by
        show g' (algebraMap A L' a) = algebraMap A Q a
        rw [IsScalarTower.algebraMap_apply A ↥S' L', hg', hg₀, Subalgebra.coe_algebraMap,
          ← IsScalarTower.algebraMap_apply A ↥C Q] }

  obtain ⟨⟨c, m⟩, hcm⟩ := IsLocalization.surj M (mk x)
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
    intro h
    have h' : (t₂ : ↥C) ∈ 𝔫 := h
    rw [ht₂] at h'
    rcases h𝔫p.mem_or_mem h' with h1 | h1
    · exact hr𝔫 (h𝔫p.mem_of_pow_mem _ h1)
    · exact hM𝔫 m.2 h1
  let y : L' := IsLocalization.mk' L' t₁ ⟨t₂, ht₂𝔫⟩
  have hy : g' y = mk x := by
    have h1 : g' y * g₀ t₂ = g₀ t₁ := by
      rw [← hg' t₂, ← map_mul, IsLocalization.mk'_spec, hg']
    have h2 : mk x * g₀ t₂ = g₀ t₁ := by
      rw [hg₀, hg₀, ht₁, ht₂, map_mul, map_mul, ← hcm]; ring
    exact (hg₀u ⟨t₂, ht₂𝔫⟩).mul_right_cancel (h1.trans h2.symm)

  rw [← hy]
  exact (Algebra.IsIntegral.isIntegral (R := A) y).map gA

end S_HenselianLocalRing_forall_exists_monic_dvd_eval_of_prime_of_not_associated
end P2MW
export P2MW.S_HenselianLocalRing_forall_exists_monic_dvd_eval_of_prime_of_not_associated (solution)
