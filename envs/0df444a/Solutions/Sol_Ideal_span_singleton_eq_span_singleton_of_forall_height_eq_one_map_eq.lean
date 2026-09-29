-- Prove2me | solution 1 for Ideal.span_singleton_eq_span_singleton_of_forall_height_eq_one_map_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2f985e69-6721-5e4b-b051-b965d7b72e21

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_span_singleton_eq_span_singleton_of_forall_height_eq_one_map_eq
set_option autoImplicit false
set_option maxHeartbeats 3200000
universe u

namespace CmpCore

open Ideal

section HeightOne
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

theorem height_span_singleton_eq_one {p : A} (hp0 : p ≠ 0) [hP : (Ideal.span {p}).IsPrime] :
    (Ideal.span {p}).height = 1 := by
  apply le_antisymm
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {p}) (Ideal.span {p})
      (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; exact Set.mem_singleton _)
  · exact Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hp0)

theorem ufm_of_height_one_principal
    (hprin : ∀ P : Ideal A, P.IsPrime → P.height = 1 → Submodule.IsPrincipal P) :
    UniqueFactorizationMonoid A := by
  refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun I hI hIp => ?_
  haveI := hIp

  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨Q, hQmin, hQI⟩ := Ideal.exists_minimalPrimes_le (show Ideal.span {x} ≤ I from
    (Ideal.span_singleton_le_iff_mem _).mpr hxI)
  haveI hQp : Q.IsPrime := hQmin.1.1
  have hxQ : x ∈ Q := hQmin.1.2 (Ideal.subset_span (Set.mem_singleton x))

  have hQ1 : Q.height = 1 := by
    apply le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQmin)
    exact (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hx0)).trans
      (Ideal.height_mono (hQmin.1.2))

  obtain ⟨q, hq⟩ := hprin Q hQp hQ1
  have hq0 : q ≠ 0 := by
    intro h; apply hx0
    have : x ∈ Submodule.span A {q} := hq ▸ hxQ
    rw [h] at this
    simpa using this
  have hQeq : Q = Ideal.span {q} := hq
  have hqprime : Prime q := (Ideal.span_singleton_prime hq0).mp (hQeq ▸ hQp)
  exact ⟨q, hQI (hQeq ▸ Ideal.subset_span (Set.mem_singleton q)), hqprime⟩

end HeightOne

section Local
variable {A : Type u} [CommRing A] [IsDomain A]

theorem pow_dvd_iff_algebraMap_mem {p : A} (hp : Prime p) [hP : (Ideal.span {p}).IsPrime] (g : A) (k : ℕ) :
    p ^ k ∣ g ↔ algebraMap A (Localization.AtPrime (Ideal.span {p})) g ∈
      Ideal.map (algebraMap A (Localization.AtPrime (Ideal.span {p}))) (Ideal.span {p ^ k}) := by
  constructor
  · intro h; exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton.mpr h)
  · intro h
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, e⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (Ideal.span {p}).primeCompl (Localization.AtPrime (Ideal.span {p}))).mp h
    simp only at e
    have hinj := IsLocalization.injective (Localization.AtPrime (Ideal.span {p}))
      (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {p}))
    have e' : g * s = a := hinj (by rw [map_mul]; exact e)
    have hdvd : p ^ k ∣ g * s := by rw [e']; exact Ideal.mem_span_singleton.mp ha
    have hps : ¬ p ∣ s := fun hd => hs (Ideal.mem_span_singleton.mpr hd)
    exact hp.pow_dvd_of_dvd_mul_right k hps hdvd

theorem pow_dvd_iff_of_map_eq {p : A} (hp : Prime p) [hP : (Ideal.span {p}).IsPrime] {g t : A}
    (h : Ideal.map (algebraMap A (Localization.AtPrime (Ideal.span {p}))) (Ideal.span {g}) =
      Ideal.map (algebraMap A (Localization.AtPrime (Ideal.span {p}))) (Ideal.span {t})) (k : ℕ) :
    p ^ k ∣ g ↔ p ^ k ∣ t := by
  rw [pow_dvd_iff_algebraMap_mem hp g k, pow_dvd_iff_algebraMap_mem hp t k,
    ← Ideal.span_singleton_le_iff_mem, ← Ideal.span_singleton_le_iff_mem]
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at h
  rw [h]

end Local

section Count
variable {A : Type u} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

theorem span_eq_of_forall_prime_pow_dvd_iff {g t : A} (hg : g ≠ 0) (ht : t ≠ 0)
    (h : ∀ p : A, Prime p → ∀ k : ℕ, p ^ k ∣ g ↔ p ^ k ∣ t) : Ideal.span ({g} : Set A) = Ideal.span {t} := by
  classical
  rw [Ideal.span_singleton_eq_span_singleton, ← Associates.mk_eq_mk_iff_associated]
  apply Associates.eq_of_eq_counts (Associates.mk_ne_zero.mpr hg) (Associates.mk_ne_zero.mpr ht)
  intro P hP
  obtain ⟨p, rfl⟩ := Associates.mk_surjective P
  have hpi : Irreducible p := Associates.irreducible_mk.mp hP
  have hp : Prime p := hpi.prime
  have key : ∀ {a b : A} (ha : a ≠ 0) (hb : b ≠ 0), (∀ k : ℕ, p ^ k ∣ a → p ^ k ∣ b) →
      (Associates.mk p).count (Associates.mk a).factors ≤ (Associates.mk p).count (Associates.mk b).factors := by
    intro a b ha hb hab
    have h1 := (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr ha) hP).mpr le_rfl
    rw [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at h1
    have h2 := hab _ h1
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow] at h2
    exact (Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hb) hP).mp h2
  exact le_antisymm (key hg ht fun k => (h p hp k).mp) (key ht hg fun k => (h p hp k).mpr)

end Count

end CmpCore

theorem solution
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (hprin : ∀ P : Ideal A, P.IsPrime → P.height = 1 → Submodule.IsPrincipal P)
    {g t : A} (hg : g ≠ 0) (ht : t ≠ 0)
    (h : ∀ (P : Ideal A) [P.IsPrime], P.height = 1 →
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {g}) =
        Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {t})) :
    Ideal.span ({g} : Set A) = Ideal.span {t} := by
  haveI : UniqueFactorizationMonoid A := CmpCore.ufm_of_height_one_principal hprin
  apply CmpCore.span_eq_of_forall_prime_pow_dvd_iff hg ht
  intro p hp k
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  exact CmpCore.pow_dvd_iff_of_map_eq hp (h (Ideal.span {p}) (CmpCore.height_span_singleton_eq_one hp.ne_zero)) k

end S_Ideal_span_singleton_eq_span_singleton_of_forall_height_eq_one_map_eq
end P2MW
export P2MW.S_Ideal_span_singleton_eq_span_singleton_of_forall_height_eq_one_map_eq (solution)
