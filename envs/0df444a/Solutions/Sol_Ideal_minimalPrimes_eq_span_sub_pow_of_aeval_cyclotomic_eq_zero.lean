-- Prove2me | solution 1 for Ideal.minimalPrimes_eq_span_sub_pow_of_aeval_cyclotomic_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e82e2cbf-b54c-5ae0-abed-7b1ab929c9cb

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_minimalPrimes_eq_span_sub_pow_of_aeval_cyclotomic_eq_zero

set_option autoImplicit false

namespace IdemSplit

open Polynomial

variable {A₀ R : Type} [CommRing A₀] [CommRing R] [Algebra A₀ R]

theorem pin_unique {ℓ : ℕ} {ω : A₀}
    (hωu : ∀ i j : ℕ, i < ℓ → j < ℓ → i ≠ j → IsUnit (ω ^ i - ω ^ j))
    (ξ : R) {I : Ideal R} (hI : I ≠ ⊤) {i j : ℕ} (hi : i < ℓ) (hj : j < ℓ)
    (hiI : ξ - algebraMap A₀ R (ω ^ i) ∈ I) (hjI : ξ - algebraMap A₀ R (ω ^ j) ∈ I) : i = j := by
  by_contra hij
  apply hI
  have hmem : algebraMap A₀ R (ω ^ i - ω ^ j) ∈ I := by
    have := I.sub_mem hjI hiI
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  exact I.eq_top_of_isUnit_mem hmem ((hωu i j hi hj hij).map _)

theorem exists_pin_mem (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : A₀)) (ω : A₀) (hω : IsPrimitiveRoot ω ℓ)
    (hωu : ∀ i j : ℕ, i < ℓ → j < ℓ → i ≠ j → IsUnit (ω ^ i - ω ^ j))
    (ξ : R) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic ℓ A₀) = 0)
    (𝔭 : Ideal R) [h𝔭 : 𝔭.IsPrime] :
    ∃ j : ℕ, (1 ≤ j ∧ j < ℓ) ∧ ξ - algebraMap A₀ R (ω ^ j) ∈ 𝔭 := by
  have hℓp : ℓ.Prime := Fact.out
  have hℓpos : 0 < ℓ := hℓp.pos
  haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩
  let π : R →ₐ[A₀] R ⧸ 𝔭 := Ideal.Quotient.mkₐ A₀ 𝔭
  let φ : A₀ →+* R ⧸ 𝔭 := (π : R →+* R ⧸ 𝔭).comp (algebraMap A₀ R)
  have hφ : ∀ a, φ a = π (algebraMap A₀ R a) := fun _ => rfl

  have hne : ∀ l : ℕ, 0 < l → l < ℓ → (φ ω) ^ l ≠ 1 := by
    intro l hl hlt h1
    have hu := (hωu l 0 hlt hℓpos (by omega)).map φ
    rw [map_sub, map_pow, map_pow, pow_zero, h1, sub_self] at hu
    exact not_isUnit_zero hu
  have hω' : IsPrimitiveRoot (φ ω) ℓ :=
    (IsPrimitiveRoot.iff hℓpos).mpr ⟨by rw [← map_pow, hω.pow_eq_one, map_one], hne⟩

  have hξℓ : ξ ^ ℓ = 1 := by
    have h := congrArg (Polynomial.aeval ξ) (Polynomial.cyclotomic_prime_mul_X_sub_one A₀ ℓ)
    simp only [map_mul, map_sub, map_pow, Polynomial.aeval_X, map_one, hξ, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  have hξℓ' : (π ξ) ^ ℓ = 1 := by rw [← map_pow, hξℓ, map_one]
  obtain ⟨i, hi, hωi⟩ := hω'.eq_pow_of_pow_eq_one hξℓ'

  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hωi
    have h := congrArg π hξ
    rw [map_zero, ← Polynomial.aeval_algHom_apply, ← hωi, show (1 : R ⧸ 𝔭) = algebraMap A₀ (R ⧸ 𝔭) 1 from
      (map_one _).symm, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
      Polynomial.eval_one_cyclotomic_prime] at h
    have hu := hℓ.map (algebraMap A₀ (R ⧸ 𝔭))
    rw [map_natCast] at hu
    rw [map_natCast] at h
    exact not_isUnit_zero (h ▸ hu)
  refine ⟨i, ⟨by omega, hi⟩, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  change π ξ = π (algebraMap A₀ R (ω ^ i))
  rw [← hφ, map_pow, hωi]

end IdemSplit

open IdemSplit in
theorem solution
    (A₀ R : Type) [CommRing A₀] [CommRing R] [Algebra A₀ R]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : A₀)) (ω : A₀) (hω : IsPrimitiveRoot ω ℓ)

    (hωu : ∀ i j : ℕ, i < ℓ → j < ℓ → i ≠ j → IsUnit (ω ^ i - ω ^ j))
    (ξ : R) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic ℓ A₀) = 0) :

    (∀ 𝔭 ∈ (⊥ : Ideal R).minimalPrimes, ∃! j : ℕ, (1 ≤ j ∧ j < ℓ) ∧ ξ - algebraMap A₀ R (ω ^ j) ∈ 𝔭) ∧

    (∀ j : ℕ, 1 ≤ j → j < ℓ → IsDomain (R ⧸ Ideal.span {ξ - algebraMap A₀ R (ω ^ j)}) →
      Ideal.span {ξ - algebraMap A₀ R (ω ^ j)} ∈ (⊥ : Ideal R).minimalPrimes ∧
      ∀ 𝔭 ∈ (⊥ : Ideal R).minimalPrimes, ξ - algebraMap A₀ R (ω ^ j) ∈ 𝔭 → 𝔭 = Ideal.span {ξ - algebraMap A₀ R (ω ^ j)}) := by
  constructor
  · intro 𝔭 h𝔭
    haveI : 𝔭.IsPrime := h𝔭.1.1
    obtain ⟨j, hj, hjm⟩ := exists_pin_mem ℓ hℓ ω hω hωu ξ hξ 𝔭
    refine ⟨j, ⟨hj, hjm⟩, fun i ⟨hi, him⟩ => ?_⟩
    exact pin_unique hωu ξ (Ideal.IsPrime.ne_top ‹_›) hi.2 hj.2 him hjm
  · intro j hj1 hjℓ hdom
    set I : Ideal R := Ideal.span {ξ - algebraMap A₀ R (ω ^ j)} with hIdef
    haveI hIp : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp hdom
    have hξI : ξ - algebraMap A₀ R (ω ^ j) ∈ I := Ideal.subset_span (Set.mem_singleton _)
    constructor
    · refine ⟨⟨hIp, bot_le⟩, ?_⟩
      rintro q ⟨hq, -⟩ hqI
      haveI := hq
      obtain ⟨𝔭, h𝔭, h𝔭q⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ q)
      haveI : 𝔭.IsPrime := h𝔭.1.1
      obtain ⟨i, hi, him⟩ := exists_pin_mem ℓ hℓ ω hω hωu ξ hξ 𝔭
      have hij : i = j := pin_unique hωu ξ hIp.ne_top hi.2 hjℓ (hqI (h𝔭q him)) hξI
      subst hij
      rw [hIdef, Ideal.span_singleton_le_iff_mem]
      exact h𝔭q him
    · intro 𝔭 h𝔭 hm
      have hI𝔭 : I ≤ 𝔭 := by rw [hIdef, Ideal.span_singleton_le_iff_mem]; exact hm
      exact le_antisymm (h𝔭.2 ⟨hIp, bot_le⟩ hI𝔭) hI𝔭

end S_Ideal_minimalPrimes_eq_span_sub_pow_of_aeval_cyclotomic_eq_zero
end P2MW
export P2MW.S_Ideal_minimalPrimes_eq_span_sub_pow_of_aeval_cyclotomic_eq_zero (solution)
