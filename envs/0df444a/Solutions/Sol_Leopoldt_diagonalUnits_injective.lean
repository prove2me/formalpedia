-- Prove2me | solution 1 for Leopoldt.diagonalUnits_injective
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T02:43:11.249182+00:00
-- url     : https://prove2.me/submissions/81633dac-a35d-4e7e-b00a-9ef2c655f8ff

import Definitions.Def_LeopoldtDefect

open NumberField IsDedekindDomain Leopoldt

theorem solution (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    Function.Injective (diagonalUnits p K) := by
  have hp : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : p.Prime).ne_zero)).2
      (Nat.prime_iff_prime_int.1 Fact.out)
  obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (R := ℤ) (S := 𝓞 K)
    (Ideal.span {(p : ℤ)}) ⊥ (by
      rw [Ideal.comap_bot_of_injective (algebraMap ℤ (𝓞 K)) (algebraMap ℤ (𝓞 K)).injective_int]
      exact bot_le)
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have h : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) Q := by
      rw [hQc]; exact Ideal.subset_span rfl
    simpa [Ideal.mem_comap] using h
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpQ
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hpQ
  let v : PrimesOver p K := ⟨⟨Q, hQp, hQ0⟩, hpQ⟩
  intro a b hab
  have h1 := congrArg (fun u : SemilocalUnits p K =>
    (((u v : (v.1.adicCompletionIntegers K)ˣ) : v.1.adicCompletionIntegers K) :
      v.1.adicCompletion K)) hab
  have h2 : algebraMap K (v.1.adicCompletion K) ((a : 𝓞 K) : K) =
      algebraMap K (v.1.adicCompletion K) ((b : 𝓞 K) : K) := h1
  rw [(algebraMap K (v.1.adicCompletion K)).injective.eq_iff] at h2
  exact Units.ext (RingOfIntegers.coe_injective h2)
