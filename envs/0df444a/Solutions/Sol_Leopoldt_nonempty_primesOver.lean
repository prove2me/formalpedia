-- Prove2me | solution 1 for Leopoldt.nonempty_primesOver
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-03T09:00:22.984883+00:00
-- url     : https://prove2.me/submissions/999f5e91-d88e-4862-97df-ab036029b04a

import Definitions.Def_LeopoldtDefect

open NumberField

theorem solution (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    Nonempty (Leopoldt.PrimesOver p K) := by
  obtain ⟨Q, hQmax, hQlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)})
  have hpne : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out (p := p.Prime)).ne_zero
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have hmem : (p : ℤ) ∈ Q.under ℤ := by
      rw [← Ideal.over_def Q (Ideal.span {(p : ℤ)})]
      exact Ideal.subset_span rfl
    simpa [Ideal.under, Ideal.mem_comap] using hmem
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpQ
    exact hpne hpQ
  exact ⟨⟨⟨Q, hQmax.isPrime, hQne⟩, hpQ⟩⟩
