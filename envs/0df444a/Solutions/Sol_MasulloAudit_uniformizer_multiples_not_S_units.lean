-- Prove2me | solution 1 for MasulloAudit.uniformizer_multiples_not_S_units
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:51:32.701561+00:00
-- url     : https://prove2.me/submissions/f94bc2fc-1cae-4d28-9c94-376b6d2b0f33

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Set.Finite.Basic

/-- For every prime `p` and every finite set `S'` of primes, there are infinitely many
`ξ ∈ ℚ^×` with `v_p(ξ) = 1` that are not `S'`-units (some prime `q ∉ S'` has `v_q(ξ) ≠ 0`). -/
theorem solution (p : ℕ) [hp : Fact p.Prime] (S' : Finset ℕ) :
    {ξ : ℚ | ξ ≠ 0 ∧ padicValRat p ξ = 1 ∧
      ∃ q : ℕ, q.Prime ∧ q ∉ S' ∧ padicValRat q ξ ≠ 0}.Infinite := by
  -- injective map from primes q > max(S') + p into the set
  have key : ∀ q : ℕ, q.Prime → S'.sup id + p < q →
      ((p : ℚ) * q) ∈ {ξ : ℚ | ξ ≠ 0 ∧ padicValRat p ξ = 1 ∧
        ∃ q : ℕ, q.Prime ∧ q ∉ S' ∧ padicValRat q ξ ≠ 0} := by
    intro q hq hlt
    have : Fact q.Prime := ⟨hq⟩
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
    have hqS : q ∉ S' := by
      intro h
      have := Finset.le_sup (f := id) h
      simp at this; omega
    have hpq : p ≠ q := by omega
    refine ⟨mul_ne_zero hp0 hq0, ?_, q, hq, hqS, ?_⟩
    · rw [padicValRat.mul hp0 hq0, padicValRat.self hp.out.one_lt,
        padicValRat.of_nat]
      have : padicValNat p q = 0 :=
        padicValNat_primes hpq
      simp [this]
    · rw [padicValRat.mul hp0 hq0, padicValRat.self hq.one_lt,
        padicValRat.of_nat]
      have : padicValNat q p = 0 := padicValNat_primes (Ne.symm hpq)
      simp [this]
  have hinf : {q : ℕ | q.Prime ∧ S'.sup id + p < q}.Infinite := by
    apply Set.infinite_of_not_bddAbove
    rintro ⟨B, hB⟩
    obtain ⟨q, hge, hq⟩ := Nat.exists_infinite_primes (S'.sup id + p + B + 1)
    have := hB ⟨hq, by omega⟩
    omega
  have hinj : Set.InjOn (fun q : ℕ => (p : ℚ) * q) {q : ℕ | q.Prime ∧ S'.sup id + p < q} := by
    intro a _ b _ h
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have := mul_left_cancel₀ hp0 h
    exact_mod_cast this
  refine Set.Infinite.mono ?_ (hinf.image hinj)
  rintro _ ⟨q, ⟨hq, hlt⟩, rfl⟩
  exact key q hq hlt

