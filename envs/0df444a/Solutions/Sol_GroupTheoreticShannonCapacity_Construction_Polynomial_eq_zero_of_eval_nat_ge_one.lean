-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.Construction.Polynomial.eq_zero_of_eval_nat_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:32.036279+00:00
-- url     : https://prove2.me/submissions/d4cef717-ce3a-4d0e-a7d3-e03f1d4e9eab

import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Definitions.Def_GroupTheoreticShannonCapacity_Construction

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.Construction
open Matrix
namespace GroupTheoreticShannonCapacity.Construction
namespace Polynomial
theorem _root_.solution (P : Polynomial ℚ)
    (h : ∀ s : ℕ, s ≥ 1 → P.eval (s : ℚ) = 0) : P = 0 := by
  by_contra hne
  have hfin := Polynomial.finite_setOf_isRoot hne
  -- The set {1, 2, 3, ...} embeds into the roots
  have hinf : Set.Infinite {x : ℚ | ∃ n : ℕ, n ≥ 1 ∧ x = n} := by
    have hrange : Set.Infinite (Set.range (fun n : ℕ => (n + 1 : ℚ))) := by
      apply Set.infinite_range_of_injective
      intro n m heq
      have : (n : ℚ) + 1 = (m : ℚ) + 1 := heq
      have : (n : ℚ) = (m : ℚ) := by linarith
      exact Nat.cast_injective this
    apply Set.Infinite.mono _ hrange
    intro x hx
    simp only [Set.mem_range] at hx
    obtain ⟨n, rfl⟩ := hx
    simp only [Set.mem_setOf_eq]
    refine ⟨n + 1, by omega, ?_⟩
    simp only [Nat.cast_add, Nat.cast_one]
  have hsub : {x : ℚ | ∃ n : ℕ, n ≥ 1 ∧ x = n} ⊆ {x : ℚ | P.IsRoot x} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    obtain ⟨n, hn_ge, rfl⟩ := hx
    exact h n hn_ge
  exact hfin.not_infinite (hinf.mono hsub)
end Polynomial
end GroupTheoreticShannonCapacity.Construction
