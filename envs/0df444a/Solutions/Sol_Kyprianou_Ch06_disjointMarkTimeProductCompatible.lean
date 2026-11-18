-- Prove2me | solution 1 for Kyprianou.Ch06.disjointMarkTimeProductCompatible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:19:25.164137+00:00
-- url     : https://prove2.me/submissions/23581903-d2e9-440c-8b19-8acaf726d25b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
set_option autoImplicit false

theorem solution
    {E : Type} (a k : Nat) (marks : Fin a → Set E)
    (hDisjoint : ∀ i j : Fin a, i ≠ j →
      Disjoint (marks i) (marks j))
    (starts stops : Fin k → NNReal)
    (hTimes : ∀ i j : Fin k, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i)
    (p q : Fin (a * k)) (hpq : p ≠ q) :
    let e : Fin (a * k) ≃ Fin a × Fin k := (finProdFinEquiv).symm
    stops (e p).2 ≤ starts (e q).2 ∨
    stops (e q).2 ≤ starts (e p).2 ∨
    Disjoint (marks (e p).1) (marks (e q).1) := by
  let e : Fin (a * k) ≃ Fin a × Fin k :=
    (finProdFinEquiv).symm
  change stops (e p).2 ≤ starts (e q).2 ∨
    stops (e q).2 ≤ starts (e p).2 ∨
    Disjoint (marks (e p).1) (marks (e q).1)
  by_cases hMark : (e p).1 = (e q).1
  · have hTime : (e p).2 ≠ (e q).2 := by
      intro hEq
      apply hpq
      apply e.injective
      exact Prod.ext hMark hEq
    rcases hTimes (e p).2 (e q).2 hTime with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (hDisjoint _ _ hMark))
