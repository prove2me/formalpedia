-- Prove2me | solution 1 for McFadden1974.IIA.binary_odds_eq
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T12:02:53.210432+00:00
-- url     : https://prove2.me/submissions/de9c94c7-5712-4a0e-9f8b-953c176b3a7d

import Mathlib
import Definitions.Def_McFadden1974_IIA_ChoiceModel

namespace HProof

open McFadden1974.IIA

variable {X S : Type*} [DecidableEq X]

private theorem binaryOdds
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss) (hA1 : Axiom1 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x y : X) (hx : x ∈ B) (hy : y ∈ B)
    (hxy : x ≠ y) (hpos : 0 < P s B x) :
    0 < P s {x, y} x ∧ P s {x, y} y / P s {x, y} x = P s B y / P s B x := by
  have hpair := hprob s {x, y} (hpairs B hB x hx y hy hxy)
  have hnonneg := hpair.1 x (by simp)
  have hsum : P s {x, y} x + P s {x, y} y = 1 := by
    simpa [Finset.sum_pair hxy] using hpair.2
  have hiia := hA1 s B hB x hx y hy
  have hbin : 0 < P s {x, y} x := by
    by_contra hn
    have heq : P s {x, y} x = 0 := le_antisymm (le_of_not_gt hn) hnonneg
    rw [heq, zero_add] at hsum
    rw [heq, hsum, zero_mul, one_mul] at hiia
    linarith
  refine ⟨hbin, (div_eq_div_iff (ne_of_gt hbin) (ne_of_gt hpos)).2 ?_⟩
  nlinarith [hiia]

end HProof

open McFadden1974.IIA

theorem solution {X S : Type*} [DecidableEq X]
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss) (hA1 : Axiom1 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x y : X) (hx : x ∈ B) (hy : y ∈ B) (hxy : x ≠ y)
    (hpos : 0 < P s B x) :
    0 < P s {x, y} x ∧ P s {x, y} y / P s {x, y} x = P s B y / P s B x := by
  exact HProof.binaryOdds P poss hprob hpairs hA1 s B hB x y hx hy hxy hpos
