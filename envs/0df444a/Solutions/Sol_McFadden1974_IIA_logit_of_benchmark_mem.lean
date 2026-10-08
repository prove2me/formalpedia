-- Prove2me | solution 1 for McFadden1974.IIA.logit_of_benchmark_mem
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-05T12:02:57.866841+00:00
-- url     : https://prove2.me/submissions/5202209e-0961-4098-a2b4-b427f63853f9

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

private theorem binPositive
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hpairs : PairsPossible poss) (hA2 : Axiom2 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x y : X) (hx : x ∈ B) (hy : y ∈ B) :
    0 < binProb P s x y := by
  by_cases hxy : x = y
  · simp [binProb, hxy]
  · simp only [binProb, if_neg hxy]
    exact hA2 s {x, y} (hpairs B hB x hx y hy hxy) x (by simp)

private theorem oddsRatio
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss)
    (hA1 : Axiom1 P poss) (hA2 : Axiom2 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x y : X) (hx : x ∈ B) (hy : y ∈ B) :
    binProb P s y x / binProb P s x y = P s B y / P s B x := by
  by_cases hxy : x = y
  · subst y
    simp [binProb, ne_of_gt (hA2 s B hB x hx)]
  · have h := (binaryOdds P poss hprob hpairs hA1 s B hB x y hx hy hxy
        (hA2 s B hB x hx)).2
    simpa [binProb, hxy, Ne.symm hxy, Finset.pair_comm] using h

private theorem probOdds
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss)
    (hA1 : Axiom1 P poss) (hA2 : Axiom2 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x : X) (hx : x ∈ B) :
    (∀ y ∈ B, P s B y = (binProb P s y x / binProb P s x y) * P s B x) ∧
      1 = (∑ y ∈ B, binProb P s y x / binProb P s x y) * P s B x := by
  have heq : ∀ y ∈ B,
      P s B y = (binProb P s y x / binProb P s x y) * P s B x := by
    intro y hy
    exact (div_eq_iff (ne_of_gt (hA2 s B hB x hx))).1
      (oddsRatio P poss hprob hpairs hA1 hA2 s B hB x y hx hy).symm
  refine ⟨heq, ?_⟩
  calc
    1 = ∑ y ∈ B, P s B y := (hprob s B hB).2.symm
    _ = ∑ y ∈ B, (binProb P s y x / binProb P s x y) * P s B x :=
      Finset.sum_congr rfl heq
    _ = (∑ y ∈ B, binProb P s y x / binProb P s x y) * P s B x :=
      (Finset.sum_mul _ _ _).symm

private theorem invSum
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss)
    (hA1 : Axiom1 P poss) (hA2 : Axiom2 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x : X) (hx : x ∈ B) :
    P s B x = 1 / ∑ y ∈ B, binProb P s y x / binProb P s x y := by
  have hmul := (probOdds P poss hprob hpairs hA1 hA2 s B hB x hx).2
  have hne : (∑ y ∈ B, binProb P s y x / binProb P s x y) ≠ 0 := by
    intro heq
    rw [heq, zero_mul] at hmul
    norm_num at hmul
  apply (eq_div_iff hne).2
  nlinarith [hmul]

private theorem transitiveOdds
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss)
    (hA1 : Axiom1 P poss) (hA2 : Axiom2 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x y z : X)
    (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B) :
    binProb P s y x / binProb P s x y =
      (binProb P s y z / binProb P s z y) / (binProb P s x z / binProb P s z x) := by
  rw [oddsRatio P poss hprob hpairs hA1 hA2 s B hB x y hx hy,
    oddsRatio P poss hprob hpairs hA1 hA2 s B hB z y hz hy,
    oddsRatio P poss hprob hpairs hA1 hA2 s B hB z x hz hx]
  field_simp [ne_of_gt (hA2 s B hB x hx), ne_of_gt (hA2 s B hB z hz)]

private theorem expOdds
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hpairs : PairsPossible poss) (hA2 : Axiom2 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (x z : X) (hx : x ∈ B) (hz : z ∈ B) :
    Real.exp (altSetV P s x z) = binProb P s x z / binProb P s z x := by
  exact Real.exp_log (div_pos
    (binPositive P poss hpairs hA2 s B hB x z hx hz)
    (binPositive P poss hpairs hA2 s B hB z x hz hx))

private theorem logitExtension
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss)
    (hA1 : Axiom1 P poss) (hA2 : Axiom2 P poss)
    (s : S) (B C : Finset X) (hB : B ∈ poss) (hC : C ∈ poss) (hBC : B ⊆ C)
    (z : X) (hz : z ∈ C) (x : X) (hx : x ∈ B) :
    P s B x = Real.exp (altSetV P s x z) / ∑ y ∈ B, Real.exp (altSetV P s y z) := by
  have heq : ∀ y ∈ B, binProb P s y x / binProb P s x y =
      Real.exp (altSetV P s y z) / Real.exp (altSetV P s x z) := by
    intro y hy
    rw [expOdds P poss hpairs hA2 s C hC y z (hBC hy) hz,
      expOdds P poss hpairs hA2 s C hC x z (hBC hx) hz]
    exact transitiveOdds P poss hprob hpairs hA1 hA2 s C hC x y z (hBC hx) (hBC hy) hz
  rw [invSum P poss hprob hpairs hA1 hA2 s B hB x hx]
  rw [Finset.sum_congr rfl heq, ← Finset.sum_div]
  simp only [one_div_div]

end HProof

open McFadden1974.IIA

theorem solution {X S : Type*} [DecidableEq X]
    (P : S → Finset X → X → ℝ) (poss : Set (Finset X))
    (hprob : IsSelectionProb P poss) (hpairs : PairsPossible poss)
    (hA1 : Axiom1 P poss) (hA2 : Axiom2 P poss)
    (s : S) (B : Finset X) (hB : B ∈ poss) (z : X) (hz : z ∈ B) (x : X) (hx : x ∈ B) :
    P s B x = Real.exp (altSetV P s x z) / ∑ y ∈ B, Real.exp (altSetV P s y z) := by
  exact HProof.logitExtension P poss hprob hpairs hA1 hA2 s B B hB hB (fun _ h => h) z hz x hx
