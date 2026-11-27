-- Prove2me | solution 1 for MaxCutSample2027.Coreset.theorem_2_1
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:44:52.776804+00:00
-- url     : https://prove2.me/submissions/c814617d-ffbd-4332-bfb0-a9b22e7355fb

import Theorems.Thm_MaxCutSample2027_Coreset_lemma_2_4
import Theorems.Thm_MaxCutSample2027_Coreset_theorem_2_9
import Definitions.Def_MaxCutSample2027_Coreset_model
open scoped BigOperators

set_option autoImplicit false

open MaxCutSample2027
open MaxCutSample2027.Coreset

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : V → V → ℝ) (p : V → ℝ)
    (hA : IsWeightMatrix A) (hp : IsPositiveProbabilityVector p)
    (k : ℕ) (hk : 1 ≤ k) :
    sampleAverage p k (fun x =>
      |(maxCut (Ahat A p x) - maxCut A) / (Fintype.card V : ℝ) ^ 2|) ≤
      48 * H A p / Real.sqrt (k : ℝ) := by
  have h := theorem_2_9 A p hA hp k hk
  have normalized (x : Fin k → V) :
      |(maxCut (Ahat A p x) - maxCut A) / (Fintype.card V : ℝ) ^ 2| =
        |FK (K A p) (empirical x) - FK (K A p) p| := by
    obtain ⟨hmain, hsamp⟩ := lemma_2_4 A p hA hp k hk x
    rw [hmain, hsamp, sub_div]
  simp only [normalized]
  exact h
