-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52DiscretePassageToGapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:37:27.778741+00:00
-- url     : https://prove2.me/submissions/f2665e57-c41e-4ea3-8658-af0e303158b0

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05
/-- Discrete renewal passage margins imply a rational gap. -/
theorem solution
    (S : ℕ → ℝ) (hmono : Monotone S) (h0 : S 0 = 0)
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    let n := sInf {k : ℕ | 0 < k ∧ x < S k}
    (u < S n - x ∧ y < x - S (n-1)) →
    ∃ a b : ℚ, (a : ℝ) < x-y ∧ x+u < (b : ℝ) ∧
      (∀ k : ℕ, S k ≤ (a : ℝ) ∨ (b : ℝ) ≤ S k) ∧
      ∃ k : ℕ, (b : ℝ) ≤ S k := by
  dsimp only
  let A : Set ℕ := {k | 0 < k ∧ x < S k}
  let n := sInf A
  rintro ⟨ho,hl⟩
  change u < S n - x at ho
  change y < x - S (n-1) at hl
  have hn0 : 0 < n := by
    by_contra! h
    have he : n = 0 := Nat.eq_zero_of_le_zero h
    rw [he,h0] at ho
    linarith
  obtain ⟨a,ha,ha'⟩ := exists_rat_btwn (show S (n-1) < x-y by linarith)
  obtain ⟨b,hb,hb'⟩ := exists_rat_btwn (show x+u < S n by linarith)
  refine ⟨a,b,ha',hb,?_,n,hb'.le⟩
  intro k
  by_cases hk : k < n
  · exact Or.inl ((hmono (by omega : k ≤ n-1)).trans ha.le)
  · exact Or.inr (hb'.le.trans (hmono (le_of_not_gt hk)))
