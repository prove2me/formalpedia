-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52DiscreteGapToPassageV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:35:44.726304+00:00
-- url     : https://prove2.me/submissions/069fa664-020b-4566-ba65-c8be8049d3f9

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
/-- A rational gap implies strict discrete renewal passage margins. -/
theorem solution
    (S : ℕ → ℝ) (hmono : Monotone S) (h0 : S 0 = 0)
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    let n := sInf {k : ℕ | 0 < k ∧ x < S k}
    (∃ a b : ℚ, (a : ℝ) < x-y ∧ x+u < (b : ℝ) ∧
      (∀ k : ℕ, S k ≤ (a : ℝ) ∨ (b : ℝ) ≤ S k) ∧
      ∃ k : ℕ, (b : ℝ) ≤ S k) → (u < S n - x ∧ y < x - S (n-1)) := by
  dsimp only
  let A : Set ℕ := {k | 0 < k ∧ x < S k}
  let n := sInf A
  rintro ⟨a,b,ha,hb,hgap,k,hk⟩
  have hk0 : 0 < k := by
    by_contra! h
    have he : k = 0 := Nat.eq_zero_of_le_zero h
    rw [he,h0] at hk
    linarith
  have hA : A.Nonempty := ⟨k,hk0,by linarith⟩
  have hn : n ∈ A := Nat.sInf_mem hA
  have hn0 : 0 < n := hn.1
  have hnhi : (b : ℝ) ≤ S n := by
    rcases hgap n with h | h
    · exfalso; linarith [hn.2]
    · exact h
  have hnpre : S (n-1) ≤ x := by
    by_contra! h
    have hp : 0 < n-1 := by
      by_contra! hh
      have he : n-1 = 0 := Nat.eq_zero_of_le_zero hh
      rw [he,h0] at h
      linarith
    have hh : n ≤ n-1 := Nat.sInf_le (show n-1 ∈ A from ⟨hp,h⟩)
    omega
  have hnlo : S (n-1) ≤ (a : ℝ) := by
    rcases hgap (n-1) with h | h
    · exact h
    · exfalso; linarith
  constructor <;> linarith
