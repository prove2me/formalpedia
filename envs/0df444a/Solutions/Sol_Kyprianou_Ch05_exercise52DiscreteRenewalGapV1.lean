-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52DiscreteRenewalGapV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:35:47.678999+00:00
-- url     : https://prove2.me/submissions/7aa76dec-770b-41f4-a1ae-1223004abcb7

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_exercise52DiscretePassageToGapV1
import Theorems.Thm_Kyprianou_Ch05_exercise52DiscreteGapToPassageV1
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
/-- Combine the two directions of the discrete renewal gap characterization. -/
theorem solution
    (S : ℕ → ℝ) (hmono : Monotone S) (h0 : S 0 = 0)
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y) :
    let n := sInf {k : ℕ | 0 < k ∧ x < S k}
    (u < S n - x ∧ y < x - S (n-1)) ↔
    ∃ a b : ℚ, (a : ℝ) < x-y ∧ x+u < (b : ℝ) ∧
      (∀ k : ℕ, S k ≤ (a : ℝ) ∨ (b : ℝ) ≤ S k) ∧
      ∃ k : ℕ, (b : ℝ) ≤ S k := by
  exact ⟨exercise52DiscretePassageToGapV1 S hmono h0 x u y hx hu hy,
    exercise52DiscreteGapToPassageV1 S hmono h0 x u y hx hu hy⟩