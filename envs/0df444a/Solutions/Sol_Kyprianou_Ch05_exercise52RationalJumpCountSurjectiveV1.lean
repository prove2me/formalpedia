-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52RationalJumpCountSurjectiveV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:32:38.846695+00:00
-- url     : https://prove2.me/submissions/15618fd5-2041-4692-b474-6ec110eb34c3

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_sourceJumpCountMonotoneAndLtIffPublic
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
/-- Regular positive arrival times attain every jump count at a rational time. -/
theorem solution
    (T : ℕ → ℝ) (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (h0 : 0 < T 0) :
    Function.Surjective (fun q : ℚ => ProbabilityTheory.jumpCount T
      (Real.toNNReal q : ℝ)) := by
  intro n
  have h := (Kyprianou.Ch01.sourceJumpCountMonotoneAndLtIffPublic T hmono htop).1
  cases n with
  | zero =>
    refine ⟨0, Nat.eq_zero_of_not_pos ?_⟩
    intro hp
    have hh := (h 0 (Real.toNNReal (0 : ℚ) : ℝ)).1 hp
    simp at hh
    exact (not_lt_of_ge hh) h0
  | succ n =>
    obtain ⟨q,hq,hq'⟩ := exists_rat_btwn (hmono (Nat.lt_succ_self n))
    have hq0 : 0 ≤ (q : ℝ) := (h0.le.trans (hmono.monotone (Nat.zero_le n))).trans hq.le
    refine ⟨q, ?_⟩
    change ProbabilityTheory.jumpCount T (Real.toNNReal q : ℝ) = n+1
    rw [Real.coe_toNNReal _ hq0]
    have hl := (h n q).2 hq.le
    have hr : ¬ n+1 < ProbabilityTheory.jumpCount T q :=
      fun hc => (not_lt_of_ge ((h (n+1) q).1 hc)) hq'
    omega
