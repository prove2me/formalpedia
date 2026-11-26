-- Prove2me | solution 1 for Kyprianou.Ch05.cutoffAntitoneMonotoneDifference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:01:56.77042+00:00
-- url     : https://prove2.me/submissions/1e5a3133-8c97-439b-ab18-1f3df0198584

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- A cutoff antitone tail is the difference of two monotone unit-bounded functions. -/
theorem solution
    (g : Real → Real) (hg : Antitone g)
    (hn : ∀ t, 0 ≤ g t) (hb : ∀ t, g t ≤ 1) (y : Real) :
    ∃ p q : Real → Real, Monotone p ∧ Monotone q ∧
      (∀ t, 0 ≤ p t) ∧ (∀ t, p t ≤ 1) ∧
      (∀ t, 0 ≤ q t) ∧ (∀ t, q t ≤ 1) ∧
      (∀ t, (if y < t then g t else 0) = p t-q t) := by
  let p : Real → Real := fun t => if y < t then 1 else 0
  let q : Real → Real := fun t => if y < t then 1-g t else 0
  have hp : Monotone p := by
    intro a b hab
    dsimp [p]
    split <;> split <;> first | linarith | norm_num
  have hq : Monotone q := by
    intro a b hab
    dsimp [q]
    split <;> split <;> first | linarith [hg hab, hb b] | norm_num
  refine ⟨p,q,hp,hq,?_,?_,?_,?_,?_⟩
  · intro t; dsimp [p]; split <;> norm_num
  · intro t; dsimp [p]; split <;> norm_num
  · intro t; dsimp [q]; split <;> linarith [hb t]
  · intro t; dsimp [q]; split <;> linarith [hn t]
  · intro t; dsimp [p,q]; split <;> simp_all
