-- Prove2me | solution 1 for Kyprianou.Ch01.sourceJumpCountMonotoneAndLtIffPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:46:45.887365+00:00
-- url     : https://prove2.me/submissions/7b329af5-5ca9-4b3f-8a7b-dcde12987814

import Mathlib
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Original source jump-count indices have a monotone first-after-time
representation for every increasing divergent arrival sequence. -/
theorem solution
    (T : ℕ → ℝ) (hmono : StrictMono T)
    (htop : Tendsto T atTop atTop) :
    (∀ (n : ℕ) (t : ℝ),
      n < ProbabilityTheory.jumpCount T t ↔ T n ≤ t) ∧
    Monotone (ProbabilityTheory.jumpCount T) := by
  classical
  have hiff : ∀ (n : ℕ) (t : ℝ),
      n < ProbabilityTheory.jumpCount T t ↔ T n ≤ t := by
    intro n t
    have hne : {m | t < T m}.Nonempty := by
      obtain ⟨m, hm⟩ := (htop.eventually_gt_atTop t).exists
      exact ⟨m, hm⟩
    unfold ProbabilityTheory.jumpCount
    constructor
    · intro h
      by_contra hlt
      push_neg at hlt
      exact absurd
        (Nat.sInf_le (show n ∈ {m | t < T m} from hlt))
        (not_le.mpr h)
    · intro h
      by_contra hle
      push_neg at hle
      have hm : sInf {m | t < T m} ∈ {m | t < T m} :=
        Nat.sInf_mem hne
      have h1 : T (sInf {m | t < T m}) ≤ T n :=
        hmono.monotone hle
      have hm' : t < T (sInf {m | t < T m}) := hm
      linarith
  have hmon : Monotone (ProbabilityTheory.jumpCount T) := by
    intro a b hab
    by_contra hcon
    push Not at hcon
    have h1 : T (ProbabilityTheory.jumpCount T b) ≤ a :=
      (hiff _ _).mp hcon
    exact absurd ((hiff _ _).mpr (h1.trans hab)) (lt_irrefl _)
  exact ⟨hiff, hmon⟩
