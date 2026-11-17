-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassage_rationalApproxEvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T19:02:52.244272+00:00
-- url     : https://prove2.me/submissions/2794825b-b971-4624-81ae-c362fdec50d6

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_passageApproxEpsilonCofinal
import Theorems.Thm_Kyprianou_Ch01_firstUpperPassage_le_iff_rationalApproachingCrossings

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01 Set Filter
open scoped NNReal
set_option autoImplicit false
universe u

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (s : ℝ) (t v : ℝ≥0) (htv : t < v) :
    {ω | Kyprianou.Ch01.firstUpperPassage X s ω ≤ (t : WithTop ℝ≥0)} =
      ⋂ n : ℕ, {ω | ∃ q : ℚ, 0 < (q : ℝ) ∧
        (q : ℝ) ≤ ((t + (v - t) / ((n : ℝ≥0) + 2) : ℝ≥0) : ℝ) ∧
        s < X (Real.toNNReal (q : ℝ)) ω} := by
  classical
  let eps : ℕ → ℝ≥0 := fun n => (v - t) / (n + 2)
  let horizon : ℕ → ℝ≥0 := fun n => t + eps n
  change {ω | firstUpperPassage X s ω ≤ (t : WithTop ℝ≥0)} =
    ⋂ n : ℕ, {ω | ∃ q : ℚ, 0 < (q : ℝ) ∧
      (q : ℝ) ≤ ((horizon n : ℝ≥0) : ℝ) ∧
      s < X (Real.toNNReal (q : ℝ)) ω}
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro hw n
    have heps : 0 < eps n :=
      div_pos (tsub_pos_of_lt htv) (by positivity)
    obtain ⟨q, hq0, hqtime, hqcross⟩ :=
      (firstUpperPassage_le_iff_rationalApproachingCrossings
        X ω (hContinuous ω) s t).mp hw (eps n) heps
    exact ⟨q, hq0, le_of_lt (by simpa [horizon] using hqtime), hqcross⟩
  · intro hw
    apply (firstUpperPassage_le_iff_rationalApproachingCrossings
      X ω (hContinuous ω) s t).mpr
    intro e he
    obtain ⟨n, hn⟩ := passageApproxEpsilonCofinal t v htv e he
    obtain ⟨q, hq0, hqtime, hqcross⟩ := hw n
    refine ⟨q, hq0, ?_, hqcross⟩
    have hh : horizon n < t + e := by
      dsimp [horizon, eps]
      simpa only [add_comm] using (add_lt_add_left hn t)
    have hhre : ((horizon n : ℝ≥0) : ℝ) < ((t + e : ℝ≥0) : ℝ) := by
      exact_mod_cast hh
    exact lt_of_le_of_lt hqtime hhre
