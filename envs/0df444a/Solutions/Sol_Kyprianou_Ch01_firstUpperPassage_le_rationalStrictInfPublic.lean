-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassage_le_rationalStrictInfPublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T12:38:11.068361+00:00
-- url     : https://prove2.me/submissions/e13896e8-78b6-44f5-bd65-fd8a932fe8d1

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.NNReal.Defs
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Restricting a strict-crossing time set to rational observations increases its infimum. -/
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (s : ℝ) :
    firstUpperPassage X s ω ≤
      ⨅ r : ℚ,
        if (0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω)
          then ((Real.toNNReal (r : ℝ)) : WithTop ℝ≥0)
          else ⊤ := by
  classical
  apply le_iInf
  intro r
  by_cases h : 0 < (r : ℝ) ∧ s < X (Real.toNNReal (r : ℝ)) ω
  · rw [if_pos h]
    have hpos : (0 : ℝ≥0) < Real.toNNReal (r : ℝ) :=
      Real.toNNReal_pos.mpr h.1
    have hex : ∃ t : ℝ≥0, 0 < t ∧ s < X t ω :=
      ⟨Real.toNNReal (r : ℝ), hpos, h.2⟩
    have hmem : Real.toNNReal (r : ℝ) ∈
        {t : ℝ≥0 | 0 < t ∧ s < X t ω} := ⟨hpos, h.2⟩
    have hle : sInf {t : ℝ≥0 | 0 < t ∧ s < X t ω} ≤
        Real.toNNReal (r : ℝ) :=
      csInf_le (OrderBot.bddBelow _) hmem
    simpa [firstUpperPassage, hex] using
      (WithTop.coe_le_coe.mpr hle)
  · simp only [if_neg h]
    exact le_top
