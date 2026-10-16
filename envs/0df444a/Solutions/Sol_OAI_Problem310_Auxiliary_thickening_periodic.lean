-- Prove2me | solution 1 for OAI.Problem310.Auxiliary.thickening_periodic
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T04:54:04.662457+00:00
-- url     : https://prove2.me/submissions/1e4215df-3ad2-492b-adb8-d4d6512acfaa

-- Source: OpenAI/math contributors, ExceptionalCenters.lean lines 87–101,
-- commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a.
-- Standalone platform adaptation and verification by Codex under the direction
-- of Alexander Richard Towell (queelius). No new mathematical argument claimed.
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening

open Metric

theorem solution (R : Set ℝ)
    (hR : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ℝ) :
    ∀ x : ℝ, x + 1 ∈ thickening ε R ↔ x ∈ thickening ε R := by
  intro x
  simp only [mem_thickening_iff]
  constructor
  · rintro ⟨z, hz, hdist⟩
    refine ⟨z - 1, ?_, ?_⟩
    · apply (hR (z - 1)).mp
      simpa using hz
    · simpa [Real.dist_eq, sub_sub] using hdist
  · rintro ⟨z, hz, hdist⟩
    refine ⟨z + 1, (hR z).mpr hz, ?_⟩
    simpa using hdist
