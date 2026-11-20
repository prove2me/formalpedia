-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_family_positive_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:50:19.11966+00:00
-- url     : https://prove2.me/submissions/3c53d74b-cc54-4d80-907f-2e32f86c53df

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Mathlib.Topology.Defs.Filter
set_option autoImplicit false

open Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W) (q : ℝ) (hq : 0 ≤ q) :
    (∀ x : ℝ, 0 ≤ W q x) ∧
    MonotoneOn (W q) (Set.Ici (0 : ℝ)) ∧
    ContinuousOn (W q) (Set.Ici (0 : ℝ)) := by
  rcases hW q hq with ⟨_, _, hpos, hcont, hmono, _⟩
  exact ⟨hpos, hmono, hcont⟩
