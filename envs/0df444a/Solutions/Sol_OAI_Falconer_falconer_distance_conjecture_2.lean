-- Prove2me | solution 2 for OAI.Falconer.falconer_distance_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dangnguyen
-- created : 2026-11-03T21:00:03.625007+00:00
-- url     : https://prove2.me/submissions/4d40b53f-7a2a-4905-aacc-49f3c431e08f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FalconerPath_defs
import Theorems.Thm_FalconerPath_starting_pair_measures
import Theorems.Thm_FalconerPath_completion

noncomputable section
open Set MeasureTheory
open scoped ENNReal

open FalconerPath

theorem solution :
    ∀ (d : ℕ), 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
      (d : ℝ≥0∞) / 2 < dimH E →
        0 < volume {r : ℝ | ∃ x ∈ E, ∃ y ∈ E, dist x y = r} := by
  intro d hd E hE hdim
  rcases starting_pair_measures hd E hE hdim 1 zero_lt_one with hdist | hpair
  · exact hdist
  · exact (completion hd E hE 1 zero_lt_one (Classical.choice hpair)).2
