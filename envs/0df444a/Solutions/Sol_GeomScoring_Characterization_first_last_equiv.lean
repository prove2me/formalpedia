-- Prove2me | solution 1 for GeomScoring.Characterization.first_last_equiv
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T21:20:10.450771+00:00
-- url     : https://prove2.me/submissions/4371ef40-8fa5-4c7f-ac6d-42342afb52e8

import Mathlib
import Definitions.Def_GeomScoring_Characterization_Model
import Theorems.Thm_GeomScoring_Characterization_proposition_4_losers
import Theorems.Thm_GeomScoring_Characterization_proposition_4_winners

open GeomScoring.Characterization

theorem solution (M : ℕ∞) (s : ScoringRule)
    (hW : IndepUnanimousWinners M s) (hL : IndepUnanimousLosers M s) :
    ∀ k m : ℕ, k < m → (m : ℕ∞) ≤ M → AffEquiv (initSeg (s m) k) (finalSeg (s m) k) := by
  intro k m hkm hm
  obtain ⟨a, b, ha, h1⟩ := ((proposition_4_losers M s).1 hL).2 k m hkm hm
  obtain ⟨c, d, hc, h2⟩ := ((proposition_4_winners M s).1 hW).2 k m hkm hm
  -- initSeg = (s k - b)/a, s k = c * finalSeg + d
  refine ⟨c / a, (d - b) / a, div_pos hc ha, fun j => ?_⟩
  have e1 := h1 j
  have e2 := h2 j
  field_simp
  linarith
