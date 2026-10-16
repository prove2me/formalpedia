-- Prove2me | solution 1 for GroverWiki.grover_search
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-15T20:02:06.355204+00:00
-- url     : https://prove2.me/submissions/c86fbc94-5352-4782-a3f2-24a7818dbb56

import Mathlib
import Definitions.Def_GroverWiki_Defs
import Theorems.Thm_GroverWiki_iterationCount_le
import Theorems.Thm_GroverWiki_measureProb_groverState_floor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Matrix

open GroverWiki

theorem solution {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) :
    ∃ r : ℕ, r ≤ ⌈Real.pi / 4 * Real.sqrt N⌉₊ ∧
      1 - 1 / (N : ℝ) ≤ measureProb (groverState f r) ω := by
  have hN : 1 ≤ N := by
    have := ω.isLt
    omega
  refine ⟨⌊Real.pi / (4 * Real.arcsin (1 / Real.sqrt N))⌋₊, ?_, ?_⟩
  · exact GroverWiki.iterationCount_le hN
  · exact GroverWiki.measureProb_groverState_floor f ω hω
