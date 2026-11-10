-- Prove2me | solution 1 for Grunbaum2003.g_theorem_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T01:29:02.394985+00:00
-- url     : https://prove2.me/submissions/e35fe0d4-b2c3-4c95-92c4-3f9e8476b686

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_g_theorem_simplex_and_zero_tail_characterization
import Theorems.Thm_Grunbaum2003_g_theorem_sufficiency_pos_g1
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

open Grunbaum2003

theorem solution (d : ℕ) (hd : 4 ≤ d) (g : ℕ → ℕ)
    (hg : IsMSequence (d / 2) g) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  rcases Nat.eq_zero_or_pos (g 1) with hg0 | hgpos
  · exact Grunbaum2003.g_theorem_simplex_and_zero_tail_characterization.2.1 d g hg hg0
  · exact Grunbaum2003.g_theorem_sufficiency_pos_g1 d hd g hg hgpos
