-- Prove2me | solution 1 for Grunbaum2003.g_theorem_necessity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T01:29:01.466893+00:00
-- url     : https://prove2.me/submissions/6efd0d1a-326d-426b-aab9-1aa332732fa4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_g_theorem_simplex_and_zero_tail_characterization
import Theorems.Thm_Grunbaum2003_g_theorem_necessity_gt_simplex
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

open Grunbaum2003

theorem solution (d : ℕ) (hd : 4 ≤ d) (P : Set (Fin d → ℝ))
    (hP : IsSimplicialDPolytope P) :
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  rcases le_or_gt (faceCount P 0) (d + 1) with hle | hgt
  · exact Grunbaum2003.g_theorem_simplex_and_zero_tail_characterization.2.2 d P hP hle
  · exact Grunbaum2003.g_theorem_necessity_gt_simplex d hd P hP hgt
