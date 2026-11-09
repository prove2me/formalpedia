-- Prove2me | solution 1 for Grunbaum2003.g_theorem_necessity_gt_simplex
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:01:05.843945+00:00
-- url     : https://prove2.me/submissions/e7b4c43d-1bbe-4330-905e-36675248797e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_g_theorem_necessity_stacked_and_simplicial_facets
import Theorems.Thm_Grunbaum2003_g_theorem_necessity_nonstacked
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators Classical

open Grunbaum2003

theorem solution (d : ℕ) (hd : 4 ≤ d) (P : Set (Fin d → ℝ))
    (hP : IsSimplicialDPolytope P) (hV_gt : d + 1 < faceCount P 0) :
    ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  by_cases hStacked : ∀ j : Fin d, (faceCount P j.val : ℤ) =
      (Nat.choose (d + 1) j.succ.val : ℤ) +
        ((faceCount P 0 - (d + 1) : ℕ) : ℤ) * gTheoremMatrix d 1 j.succ.val
  · obtain ⟨g, hg, _, _, hF⟩ :=
      Grunbaum2003.g_theorem_necessity_stacked_and_simplicial_facets.2 d hd P hP hV_gt hStacked
    exact ⟨g, hg, hF⟩
  · exact Grunbaum2003.g_theorem_necessity_nonstacked d hd P hP hV_gt hStacked
