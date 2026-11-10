-- Prove2me | solution 1 for Grunbaum2003.g_theorem_sufficiency_pos_g1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:01:03.872206+00:00
-- url     : https://prove2.me/submissions/84a4a142-be41-4758-9f28-4e1f5c99435b

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_gTheoremMatrix_row_one_top_columns_and_g2_zero_sum
import Theorems.Thm_Grunbaum2003_exists_stacked_simplicial_polytope_faceCount
import Theorems.Thm_Grunbaum2003_g_theorem_sufficiency_pos_g2
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

open Grunbaum2003

theorem solution (d : ℕ) (hd : 4 ≤ d) (g : ℕ → ℕ)
    (hg : IsMSequence (d / 2) g) (hg1 : 0 < g 1) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  rcases Nat.eq_zero_or_pos (g 2) with hg2_zero | hg2_pos
  · obtain ⟨P, hP, hP_f⟩ := Grunbaum2003.exists_stacked_simplicial_polytope_faceCount d hd (g 1) hg1
    refine ⟨P, hP, fun j => ?_⟩
    rw [hP_f j,
      ← Grunbaum2003.gTheoremMatrix_row_one_top_columns_and_g2_zero_sum.2.2.2.2.1 (by omega) hg hg2_zero j]
  · exact Grunbaum2003.g_theorem_sufficiency_pos_g2 d hd g hg hg1 hg2_pos
