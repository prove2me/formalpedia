-- Prove2me | solution 1 for Grunbaum2003.g_theorem_sufficiency_pos_g2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:38:51.795947+00:00
-- url     : https://prove2.me/submissions/9277e588-402a-45f4-af31-75f3698842cc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_gTheoremMatrix_upper_triangular_and_nonstacked_g2
import Theorems.Thm_Grunbaum2003_g_theorem_sufficiency_pos_g2_from_upper_triangular
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

open Grunbaum2003

theorem solution (d : ℕ) (hd : 4 ≤ d) (g : ℕ → ℕ)
    (hg : IsMSequence (d / 2) g) (hg1 : 0 < g 1) (hg2 : 0 < g 2) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val := by
  obtain ⟨hZero, hDiag, hPref, hRow0, _⟩ :=
    Grunbaum2003.gTheoremMatrix_upper_triangular_and_nonstacked_g2 d hd
  obtain ⟨P, hP, _, _, hRep⟩ :=
    Grunbaum2003.g_theorem_sufficiency_pos_g2_from_upper_triangular d hd g hg hg1 hg2
      ⟨hZero, hDiag, hPref g, hRow0⟩
  exact ⟨P, hP, hRep⟩
