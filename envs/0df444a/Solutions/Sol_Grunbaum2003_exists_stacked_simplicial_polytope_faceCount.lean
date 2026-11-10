-- Prove2me | solution 1 for Grunbaum2003.exists_stacked_simplicial_polytope_faceCount
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:13:49.996226+00:00
-- url     : https://prove2.me/submissions/df85816f-9b65-4ba0-9272-11157393c607

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_exists_stacked_simplicial_polytope_of_stellar_step
import Theorems.Thm_Grunbaum2003_exists_stellar_subdivision_simplicial_polytope
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

open Grunbaum2003

theorem solution (d : ℕ) (hd : 4 ≤ d) (n : ℕ) (_hn : 0 < n) :
    ∃ P : Set (Fin d → ℝ), IsSimplicialDPolytope P ∧
      ∀ j : Fin d, (faceCount P j.val : ℤ) =
        (Nat.choose (d + 1) j.succ.val : ℤ) + (n : ℤ) * gTheoremMatrix d 1 j.succ.val :=
  Grunbaum2003.exists_stacked_simplicial_polytope_of_stellar_step.2 d hd
    (Grunbaum2003.exists_stellar_subdivision_simplicial_polytope d hd) n
