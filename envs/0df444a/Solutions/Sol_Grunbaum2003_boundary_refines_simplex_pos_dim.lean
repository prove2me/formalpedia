-- Prove2me | solution 1 for Grunbaum2003.boundary_refines_simplex_pos_dim
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:05:45.39032+00:00
-- url     : https://prove2.me/submissions/4f4511ec-294f-4b86-9031-519c1c163852

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Theorems.Thm_Grunbaum2003_boundary_refines_simplex_one_dim
import Theorems.Thm_Grunbaum2003_boundary_refines_simplex_ge_two
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

theorem solution (d : ℕ) (hd : 0 < d)
    (P : Set (Fin d → ℝ)) (hP : Grunbaum2003.IsDPolytope P)
    (v : Fin (d + 1) → (Fin d → ℝ)) (hv : AffineIndependent ℝ v) :
    Grunbaum2003.BoundaryRefines P (convexHull ℝ (Set.range v)) := by
  by_cases hd1 : d = 1
  · subst d
    exact Grunbaum2003.boundary_refines_simplex_one_dim P hP v hv
  · have hd2 : 2 ≤ d := by omega
    exact Grunbaum2003.boundary_refines_simplex_ge_two d hd2 P hP v hv
