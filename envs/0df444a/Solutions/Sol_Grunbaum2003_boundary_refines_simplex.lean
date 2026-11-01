-- Prove2me | solution 1 for Grunbaum2003.boundary_refines_simplex
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:28:38.125825+00:00
-- url     : https://prove2.me/submissions/0c1cf558-5489-4f88-8af6-dd568f19c3ad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_BoundaryRefines
import Theorems.Thm_Grunbaum2003_boundary_refines_simplex_zero_dim
import Theorems.Thm_Grunbaum2003_boundary_refines_simplex_pos_dim
import Mathlib.LinearAlgebra.AffineSpace.Independent

set_option autoImplicit false

namespace Grunbaum2003

/-- Grünbaum (2003), Theorem 11.1.1 (p. 200): the boundary complex of every `d`-polytope
is a refinement of the boundary complex of any `d`-simplex in `ℝ^d`. -/
theorem boundary_refines_simplex_sol (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : IsDPolytope P)
    (v : Fin (d + 1) → (Fin d → ℝ)) (hv : AffineIndependent ℝ v) :
    BoundaryRefines P (convexHull ℝ (Set.range v)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact boundary_refines_simplex_zero_dim P hP v hv
  · exact boundary_refines_simplex_pos_dim d hd P hP v hv

end Grunbaum2003

theorem solution (d : ℕ)
    (P : Set (Fin d → ℝ)) (hP : Grunbaum2003.IsDPolytope P)
    (v : Fin (d + 1) → (Fin d → ℝ)) (hv : AffineIndependent ℝ v) :
    Grunbaum2003.BoundaryRefines P (convexHull ℝ (Set.range v)) :=
  Grunbaum2003.boundary_refines_simplex_sol d P hP v hv
