-- Prove2me | solution 1 for Grunbaum2003.simplicial_three_polytope_euler_relations
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T22:41:15.512508+00:00
-- url     : https://prove2.me/submissions/6b78cdb4-d5cb-4adc-8e6d-ce0dc2bcb7be

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Theorems.Thm_Grunbaum2003_simplicial_three_polytope_euler_from_edge_ridge_and_crossing_counts
import Theorems.Thm_Grunbaum2003_simplicial_three_polytope_edge_in_two_facets_and_vertex_two_crossings

set_option autoImplicit false

open Grunbaum2003

theorem solution (P : Set (Fin 3 → ℝ))
    (hP : IsSimplicialDPolytope P) :
    faceCount P 0 + faceCount P 2 = faceCount P 1 + 2 ∧
      3 * faceCount P 2 = 2 * faceCount P 1 :=
  Grunbaum2003.simplicial_three_polytope_euler_from_edge_ridge_and_crossing_counts P hP
    (fun V ℰ ℱ hV hℰ hℱ =>
      Grunbaum2003.simplicial_three_polytope_edge_in_two_facets_and_vertex_two_crossings
        P hP V ℰ ℱ hV hℰ hℱ)
