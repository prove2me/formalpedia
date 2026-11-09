-- Prove2me | solution 1 for Grunbaum2003.simplicial_three_polytope_edge_in_two_facets_and_vertex_two_crossings
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T23:08:42.375192+00:00
-- url     : https://prove2.me/submissions/b2d05e24-2432-4245-a916-4e22a142ad31

import Theorems.Thm_Grunbaum2003_simplicial_three_polytope_edge_in_two_facets
import Theorems.Thm_Grunbaum2003_simplicial_three_polytope_vertex_two_crossings
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false
open Classical
open Grunbaum2003

theorem solution
    (P : Set (Fin 3 → ℝ)) (hP : IsSimplicialDPolytope P)
    (V : Finset (Fin 3 → ℝ)) (ℰ ℱ : Finset (Set (Fin 3 → ℝ)))
    (hV : (V : Set (Fin 3 → ℝ)) = {x : Fin 3 → ℝ | IsExposed ℝ P {x}})
    (hℰ : (ℰ : Set (Set (Fin 3 → ℝ))) =
      {E : Set (Fin 3 → ℝ) | E.Nonempty ∧ IsExposed ℝ P E ∧
        Module.finrank ℝ (affineSpan ℝ E).direction = 1})
    (hℱ : (ℱ : Set (Set (Fin 3 → ℝ))) =
      {F : Set (Fin 3 → ℝ) | F.Nonempty ∧ IsExposed ℝ P F ∧
        Module.finrank ℝ (affineSpan ℝ F).direction = 2}) :
    (∀ E ∈ ℰ, (ℱ.filter (fun F => E ⊆ F)).card = 2) ∧
    (∀ (l : StrongDual ℝ (Fin 3 → ℝ)),
      (∀ x ∈ V, ∀ y ∈ V, l x = l y → x = y) →
      ∀ x ∈ V,
        (∃ E_down ∈ ℰ, x ∈ E_down ∧ ∃ u ∈ V, u ∈ E_down ∧ l u < l x) →
        (∃ E_up ∈ ℰ, x ∈ E_up ∧ ∃ u ∈ V, u ∈ E_up ∧ l x < l u) →
        (ℱ.filter (fun F =>
          ((ℰ.filter (fun E => x ∈ E ∧ ∀ w ∈ V, w ∈ E → l w ≤ l x)).filter
            (fun E => E ⊆ F)).card = 1)).card = 2) := by
  have hTwoFacets :=
    Grunbaum2003.simplicial_three_polytope_edge_in_two_facets P hP V ℰ ℱ hV hℰ hℱ
  exact ⟨hTwoFacets,
    Grunbaum2003.simplicial_three_polytope_vertex_two_crossings P hP V ℰ ℱ hV hℰ hℱ hTwoFacets⟩
