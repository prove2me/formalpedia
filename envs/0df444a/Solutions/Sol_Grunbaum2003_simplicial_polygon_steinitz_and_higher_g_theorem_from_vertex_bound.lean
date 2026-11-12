-- Prove2me | solution 1 for Grunbaum2003.simplicial_polygon_steinitz_and_higher_g_theorem_from_vertex_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T02:16:12.290178+00:00
-- url     : https://prove2.me/submissions/87987996-837e-4c69-a867-470311a228aa

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_exposed_edge_pair_and_simplex_faceCount_choose
import Theorems.Thm_Grunbaum2003_simplicial_polygon_steinitz_and_higher_g_theorem_from_simplex_and_edges
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem simplicial_polygon_steinitz_and_higher_g_theorem_from_vertex_bound_sol
    (hVertexBound : ∀ (d : ℕ) (P : Set (Fin d → ℝ)),
      faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
      (IsDPolytope P → d + 1 ≤ faceCount P 0)) :
    (∀ f : Fin (2 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 2 → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin 2, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3)) ∧
    (∀ f : Fin (3 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 3 → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin 3, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4)) ∧
    (∀ (d : ℕ), 4 ≤ d → ∀ (f : Fin (d + 1) → ℤ), f 0 = 1 →
      ((∃ P : Set (Fin d → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ k : Fin (d + 1),
          f k = ∑ j ∈ Finset.range (d / 2 + 1),
            (g j : ℤ) * gTheoremMatrix d j k.val)) := by
  obtain ⟨hEdgePair, hSimplicialTwo, hSimplex, hExistsSimplex⟩ :=
    exposed_edge_pair_and_simplex_faceCount_choose
  obtain ⟨h2, h3, h4⟩ :=
    simplicial_polygon_steinitz_and_higher_g_theorem_from_simplex_and_edges
      hVertexBound (fun hHull F hF => hEdgePair hHull F hF) ⟨hSimplex, hExistsSimplex⟩
  refine ⟨?_, h3, h4⟩
  intro f hf0
  rw [← h2 f hf0]
  constructor
  · rintro ⟨P, hPSimp, hPf⟩
    exact ⟨P, (hSimplicialTwo P).mp hPSimp, hPf⟩
  · rintro ⟨P, hPPoly, hPf⟩
    exact ⟨P, (hSimplicialTwo P).mpr hPPoly, hPf⟩

end Grunbaum2003

open Grunbaum2003 in
theorem solution
    (hVertexBound : ∀ (d : ℕ) (P : Set (Fin d → ℝ)),
      faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
      (IsDPolytope P → d + 1 ≤ faceCount P 0)) :
    (∀ f : Fin (2 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 2 → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin 2, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 3 ∧ f 2 = (n : ℤ) + 3)) ∧
    (∀ f : Fin (3 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 3 → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin 3, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ n : ℕ, f 1 = (n : ℤ) + 4 ∧ f 2 = (n : ℤ) * 3 + 6 ∧ f 3 = (n : ℤ) * 2 + 4)) ∧
    (∀ (d : ℕ), 4 ≤ d → ∀ (f : Fin (d + 1) → ℤ), f 0 = 1 →
      ((∃ P : Set (Fin d → ℝ),
        IsSimplicialDPolytope P ∧
        ∀ j : Fin d, f j.succ = (faceCount P j.val : ℤ)) ↔
       ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        ∀ k : Fin (d + 1),
          f k = ∑ j ∈ Finset.range (d / 2 + 1),
            (g j : ℤ) * gTheoremMatrix d j k.val)) :=
  Grunbaum2003.simplicial_polygon_steinitz_and_higher_g_theorem_from_vertex_bound_sol hVertexBound
