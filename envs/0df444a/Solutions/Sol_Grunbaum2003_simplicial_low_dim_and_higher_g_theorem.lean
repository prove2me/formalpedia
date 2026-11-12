-- Prove2me | solution 1 for Grunbaum2003.simplicial_low_dim_and_higher_g_theorem
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T01:31:18.677052+00:00
-- url     : https://prove2.me/submissions/79def8f9-7634-462b-811e-e7b82d378cd1

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound
import Theorems.Thm_Grunbaum2003_simplicial_polygon_steinitz_and_higher_g_theorem_from_vertex_bound
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem simplicial_low_dim_and_higher_g_theorem_sol :
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
  simplicial_polygon_steinitz_and_higher_g_theorem_from_vertex_bound
    polytope_faceCount_zero_eq_exposed_vertices_and_lower_bound

end Grunbaum2003

open Grunbaum2003 in
theorem solution :
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
  Grunbaum2003.simplicial_low_dim_and_higher_g_theorem_sol
