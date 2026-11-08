-- Prove2me | solution 1 for Grunbaum2003.simplicial_polygon_steinitz_and_higher_g_theorem_from_simplex_and_edges
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-08T02:35:27.477203+00:00
-- url     : https://prove2.me/submissions/5a815ba6-8220-4845-be13-27de6259cee2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Grunbaum2003_IsDPolytope
import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_gTheoremMatrix_columns_mSequence_and_simplex_realization
import Theorems.Thm_Grunbaum2003_simplicial_polygon_steinitz_and_higher_g_theorem_from_mSequence_bridge
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

theorem simplicial_polygon_steinitz_and_higher_g_theorem_from_simplex_and_edges_sol
    (hVertexBound : ∀ (d : ℕ) (P : Set (Fin d → ℝ)),
      faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
      (IsDPolytope P → d + 1 ≤ faceCount P 0))
    (hEdgePair : ∀ {d : ℕ} {P : Set (Fin d → ℝ)},
      ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
        ∀ E : PolytopeFace P,
          E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
      ∀ (F : Set (Fin d → ℝ)), IsExposed ℝ P F →
        ((F.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 1) ↔
          ∃ a b : Fin d → ℝ,
            IsExposed ℝ P {a} ∧ IsExposed ℝ P {b} ∧ a ≠ b ∧
            F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = {a, b} ∧
            F = convexHull ℝ ({a, b} : Set (Fin d → ℝ))))
    (hSimplex :
      (∀ (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ),
        AffineIndependent ℝ v →
        IsSimplicialDPolytope (convexHull ℝ (Set.range v)) ∧
        ∀ k : ℕ, faceCount (convexHull ℝ (Set.range v)) k = Nat.choose (d + 1) (k + 1)) ∧
      (∀ d : ℕ,
        ∃ P : Set (Fin d → ℝ),
          IsSimplicialDPolytope P ∧
          ∀ k : ℕ, faceCount P k = Nat.choose (d + 1) (k + 1))) :
    (∀ f : Fin (2 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 2 → ℝ),
        IsDPolytope P ∧
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
  obtain ⟨hRow0, hCol0, hCol1, hOneStep, hM1, hSimpM, _, _⟩ :=
    gTheoremMatrix_columns_mSequence_and_simplex_realization
  exact simplicial_polygon_steinitz_and_higher_g_theorem_from_mSequence_bridge
    hVertexBound (fun hHull F hF => hEdgePair hHull F hF) hSimplex
    ⟨hRow0, hCol0, hCol1, hOneStep, hM1, hSimpM⟩

end Grunbaum2003

open Grunbaum2003 in
theorem solution
    (hVertexBound : ∀ (d : ℕ) (P : Set (Fin d → ℝ)),
      faceCount P 0 = {x : Fin d → ℝ | IsExposed ℝ P {x}}.ncard ∧
      (IsDPolytope P → d + 1 ≤ faceCount P 0))
    (hEdgePair : ∀ {d : ℕ} {P : Set (Fin d → ℝ)},
      ({x : Fin d → ℝ | IsExposed ℝ P {x}}.Finite ∧
        ∀ E : PolytopeFace P,
          E.val = convexHull ℝ (E.val ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}})) →
      ∀ (F : Set (Fin d → ℝ)), IsExposed ℝ P F →
        ((F.Nonempty ∧ Module.finrank ℝ (affineSpan ℝ F).direction = 1) ↔
          ∃ a b : Fin d → ℝ,
            IsExposed ℝ P {a} ∧ IsExposed ℝ P {b} ∧ a ≠ b ∧
            F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = {a, b} ∧
            F = convexHull ℝ ({a, b} : Set (Fin d → ℝ))))
    (hSimplex :
      (∀ (d : ℕ) (v : Fin (d + 1) → Fin d → ℝ),
        AffineIndependent ℝ v →
        IsSimplicialDPolytope (convexHull ℝ (Set.range v)) ∧
        ∀ k : ℕ, faceCount (convexHull ℝ (Set.range v)) k = Nat.choose (d + 1) (k + 1)) ∧
      (∀ d : ℕ,
        ∃ P : Set (Fin d → ℝ),
          IsSimplicialDPolytope P ∧
          ∀ k : ℕ, faceCount P k = Nat.choose (d + 1) (k + 1))) :
    (∀ f : Fin (2 + 1) → ℤ, f 0 = 1 →
      ((∃ P : Set (Fin 2 → ℝ),
        IsDPolytope P ∧
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
  Grunbaum2003.simplicial_polygon_steinitz_and_higher_g_theorem_from_simplex_and_edges_sol
    hVertexBound hEdgePair hSimplex
