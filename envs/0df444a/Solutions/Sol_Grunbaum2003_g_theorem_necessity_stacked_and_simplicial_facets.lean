-- Prove2me | solution 1 for Grunbaum2003.g_theorem_necessity_stacked_and_simplicial_facets
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-09T02:01:04.993866+00:00
-- url     : https://prove2.me/submissions/03afb01d-dc19-46ed-bcfe-d67cd71ebadf

import Definitions.Def_Grunbaum2003_IsSimplicialDPolytope
import Definitions.Def_Grunbaum2003_PolytopeFace
import Definitions.Def_Grunbaum2003_faceCount
import Definitions.Def_Grunbaum2003_IsMSequence
import Definitions.Def_Grunbaum2003_gTheoremMatrix
import Theorems.Thm_Grunbaum2003_polytope_face_eq_convexHull_exposed_vertices
import Theorems.Thm_Grunbaum2003_simplicial_facet_exposed_vertices_and_cardinality
import Theorems.Thm_Grunbaum2003_simplicial_facet_subfaces_and_bipartite_double_counting
import Theorems.Thm_Grunbaum2003_gTheoremMatrix_columns_mSequence_and_simplex_realization
import Theorems.Thm_Grunbaum2003_gTheoremMatrix_row_one_top_columns_and_g2_zero_sum
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Hull
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
open scoped BigOperators

open Grunbaum2003

theorem solution :
    (∀ {d : ℕ} {P : Set (Fin d → ℝ)},
      IsSimplicialDPolytope P →
      ∀ (F : Set (Fin d → ℝ)), F.Nonempty → IsExposed ℝ P F →
        Module.finrank ℝ (affineSpan ℝ F).direction + 1 = d →
        ∃ v : Fin d → Fin d → ℝ,
          AffineIndependent ℝ v ∧
          Function.Injective v ∧
          (∀ i : Fin d, IsExposed ℝ P {v i}) ∧
          F = convexHull ℝ (Set.range v) ∧
          F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} = Set.range v ∧
          (F ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}}).ncard = d ∧
          (∀ s : Finset (Fin d),
            convexHull ℝ (v '' (s : Set (Fin d))) ∩ {x : Fin d → ℝ | IsExposed ℝ P {x}} =
              v '' (s : Set (Fin d))) ∧
          (∀ s₁ s₂ : Finset (Fin d),
            convexHull ℝ (v '' (s₁ : Set (Fin d))) = convexHull ℝ (v '' (s₂ : Set (Fin d))) ↔
              s₁ = s₂)) ∧
    (∀ (d : ℕ), 4 ≤ d → ∀ (P : Set (Fin d → ℝ)),
      IsSimplicialDPolytope P →
      d + 1 < faceCount P 0 →
      (∀ j : Fin d, (faceCount P j.val : ℤ) =
        (Nat.choose (d + 1) j.succ.val : ℤ) +
          ((faceCount P 0 - (d + 1) : ℕ) : ℤ) * gTheoremMatrix d 1 j.succ.val) →
      ∃ g : ℕ → ℕ, IsMSequence (d / 2) g ∧
        g 1 = faceCount P 0 - (d + 1) ∧
        g 2 = 0 ∧
        ∀ j : Fin d, (faceCount P j.val : ℤ) =
          ∑ i ∈ Finset.range (d / 2 + 1), (g i : ℤ) * gTheoremMatrix d i j.succ.val) := by
  refine ⟨?_, ?_⟩
  · intro d P hP F hF_ne hF_exp hF_dim
    have hHull := Grunbaum2003.polytope_face_eq_convexHull_exposed_vertices d P hP.1
    obtain ⟨v, hAff, hInj, hExp, hF_eq, hF_inter, hF_ncard⟩ :=
      Grunbaum2003.simplicial_facet_exposed_vertices_and_cardinality hP hHull F hF_ne hF_exp hF_dim
    have hSub := Grunbaum2003.simplicial_facet_subfaces_and_bipartite_double_counting.1 v hInj hExp
    exact ⟨v, hAff, hInj, hExp, hF_eq, hF_inter, hF_ncard, hSub.1, hSub.2⟩
  · intro d hd P _hP _hV_gt hStacked
    let n : ℕ := faceCount P 0 - (d + 1)
    let g : ℕ → ℕ := fun j => if j = 0 then 1 else if j = 1 then n else 0
    have hBridge := Grunbaum2003.gTheoremMatrix_columns_mSequence_and_simplex_realization
    have hg_mseq : IsMSequence (d / 2) g := hBridge.2.2.2.1 (d / 2) n
    have hg1 : g 1 = n := rfl
    have hg2 : g 2 = 0 := rfl
    have hSum := Grunbaum2003.gTheoremMatrix_row_one_top_columns_and_g2_zero_sum.2.2.2.2.1
      (by omega : 2 ≤ d) hg_mseq hg2
    refine ⟨g, hg_mseq, hg1, hg2, fun j => ?_⟩
    rw [hStacked j, hSum j, hg1]
