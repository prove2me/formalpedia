-- Prove2me | solution 1 for OAI.ProjectionCounterexample.coordinate_facet_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:07:20.482179+00:00
-- url     : https://prove2.me/submissions/5c42cc37-8a6f-4c58-ba11-0cb673312b8e

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/FacetCoordinates.lean:L37-L59
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.coordinate_facet_eq_image. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Definitions.Def_ProjectionCounterexample
import Definitions.Def_OAI_Geometry_ProjectionBody_GeometryDefinitions
import Definitions.Def_OAI_Geometry_ProjectionBody_ConvexGeometry
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCover
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCoordinates
import Theorems.Thm_OAI_ProjectionCounterexample_simplex_eq_coordinates

-- ---- from OAI.Geometry.ProjectionBody.FacetCoordinates ----
namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

theorem sum_insertZero {n : ℕ} (i : Fin (n + 1)) (x : E n) :
    ∑ j, insertZero i x j = ∑ j, x j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

/-- A coordinate facet is an actual isometric image of the lower-dimensional simplex. -/
theorem coordinate_facet_eq_image {n : ℕ} (i : Fin (n + 1)) :
    {x ∈ simplex (n + 1) | x i = 0} = insertZero i '' simplex n := by
  simp_rw [simplex_eq_coordinates]
  apply Subset.antisymm
  · rintro x ⟨⟨hx, hs⟩, hxi⟩
    let y : E n := WithLp.toLp 2 (fun j => x (i.succAbove j))
    have hy : (∀ j, 0 ≤ y j) ∧ ∑ j, y j ≤ 1 := by
      refine ⟨fun j => hx _, ?_⟩
      rw [Fin.sum_univ_succAbove _ i, hxi, zero_add] at hs
      exact hs
    refine ⟨y, hy, ?_⟩
    ext j
    induction j using i.succAboveCases
    · simpa using hxi.symm
    · simp [y]
  · rintro x ⟨y, ⟨hy, hs⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, by simp⟩
    · intro j
      induction j using i.succAboveCases
      · simp
      · simpa using hy _
    · simpa [sum_insertZero] using hs

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set

theorem solution {n : ℕ} (i : Fin (n + 1)) :
    {x ∈ simplex (n + 1) | x i = 0} = insertZero i '' simplex n := by
  first
    | exact OAI.ProjectionCounterexample.coordinate_facet_eq_image i
    | exact OAI.ProjectionCounterexample.coordinate_facet_eq_image
    | (apply OAI.ProjectionCounterexample.coordinate_facet_eq_image <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.coordinate_facet_eq_image <;> assumption)
