-- Prove2me | solution 1 for OAI.ProjectionCounterexample.simplex_facet_transverse
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:08:36.176358+00:00
-- url     : https://prove2.me/submissions/a0bec48e-ba2b-41d0-9bd0-74403c52dc0b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/SimplexFacetCharts.lean:L47-L75
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.simplex_facet_transverse. The node keeps its source
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
import Definitions.Def_OAI_Geometry_ProjectionBody_GraphChart
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacetCharts

-- ---- from OAI.Geometry.ProjectionBody.FacetCoordinates ----
namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

theorem sum_insertZero {n : ℕ} (i : Fin (n + 1)) (x : E n) :
    ∑ j, insertZero i x j = ∑ j, x j := by
  rw [Fin.sum_univ_succAbove _ i]
  simp

end ProjectionCounterexample

end

end OAI

-- ---- from OAI.Geometry.ProjectionBody.SimplexFacetCharts ----
namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- Every defining hyperplane other than the chart's own hyperplane is transverse.
The positive dimension excludes the degenerate segment-endpoint case. -/
theorem simplex_facet_transverse {n : ℕ} (hn : 0 < n)
    (i j : Option (Fin (n + 1))) (hij : i ≠ j) :
    (simplexFunctional (n + 1) j).comp (simplexFacetLinear n i) ≠ 0 := by
  intro heq
  let k : Fin n := ⟨0, hn⟩
  cases i with
  | none =>
    cases j with
    | none => exact hij rfl
    | some j =>
      induction j using Fin.lastCases with
      | last =>
        have h := LinearMap.congr_fun heq (EuclideanSpace.single k 1)
        simp [simplexFacetLinear, graphLinear] at h
      | cast j =>
        have h := LinearMap.congr_fun heq (EuclideanSpace.single j 1)
        simp [simplexFacetLinear, graphLinear, insertZero, Fin.insertNth_last'] at h
  | some i =>
    cases j with
    | none =>
      have h := LinearMap.congr_fun heq (EuclideanSpace.single k 1)
      simp [simplexFacetLinear, sum_insertZero] at h
    | some j =>
      have hji : j ≠ i := fun h => hij (congrArg some h.symm)
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hji
      have h := LinearMap.congr_fun heq (EuclideanSpace.single k 1)
      simp [simplexFacetLinear] at h

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set
open scoped RealInnerProductSpace

theorem solution {n : ℕ} (hn : 0 < n)
    (i j : Option (Fin (n + 1))) (hij : i ≠ j) :
    (simplexFunctional (n + 1) j).comp (simplexFacetLinear n i) ≠ 0 := by
  first
    | exact OAI.ProjectionCounterexample.simplex_facet_transverse hn i j hij
    | exact OAI.ProjectionCounterexample.simplex_facet_transverse
    | (apply OAI.ProjectionCounterexample.simplex_facet_transverse <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.simplex_facet_transverse <;> assumption)
