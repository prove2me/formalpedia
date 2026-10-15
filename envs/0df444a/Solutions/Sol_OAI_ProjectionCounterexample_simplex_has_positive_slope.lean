-- Prove2me | solution 1 for OAI.ProjectionCounterexample.simplex_has_positive_slope
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:06:42.510289+00:00
-- url     : https://prove2.me/submissions/334a8225-8e1d-416a-acef-d2030b85a98e

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/SimplexFacets.lean:L54-L71
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.simplex_has_positive_slope. The node keeps its source
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

-- ---- from OAI.Geometry.ProjectionBody.SimplexFacets ----
namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

/-- Every nonzero direction has a visible defining facet of the simplex. -/
theorem simplex_has_positive_slope {d : ℕ} {u : E d} (hu : u ≠ 0) :
    ∃ i, 0 < simplexFunctional d i u := by
  by_contra h
  have hall (i : Option (Fin d)) : simplexFunctional d i u ≤ 0 :=
    le_of_not_gt (fun hi => h ⟨i, hi⟩)
  have hcoords (i : Fin d) : 0 ≤ u i := by
    have := hall (some i)
    simpa using this
  have hsum : ∑ i, u i = 0 := by
    apply le_antisymm
    · simpa using hall none
    · exact Finset.sum_nonneg fun i _ => hcoords i
  have hzero : ∀ i : Fin d, u i = 0 := by
    simpa using (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hcoords i)).mp hsum
  apply hu
  ext i
  exact hzero i

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set

theorem solution {d : ℕ} {u : E d} (hu : u ≠ 0) :
    ∃ i, 0 < simplexFunctional d i u := by
  first
    | exact OAI.ProjectionCounterexample.simplex_has_positive_slope hu
    | exact OAI.ProjectionCounterexample.simplex_has_positive_slope
    | (apply OAI.ProjectionCounterexample.simplex_has_positive_slope <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.simplex_has_positive_slope <;> assumption)
