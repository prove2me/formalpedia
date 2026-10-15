-- Prove2me | solution 1 for OAI.ProjectionCounterexample.normDet_project_comp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:27:34.874816+00:00
-- url     : https://prove2.me/submissions/55408304-8a11-4315-9f33-9a5e1d61514a

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/HyperplaneJacobian.lean:L102-L124
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.normDet_project_comp. The node keeps its source
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
import Definitions.Def_OAI_Geometry_Zonotope_Decomposition
import Definitions.Def_OAI_Geometry_Zonotope_Support
import Definitions.Def_OAI_Geometry_Zonotope_Euclidean
import Definitions.Def_OAI_Geometry_Zonotope_Product
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetCharts
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetGraphs
import Definitions.Def_OAI_Geometry_ProjectionBody_HyperplaneJacobian
import Theorems.Thm_OAI_ProjectionCounterexample_hyperplaneProjection_normDet

-- ---- from OAI.Geometry.ProjectionBody.HyperplaneJacobian ----
namespace OAI

open scoped RealInnerProductSpace

namespace ProjectionCounterexample

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem perpendicularTo_finrank {n : V} (hn : ‖n‖ = 1) :
    Module.finrank ℝ (perpendicularTo n) = Module.finrank ℝ V - 1 := by
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have h := (ℝ ∙ n).finrank_add_finrank_orthogonal
  have h' := congrArg (fun k : ℕ => k - 1) h
  simpa only [finrank_span_singleton hn0, Nat.add_sub_cancel_left] using h'

/-- The same area factor for any linear chart into the source tangent hyperplane.
The chart may be singular; the norm determinant identity handles that case as well. -/
theorem normDet_project_comp {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] (L : U →ₗ[ℝ] V) {n u : V}
    (hn : ‖n‖ = 1) (hu : ‖u‖ = 1)
    (hmem : ∀ x, ⟪n, L x⟫ = 0)
    (hrank : Module.finrank ℝ U = Module.finrank ℝ V - 1) :
    ((perpendicularTo u).starProjection.toLinearMap.comp L).normDet =
      |⟪n, u⟫| * L.normDet := by
  let L' : U →ₗ[ℝ] perpendicularTo n := L.codRestrict (perpendicularTo n)
    (fun x => Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hmem x))
  have hdim : Module.finrank ℝ U = Module.finrank ℝ (perpendicularTo n) :=
    hrank.trans (perpendicularTo_finrank hn).symm
  have hL : L'.normDet = L.normDet := by
    dsimp only [L']
    exact LinearMap.normDet_codRestrict
      (fun x => Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (hmem x))
  calc
    ((perpendicularTo u).starProjection.toLinearMap.comp L).normDet =
        ((hyperplaneProjection n u).comp L').normDet := rfl
    _ = (hyperplaneProjection n u).normDet * L'.normDet :=
      LinearMap.normDet_comp_of_finrank_eq L' (hyperplaneProjection n u) hdim
    _ = |⟪n, u⟫| * L.normDet := by rw [hyperplaneProjection_normDet hn hu, hL]

end

end ProjectionCounterexample

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem solution {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U] (L : U →ₗ[ℝ] V) {n u : V}
    (hn : ‖n‖ = 1) (hu : ‖u‖ = 1)
    (hmem : ∀ x, ⟪n, L x⟫ = 0)
    (hrank : Module.finrank ℝ U = Module.finrank ℝ V - 1) :
    ((perpendicularTo u).starProjection.toLinearMap.comp L).normDet =
      |⟪n, u⟫| * L.normDet := by
  first
    | exact OAI.ProjectionCounterexample.normDet_project_comp L hn hu hmem hrank
    | exact OAI.ProjectionCounterexample.normDet_project_comp
    | (apply OAI.ProjectionCounterexample.normDet_project_comp <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.normDet_project_comp <;> assumption)
