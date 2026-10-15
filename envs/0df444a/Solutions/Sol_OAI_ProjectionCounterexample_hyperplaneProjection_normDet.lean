-- Prove2me | solution 1 for OAI.ProjectionCounterexample.hyperplaneProjection_normDet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:26:39.36999+00:00
-- url     : https://prove2.me/submissions/7da747db-ae13-4f60-b1fe-c573230cd0c7

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/HyperplaneJacobian.lean:L49-L100
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.hyperplaneProjection_normDet. The node keeps its source
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

-- ---- from OAI.Geometry.ProjectionBody.HyperplaneJacobian ----
namespace OAI

open scoped RealInnerProductSpace

namespace ProjectionCounterexample

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

omit [FiniteDimensional ℝ V] in
theorem perpendicularTo_projection_apply {u : V} (hu : ‖u‖ = 1) (x : V) :
    (perpendicularTo u).starProjection x = x - ⟪u, x⟫ • u := by
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ hu]

omit [FiniteDimensional ℝ V] in
theorem inner_perpendicularTo_projection {u : V} (hu : ‖u‖ = 1) (x y : V) :
    ⟪(perpendicularTo u).starProjection x, (perpendicularTo u).starProjection y⟫ =
      ⟪x, y⟫ - ⟪u, x⟫ * ⟪u, y⟫ := by
  rw [perpendicularTo_projection_apply hu, perpendicularTo_projection_apply hu]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]
  rw [real_inner_comm x u]
  ring

/-- The projected facet's area factor is the absolute inner product of unit normals. -/
theorem hyperplaneProjection_normDet {n u : V} (hn : ‖n‖ = 1) (hu : ‖u‖ = 1) :
    (hyperplaneProjection n u).normDet = |⟪n, u⟫| := by
  classical
  let b := stdOrthonormalBasis ℝ (perpendicularTo n)
  let a : Fin (Module.finrank ℝ (perpendicularTo n)) → ℝ :=
    fun i => ⟪u, (b i : V)⟫
  let f := hyperplaneProjection n u
  have hGram : Matrix.gram ℝ (fun i => f (b i)) =
      1 + Matrix.replicateCol Unit (-a) * Matrix.replicateRow Unit a := by
    ext i j
    rw [Matrix.gram_apply]
    change ⟪(perpendicularTo u).starProjection (b i : V),
      (perpendicularTo u).starProjection (b j : V)⟫ = _
    rw [inner_perpendicularTo_projection hu]
    have hbij : ⟪(b i : V), (b j : V)⟫ = if i = j then 1 else 0 :=
      b.inner_eq_ite i j
    rw [hbij]
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, a, sub_eq_add_neg]
  have hparseval : ∑ i, (a i) ^ 2 =
      ‖(perpendicularTo n).orthogonalProjectionOnto u‖ ^ 2 := by
    calc
      ∑ i, (a i) ^ 2 =
          ∑ i, ⟪b i, (perpendicularTo n).orthogonalProjectionOnto u⟫ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
        exact real_inner_comm _ _
      _ = ‖(perpendicularTo n).orthogonalProjectionOnto u‖ ^ 2 :=
        b.sum_sq_inner_right _
  have hnormal : ‖(ℝ ∙ n).starProjection u‖ ^ 2 = ⟪n, u⟫ ^ 2 := by
    rw [Submodule.starProjection_unit_singleton ℝ hn]
    simp [norm_smul, hn, Real.norm_eq_abs, sq_abs]
  have hsum : ∑ i, (a i) ^ 2 = 1 - ⟪n, u⟫ ^ 2 := by
    have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection u (ℝ ∙ n)
    rw [hu, one_pow, hnormal] at hp
    change 1 = ⟪n, u⟫ ^ 2 + ‖(perpendicularTo n).orthogonalProjectionOnto u‖ ^ 2 at hp
    rw [← hparseval] at hp
    linarith
  have hsquare : f.normDet ^ 2 = ⟪n, u⟫ ^ 2 := by
    calc
      f.normDet ^ 2 = (Matrix.gram ℝ (fun i => f (b i))).det :=
        f.normDet_sq_eq_det_gram b
      _ = 1 + a ⬝ᵥ (-a) := by
        rw [hGram, Matrix.det_one_add_replicateCol_mul_replicateRow]
      _ = 1 - ∑ i, (a i) ^ 2 := by
        simp [dotProduct, pow_two, Finset.sum_neg_distrib, sub_eq_add_neg]
      _ = ⟪n, u⟫ ^ 2 := by rw [hsum]; ring
  apply (sq_eq_sq₀ f.normDet_nonneg (abs_nonneg _)).mp
  simpa using hsquare

end

end ProjectionCounterexample

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem solution {n u : V} (hn : ‖n‖ = 1) (hu : ‖u‖ = 1) :
    (hyperplaneProjection n u).normDet = |⟪n, u⟫| := by
  first
    | exact OAI.ProjectionCounterexample.hyperplaneProjection_normDet hn hu
    | exact OAI.ProjectionCounterexample.hyperplaneProjection_normDet
    | (apply OAI.ProjectionCounterexample.hyperplaneProjection_normDet <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.hyperplaneProjection_normDet <;> assumption)
