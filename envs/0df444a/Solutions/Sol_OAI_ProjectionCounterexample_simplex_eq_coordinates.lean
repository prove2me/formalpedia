-- Prove2me | solution 1 for OAI.ProjectionCounterexample.simplex_eq_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:02:47.062593+00:00
-- url     : https://prove2.me/submissions/571a5bf6-5f75-4aae-ac81-9a885ae43a2d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ConvexGeometry.lean:L34-L79
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.simplex_eq_coordinates. The node keeps its source
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

-- ---- from OAI.Geometry.ProjectionBody.ConvexGeometry ----
namespace OAI

open Set

namespace ProjectionCounterexample

noncomputable section

theorem simplex_eq_coordinates (d : ℕ) :
    simplex d = {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
  classical
  apply Subset.antisymm
  · apply convexHull_min
    · rintro x (rfl | ⟨i, rfl⟩)
      · simp
      · constructor
        · intro j
          simp only [PiLp.single_apply]
          split_ifs
          · exact zero_le_one
          · exact le_rfl
        · simp [PiLp.single_apply]
    · intro x hx y hy a b ha hb hab
      constructor
      · intro i
        exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
      · change ∑ i, (a * x i + b * y i) ≤ 1
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        calc
          a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
              (mul_le_mul_of_nonneg_left hy.2 hb)
          _ = 1 := by simpa using hab
  · intro x hx
    let w : Option (Fin d) → ℝ := fun o =>
      match o with
      | none => 1 - ∑ i, x i
      | some i => x i
    let z : Option (Fin d) → E d := fun o =>
      match o with
      | none => 0
      | some i => EuclideanSpace.single i 1
    apply mem_convexHull_of_exists_fintype w z
    · intro o
      cases o with
      | none => exact sub_nonneg.mpr hx.2
      | some i => exact hx.1 i
    · simp [w, Fintype.sum_option]
    · intro o
      cases o with
      | none => exact mem_insert 0 _
      | some i => exact mem_insert_of_mem 0 (mem_range_self i)
    · simpa [w, z, Fintype.sum_option, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr x

end

end ProjectionCounterexample

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set

theorem solution (d : ℕ) :
    simplex d = {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} := by
  first
    | exact OAI.ProjectionCounterexample.simplex_eq_coordinates d
    | exact OAI.ProjectionCounterexample.simplex_eq_coordinates
    | (apply OAI.ProjectionCounterexample.simplex_eq_coordinates <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.simplex_eq_coordinates <;> assumption)
