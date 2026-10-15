-- Prove2me | solution 1 for OAI.ProjectionCounterexample.visible_face_line_unique
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:03:57.794695+00:00
-- url     : https://prove2.me/submissions/40067026-aad4-4803-8428-551cb3a8590d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/FacetCover.lean:L75-L93
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.visible_face_line_unique. The node keeps its source
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

-- ---- from OAI.Geometry.ProjectionBody.FacetCover ----
namespace OAI

/-! Finite-halfspace geometry underlying the visible-facet projection formula. -/

noncomputable section
open Set

namespace ProjectionCounterexample

variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

omit [Fintype ι] in
/-- Two visible boundary points on the same line parallel to the direction coincide.
This will put overlaps of projected visible faces in their common lower-dimensional face. -/
theorem visible_face_line_unique
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {i j : ι} {y z u : V} {t : ℝ}
    (hy : y ∈ boundingFace a b i) (hz : z ∈ boundingFace a b j)
    (hi : 0 < a i u) (hj : 0 < a j u) (hline : z = y + t • u) : z = y := by
  have hti : t * a i u ≤ 0 := by
    have h := hz.1 i
    rw [hline, map_add, map_smul, smul_eq_mul, hy.2] at h
    linarith
  have htj : 0 ≤ t * a j u := by
    have h := hy.1 j
    have he := hz.2
    rw [hline, map_add, map_smul, smul_eq_mul] at he
    linarith
  have ht0 : t = 0 := by nlinarith
  simpa [ht0] using hline

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set
variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

omit [Fintype ι] in
theorem solution
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {i j : ι} {y z u : V} {t : ℝ}
    (hy : y ∈ boundingFace a b i) (hz : z ∈ boundingFace a b j)
    (hi : 0 < a i u) (hj : 0 < a j u) (hline : z = y + t • u) : z = y := by
  first
    | exact OAI.ProjectionCounterexample.visible_face_line_unique a b hy hz hi hj hline
    | exact OAI.ProjectionCounterexample.visible_face_line_unique
    | (apply OAI.ProjectionCounterexample.visible_face_line_unique <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.visible_face_line_unique <;> assumption)
