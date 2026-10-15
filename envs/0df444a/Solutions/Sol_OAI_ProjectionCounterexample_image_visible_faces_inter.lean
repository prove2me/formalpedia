-- Prove2me | solution 1 for OAI.ProjectionCounterexample.image_visible_faces_inter
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:05:15.92291+00:00
-- url     : https://prove2.me/submissions/be7aae93-fde9-4066-8576-0067d61d14a1

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/FacetCover.lean:L95-L113
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.image_visible_faces_inter. The node keeps its source
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
import Theorems.Thm_OAI_ProjectionCounterexample_visible_face_line_unique

-- ---- from OAI.Geometry.ProjectionBody.FacetCover ----
namespace OAI

/-! Finite-halfspace geometry underlying the visible-facet projection formula. -/

noncomputable section
open Set

namespace ProjectionCounterexample

variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

omit [Fintype ι] in
/-- Overlaps of visible-face shadows are precisely shadows of the face intersections. -/
theorem image_visible_faces_inter
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W)
    {u : V} (hker : LinearMap.ker q = Submodule.span ℝ {u})
    {i j : ι} (hi : 0 < a i u) (hj : 0 < a j u) :
    (q '' boundingFace a b i) ∩ (q '' boundingFace a b j) =
      q '' (boundingFace a b i ∩ boundingFace a b j) := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨y, hy, hyq⟩, ⟨z, hz, hzq⟩⟩
    have hdiff : z - y ∈ Submodule.span ℝ {u} := by
      rw [← hker, LinearMap.mem_ker, map_sub, hyq, hzq, sub_self]
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hdiff
    have hline : z = y + t • u := by
      rw [ht]
      simp [sub_eq_add_neg]
    have hzy := visible_face_line_unique a b hy hz hi hj hline
    exact ⟨y, ⟨hy, hzy ▸ hz⟩, hyq⟩
  · exact Set.image_inter_subset q _ _

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
    (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (q : V →ₗ[ℝ] W)
    {u : V} (hker : LinearMap.ker q = Submodule.span ℝ {u})
    {i j : ι} (hi : 0 < a i u) (hj : 0 < a j u) :
    (q '' boundingFace a b i) ∩ (q '' boundingFace a b j) =
      q '' (boundingFace a b i ∩ boundingFace a b j) := by
  first
    | exact OAI.ProjectionCounterexample.image_visible_faces_inter a b q hker hi hj
    | exact OAI.ProjectionCounterexample.image_visible_faces_inter
    | (apply OAI.ProjectionCounterexample.image_visible_faces_inter <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.image_visible_faces_inter <;> assumption)
