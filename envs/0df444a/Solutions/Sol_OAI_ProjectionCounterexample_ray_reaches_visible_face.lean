-- Prove2me | solution 1 for OAI.ProjectionCounterexample.ray_reaches_visible_face
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:03:19.667583+00:00
-- url     : https://prove2.me/submissions/17ffebb5-80f8-4128-a81a-de69fbef994d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/FacetCover.lean:L28-L56
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionCounterexample.ray_reaches_visible_face. The node keeps its source
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

/-- Moving in a direction with a positive halfspace slope reaches a visible face. -/
theorem ray_reaches_visible_face (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {y u : V} (hy : y ∈ halfspaceBody a b) (hu : ∃ i, 0 < a i u) :
    ∃ (t : ℝ) (i : ι), 0 ≤ t ∧ 0 < a i u ∧
      y + t • u ∈ boundingFace a b i := by
  classical
  let s := Finset.univ.filter fun i => 0 < a i u
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := hu
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨i, hi, hmin⟩ :=
    s.exists_min_image (fun j => (b j - a j y) / a j u) hs
  have hiu : 0 < a i u := (Finset.mem_filter.mp hi).2
  let t := (b i - a i y) / a i u
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr (hy i)) hiu.le
  refine ⟨t, i, ht, hiu, ?_, ?_⟩
  · intro j
    rw [map_add, map_smul, smul_eq_mul]
    by_cases hju : 0 < a j u
    · have hle : t ≤ (b j - a j y) / a j u :=
        hmin j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hju⟩)
      have := (le_div_iff₀ hju).mp hle
      linarith
    · have hm : t * a j u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (le_of_not_gt hju)
      have := hy j
      linarith
  · rw [map_add, map_smul, smul_eq_mul]
    have hm : t * a i u = b i - a i y := div_mul_cancel₀ _ (ne_of_gt hiu)
    linarith

end ProjectionCounterexample

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionCounterexample
open Set
variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

theorem solution (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ)
    {y u : V} (hy : y ∈ halfspaceBody a b) (hu : ∃ i, 0 < a i u) :
    ∃ (t : ℝ) (i : ι), 0 ≤ t ∧ 0 < a i u ∧
      y + t • u ∈ boundingFace a b i := by
  first
    | exact OAI.ProjectionCounterexample.ray_reaches_visible_face a b hy hu
    | exact OAI.ProjectionCounterexample.ray_reaches_visible_face
    | (apply OAI.ProjectionCounterexample.ray_reaches_visible_face <;> assumption)
    | (intros; apply OAI.ProjectionCounterexample.ray_reaches_visible_face <;> assumption)
