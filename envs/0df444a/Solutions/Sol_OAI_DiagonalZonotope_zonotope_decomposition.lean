-- Prove2me | solution 1 for OAI.DiagonalZonotope.zonotope_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:09:13.760451+00:00
-- url     : https://prove2.me/submissions/dabf9055-8cec-45e3-9f3f-5082758f712e

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Decomposition.lean:L52-L85
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalZonotope.zonotope_decomposition. The node keeps its source
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

-- ---- from OAI.Geometry.Zonotope.Decomposition ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
The unit cube extruded by the segment from zero to the all-ones vector.
Its decomposition uses the cube and one extrusion cell for every upper facet.
The set definitions are literal subsets of a finite real coordinate space.
-/

noncomputable section
open Set

namespace DiagonalZonotope

variable {ι : Type*}

lemma cube_subset_zonotope : (cube : Set (ι → ℝ)) ⊆ zonotope := by
  intro x hx
  refine ⟨x, hx, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
  funext j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, zero_mul, add_zero]

lemma cell_subset_zonotope (i : ι) : cell i ⊆ zonotope := by
  intro x hx
  rcases hx with ⟨hlo, hhi, hcoord⟩
  refine ⟨fun j => x j - (x i - 1), ?_, x i - 1, ?_, ?_⟩
  · intro j
    constructor <;> linarith [(hcoord j).1, (hcoord j).2]
  · constructor <;> linarith
  · funext j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact (sub_add_cancel _ _).symm

/-- Decompose the actual diagonal extrusion by a maximal coordinate. -/
theorem zonotope_decomposition [Fintype ι] :
    (zonotope : Set (ι → ℝ)) = cube ∪ ⋃ i, cell i := by
  classical
  apply Subset.antisymm
  · intro x hx
    by_cases hc : x ∈ cube
    · exact Or.inl hc
    · rcases hx with ⟨q, hq, t, ht, hxt⟩
      have heq (j : ι) : x j = q j + t := by
        simpa using congrFun hxt j
      have hnonneg (j : ι) : 0 ≤ x j := by
        rw [heq j]
        exact add_nonneg (hq j).1 ht.1
      have hlarge : ∃ k, 1 < x k := by
        by_contra h
        push Not at h
        exact hc (fun j => ⟨hnonneg j, h j⟩)
      obtain ⟨k, hk⟩ := hlarge
      obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ x
        ⟨k, Finset.mem_univ k⟩
      have hmax' (j : ι) : x j ≤ x i := hmax j (Finset.mem_univ j)
      right
      apply mem_iUnion.mpr
      refine ⟨i, ?_⟩
      refine ⟨by linarith [hmax' k], ?_, ?_⟩
      · linarith [heq i, (hq i).2, ht.2]
      · intro j
        exact ⟨by linarith [heq i, heq j, (hq i).2, (hq j).1], hmax' j⟩
  · intro x hx
    rcases hx with hc | hc
    · exact cube_subset_zonotope hc
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hc
      exact cell_subset_zonotope i hi

section AffineCell
variable [DecidableEq ι]

end AffineCell
end DiagonalZonotope

end

end OAI

-- ---- platform node ----
open OAI OAI.DiagonalZonotope
open Set
variable {ι : Type*}

theorem solution [Fintype ι] :
    (zonotope : Set (ι → ℝ)) = cube ∪ ⋃ i, cell i := by
  first
    | exact OAI.DiagonalZonotope.zonotope_decomposition
    | (apply OAI.DiagonalZonotope.zonotope_decomposition <;> assumption)
    | (intros; apply OAI.DiagonalZonotope.zonotope_decomposition <;> assumption)
