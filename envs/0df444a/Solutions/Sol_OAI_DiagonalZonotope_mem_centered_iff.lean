-- Prove2me | solution 1 for OAI.DiagonalZonotope.mem_centered_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:09:51.483641+00:00
-- url     : https://prove2.me/submissions/d882add2-5fcd-4d39-8c9b-e4101ca6377f

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Support.lean:L17-L51
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalZonotope.mem_centered_iff. The node keeps its source
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

-- ---- from OAI.Geometry.Zonotope.Support ----
namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι]

/-- Coordinate and coordinate-difference inequalities describe the centered body exactly. -/
theorem mem_centered_iff (x : ι → ℝ) :
    x ∈ centered ↔ (∀ i, |x i| ≤ 1) ∧ ∀ i j, |x i - x j| ≤ 1 := by
  classical
  constructor
  · rintro ⟨q, hq, t, ht, hx⟩
    have heq (j : ι) : x j + 1 = q j + t := by simpa using congrFun hx j
    constructor
    · intro i
      apply abs_le.mpr
      constructor <;> linarith [heq i, (hq i).1, (hq i).2, ht.1, ht.2]
    · intro i j
      apply abs_le.mpr
      constructor <;> linarith [heq i, heq j, (hq i).1, (hq i).2, (hq j).1, (hq j).2]
  · rintro ⟨hab, hdiff⟩
    by_cases hn : ∀ j, x j ≤ 0
    · refine ⟨fun j => x j + 1, ?_, 0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      · intro j
        constructor <;> linarith [(abs_le.mp (hab j)).1, hn j]
      · funext j
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, zero_mul, add_zero]
    · have hp : ∃ k, 0 < x k := by simpa only [not_forall, not_le] using hn
      obtain ⟨k, hk⟩ := hp
      obtain ⟨i, _, hmax⟩ := Finset.exists_max_image Finset.univ x
        ⟨k, Finset.mem_univ k⟩
      have hm (j : ι) : x j ≤ x i := hmax j (Finset.mem_univ j)
      refine ⟨fun j => x j + 1 - x i, ?_, x i, ?_, ?_⟩
      · intro j
        constructor
        · linarith [(abs_le.mp (hdiff j i)).1]
        · linarith [hm j]
      · exact ⟨le_of_lt (lt_of_lt_of_le hk (hm k)), (abs_le.mp (hab i)).2⟩
      · funext j
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
        exact (sub_add_cancel _ _).symm

end DiagonalZonotope

end

end OAI

-- ---- platform node ----
open OAI OAI.DiagonalZonotope
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

theorem solution (x : ι → ℝ) :
    x ∈ centered ↔ (∀ i, |x i| ≤ 1) ∧ ∀ i j, |x i - x j| ≤ 1 := by
  first
    | exact OAI.DiagonalZonotope.mem_centered_iff x
    | exact OAI.DiagonalZonotope.mem_centered_iff
    | (apply OAI.DiagonalZonotope.mem_centered_iff <;> assumption)
    | (intros; apply OAI.DiagonalZonotope.mem_centered_iff <;> assumption)
