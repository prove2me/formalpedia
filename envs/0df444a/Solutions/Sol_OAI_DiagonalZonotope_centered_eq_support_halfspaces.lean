-- Prove2me | solution 1 for OAI.DiagonalZonotope.centered_eq_support_halfspaces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:17:53.868693+00:00
-- url     : https://prove2.me/submissions/4c79a459-39d4-4bdf-bb0f-f7327ecd170c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Halfspaces.lean:L39-L69
-- (upload_full_project.md Phase 4): solution for node OAI.DiagonalZonotope.centered_eq_support_halfspaces. The node keeps its source
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
import Theorems.Thm_OAI_DiagonalZonotope_centered_support_le
import Theorems.Thm_OAI_DiagonalZonotope_mem_centered_iff

-- ---- from OAI.Geometry.Zonotope.Halfspaces ----
namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma abs_single_difference (i j k : ι) (hij : i ≠ j) :
    |((Pi.single i (1 : ℝ) : ι → ℝ)) k - ((Pi.single j (1 : ℝ) : ι → ℝ)) k| =
      ((Pi.single i (1 : ℝ) : ι → ℝ)) k + ((Pi.single j (1 : ℝ) : ι → ℝ)) k := by
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [Ne.symm hij]
    · simp [hki, hkj]

lemma coordinate_difference_support (i j : ι) (hij : i ≠ j) :
    ((∑ k, |((Pi.single i (1 : ℝ) : ι → ℝ) - (Pi.single j (1 : ℝ) : ι → ℝ)) k|) +
      |∑ k, ((Pi.single i (1 : ℝ) : ι → ℝ) - (Pi.single j (1 : ℝ) : ι → ℝ)) k|) / 2 = 1 := by
  have ha : (∑ k, |((Pi.single i (1 : ℝ) : ι → ℝ) - (Pi.single j (1 : ℝ) : ι → ℝ)) k|) = 2 := by
    calc
      _ = ∑ k, (((Pi.single i (1 : ℝ) : ι → ℝ)) k + ((Pi.single j (1 : ℝ) : ι → ℝ)) k) := by
        apply Finset.sum_congr rfl
        intro k _
        exact abs_single_difference i j k hij
      _ = 2 := by norm_num [Finset.sum_add_distrib, Pi.single_apply]
  have hs : (∑ k, ((Pi.single i (1 : ℝ) : ι → ℝ) - (Pi.single j (1 : ℝ) : ι → ℝ)) k) = 0 := by
    simp [Pi.sub_apply, Finset.sum_sub_distrib, Pi.single_apply]
  rw [ha, hs]
  norm_num

/-- Explicit coordinate tests suffice to recover the body from all support bounds. -/
theorem centered_eq_support_halfspaces :
    (centered : Set (ι → ℝ)) =
      {x | ∀ u : ι → ℝ, (∑ i, u i * x i) ≤
        ((∑ i, |u i|) + |∑ i, u i|) / 2} := by
  ext x
  constructor
  · intro hx u
    exact centered_support_le u x hx
  · intro hx
    apply (mem_centered_iff x).mpr
    constructor
    · intro i
      have hp := hx ((Pi.single i (1 : ℝ) : ι → ℝ))
      have hn := hx ((Pi.single i (-1 : ℝ) : ι → ℝ))
      have hp' : x i ≤ 1 := by simpa [Pi.single_apply, apply_ite] using hp
      have hn' : -x i ≤ 1 := by simpa [Pi.single_apply, apply_ite] using hn
      exact abs_le.mpr ⟨by linarith, hp'⟩
    · intro i j
      by_cases hij : i = j
      · subst j
        simp
      · have hp := hx ((Pi.single i (1 : ℝ) : ι → ℝ) - (Pi.single j (1 : ℝ) : ι → ℝ))
        have hn := hx ((Pi.single j (1 : ℝ) : ι → ℝ) - (Pi.single i (1 : ℝ) : ι → ℝ))
        rw [coordinate_difference_support i j hij] at hp
        rw [coordinate_difference_support j i (Ne.symm hij)] at hn
        have hp' : x i - x j ≤ 1 := by
          simpa [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply] using hp
        have hn' : x j - x i ≤ 1 := by
          simpa [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply] using hn
        exact abs_le.mpr ⟨by linarith, hp'⟩

end DiagonalZonotope

end

end OAI

-- ---- platform node ----
open OAI OAI.DiagonalZonotope
open Set
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem solution :
    (centered : Set (ι → ℝ)) =
      {x | ∀ u : ι → ℝ, (∑ i, u i * x i) ≤
        ((∑ i, |u i|) + |∑ i, u i|) / 2} := by
  first
    | exact OAI.DiagonalZonotope.centered_eq_support_halfspaces
    | (apply OAI.DiagonalZonotope.centered_eq_support_halfspaces <;> assumption)
    | (intros; apply OAI.DiagonalZonotope.centered_eq_support_halfspaces <;> assumption)
