-- Prove2me | solution 1 for OAI.Dixmier.rectangleEdges_card_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:36:08.980623+00:00
-- url     : https://prove2.me/submissions/30d87d1b-2c1a-4d1f-97f0-9835974417f1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/SparseSplitting.lean:L57-L74
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.rectangleEdges_card_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting

-- ---- from OAI.Analysis.Unitarizability.SparseSplitting ----
namespace OAI

/-! Spectral norm bounds imply sparse endpoint assignments.
The input is a bounded convolution operator with its coefficient formula. -/
noncomputable section
namespace Dixmier
open Finset
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {G I : Type*} [Fintype I]

theorem indicatorL2_norm_sq (U : Finset G) : ‖indicatorL2 U‖ ^ 2 = U.card := by
  have h := lp.norm_sum_single (p := 2) (by norm_num) (fun _ : G => (1 : ℂ)) U
  simpa [indicatorL2] using h

theorem indicatorL2_norm (U : Finset G) : ‖indicatorL2 U‖ = Real.sqrt U.card := by
  rw [← indicatorL2_norm_sq, Real.sqrt_sq (norm_nonneg _)]

variable [Group G]

/-- Pairing convolution with the two indicator vectors counts labelled edges. -/
theorem indicator_convolution_inner (s : I → G)
    (A : ScalarL2 G →L[ℂ] ScalarL2 G)
    (hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ i, ξ (x * s i))
    (U V : Finset G) :
    ⟪indicatorL2 U, A (indicatorL2 V)⟫_ℂ = (rectangleEdges s U V).card := by
  calc
    _ = ∑ x ∈ U, ∑ i, if x * s i ∈ V then (1 : ℂ) else 0 := by
      change ⟪∑ x ∈ U, lp.single 2 x (1 : ℂ), A (indicatorL2 V)⟫_ℂ = _
      simp only [sum_inner, lp.inner_single_left, hA, indicatorL2_apply]
      simp
    _ = (rectangleEdges s U V).card := by
      rw [Finset.card_eq_sum_ones]
      simp only [Nat.cast_sum, Nat.cast_one]
      rw [rectangleEdges, Finset.sum_filter, Finset.sum_product]

/-- The rectangular edge-count bound with all multiplicities retained. -/
theorem rectangleEdges_card_le (s : I → G)
    (A : ScalarL2 G →L[ℂ] ScalarL2 G)
    (hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ i, ξ (x * s i))
    {q : ℝ} (hq : ‖A‖ ≤ q) (U V : Finset G) :
    ((rectangleEdges s U V).card : ℝ) ≤ q * Real.sqrt ((U.card : ℝ) * V.card) := by
  have hq0 : 0 ≤ q := (norm_nonneg A).trans hq
  calc
    _ = ‖⟪indicatorL2 U, A (indicatorL2 V)⟫_ℂ‖ := by
      rw [indicator_convolution_inner s A hA]
      simp
    _ ≤ ‖indicatorL2 U‖ * ‖A (indicatorL2 V)‖ := norm_inner_le_norm _ _
    _ ≤ ‖indicatorL2 U‖ * (q * ‖indicatorL2 V‖) :=
      mul_le_mul_of_nonneg_left ((A.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hq (norm_nonneg _))) (norm_nonneg _)
    _ = q * Real.sqrt ((U.card : ℝ) * V.card) := by
      rw [indicatorL2_norm, indicatorL2_norm, Real.sqrt_mul (Nat.cast_nonneg _)]
      ring

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
open Finset
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {G I : Type*} [Fintype I]
variable [Group G]

theorem solution (s : I → G)
    (A : ScalarL2 G →L[ℂ] ScalarL2 G)
    (hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ i, ξ (x * s i))
    {q : ℝ} (hq : ‖A‖ ≤ q) (U V : Finset G) :
    ((rectangleEdges s U V).card : ℝ) ≤ q * Real.sqrt ((U.card : ℝ) * V.card) := by
  first
    | exact OAI.Dixmier.rectangleEdges_card_le s A hA hq U V
    | exact OAI.Dixmier.rectangleEdges_card_le
    | (apply OAI.Dixmier.rectangleEdges_card_le <;> assumption)
    | (intros; apply OAI.Dixmier.rectangleEdges_card_le <;> assumption)
