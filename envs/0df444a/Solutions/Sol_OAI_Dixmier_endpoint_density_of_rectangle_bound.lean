-- Prove2me | solution 1 for OAI.Dixmier.endpoint_density_of_rectangle_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:36:41.94106+00:00
-- url     : https://prove2.me/submissions/c89329b2-689b-4e93-8e15-bc80811bde50

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/SparseSplitting.lean:L91-L110
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.endpoint_density_of_rectangle_bound. The node keeps its source
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

variable [Group G]

/-- Every finite edge family lies in the rectangle of its endpoints. -/
theorem edges_subset_endpoint_rectangle (s : I → G) (F : Finset (G × I)) :
    F ⊆ rectangleEdges s (F.image Prod.fst) (F.image fun e => e.1 * s e.2) := by
  intro e he
  simp only [rectangleEdges, mem_filter, mem_product, mem_univ, and_true]
  exact ⟨mem_image.mpr ⟨e, he, rfl⟩, mem_image.mpr ⟨e, he, rfl⟩⟩

/-- Arithmetic used in the Hall argument, including its factor one half. -/
theorem sqrt_mul_le_half_add {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u * v) ≤ (u + v) / 2 := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [sq_nonneg (u - v)]

/-- The finite Hall density follows from the rectangular spectral estimate. -/
theorem endpoint_density_of_rectangle_bound (s : I → G) {q : ℝ} {r : ℕ}
    (hq : 0 ≤ q) (hqr : q ≤ r)
    (hrect : ∀ U V : Finset G, ((rectangleEdges s U V).card : ℝ) ≤
      q * Real.sqrt ((U.card : ℝ) * V.card))
    (F : Finset (G × I)) :
    F.card ≤ r * ((F.image Prod.fst).card + (F.image fun e => e.1 * s e.2).card) := by
  let U := F.image Prod.fst
  let V := F.image fun e => e.1 * s e.2
  have he : (F.card : ℝ) ≤ (rectangleEdges s U V).card := by
    exact_mod_cast card_le_card (edges_subset_endpoint_rectangle s F)
  have hsum : (0 : ℝ) ≤ (U.card : ℝ) + V.card := by positivity
  have hhalf : ((U.card : ℝ) + V.card) / 2 ≤ (U.card : ℝ) + V.card := by linarith
  have h : (F.card : ℝ) ≤ (r : ℝ) * ((U.card : ℝ) + V.card) := calc
    _ ≤ q * Real.sqrt ((U.card : ℝ) * V.card) := he.trans (hrect U V)
    _ ≤ q * (((U.card : ℝ) + V.card) / 2) :=
      mul_le_mul_of_nonneg_left (sqrt_mul_le_half_add (by positivity) (by positivity)) hq
    _ ≤ q * ((U.card : ℝ) + V.card) := mul_le_mul_of_nonneg_left hhalf hq
    _ ≤ (r : ℝ) * ((U.card : ℝ) + V.card) := mul_le_mul_of_nonneg_right hqr hsum
  exact_mod_cast h

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

theorem solution (s : I → G) {q : ℝ} {r : ℕ}
    (hq : 0 ≤ q) (hqr : q ≤ r)
    (hrect : ∀ U V : Finset G, ((rectangleEdges s U V).card : ℝ) ≤
      q * Real.sqrt ((U.card : ℝ) * V.card))
    (F : Finset (G × I)) :
    F.card ≤ r * ((F.image Prod.fst).card + (F.image fun e => e.1 * s e.2).card) := by
  first
    | exact OAI.Dixmier.endpoint_density_of_rectangle_bound s hq hqr hrect F
    | exact OAI.Dixmier.endpoint_density_of_rectangle_bound
    | (apply OAI.Dixmier.endpoint_density_of_rectangle_bound <;> assumption)
    | (intros; apply OAI.Dixmier.endpoint_density_of_rectangle_bound <;> assumption)
