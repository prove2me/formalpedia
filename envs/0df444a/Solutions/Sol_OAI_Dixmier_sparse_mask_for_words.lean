-- Prove2me | solution 1 for OAI.Dixmier.sparse_mask_for_words
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:37:20.106182+00:00
-- url     : https://prove2.me/submissions/cd429015-b5ef-4093-8d9c-a8601746c759

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Regular.lean:L103-L125
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.sparse_mask_for_words. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Theorems.Thm_OAI_Dixmier_endpoint_density_of_rectangle_bound
import Theorems.Thm_OAI_Dixmier_exists_sparse_mask
import Theorems.Thm_OAI_Dixmier_rectangleEdges_card_le

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

/-- Sparse assignment from a bounded convolution operator, at any integer
capacity above its norm. -/
theorem sparse_mask_of_convolution_bound (s : I → G)
    (A : ScalarL2 G →L[ℂ] ScalarL2 G)
    (hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ i, ξ (x * s i))
    {r : ℕ} (hr : ‖A‖ ≤ r) :
    ∃ a : G → I → Bool, (∀ x, (rowOnes a x).card ≤ r) ∧
      ∀ y, (columnZeros a s y).card ≤ r := by
  apply exists_sparse_mask
  exact endpoint_density_of_rectangle_bound s (norm_nonneg A) hr
    (rectangleEdges_card_le s A hA le_rfl)

end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Regular ----
namespace OAI

/-! Regular convolution operators, product lists with multiplicity,
and sparse splitting from a contracting average. -/
noncomputable section
namespace Dixmier
universe u
open Finset
attribute [local instance] Classical.propDecidable

variable {G : Type*}

variable [Group G]

/-- Product lists are indexed by words, not by their possibly colliding values. -/
theorem sum_wordProduct {I R : Type*} [Fintype I] [Semiring R]
    (s : I → G) (φ : G →* R) (n : ℕ) :
    (∑ w : Word I n, φ (wordProduct s n w)) = (∑ i, φ (s i)) ^ n := by
  induction n with
  | zero =>
    change (∑ w : PUnit, φ (1 : G)) = _
    simp
  | succ n ih =>
    change (∑ w : I × Word I n, φ (s w.1 * wordProduct s n w.2)) = _
    simp only [Fintype.sum_prod_type, map_mul, ← Finset.mul_sum, ← Finset.sum_mul, ih,
      pow_succ']

/-- Sparse splitting for words from a norm bound on the finite average. -/
theorem sparse_mask_for_words {I : Type*} [Fintype I] (s : I → G)
    {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (havg : ‖∑ i, rightRegular (s i)‖ ≤ (Fintype.card I : ℝ) * ρ) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ a : G → Word I ℓ → Bool,
      (∀ x, (rowOnes a x).card ≤ ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊) ∧
      ∀ y, (columnZeros a (wordProduct s ℓ) y).card ≤
        ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊ := by
  let A : ScalarL2 G →L[ℂ] ScalarL2 G := ∑ w : Word I ℓ, rightRegular (wordProduct s ℓ w)
  have hA : ∀ (ξ : ScalarL2 G) (x : G), A ξ x = ∑ w, ξ (x * wordProduct s ℓ w) := by
    intro ξ x
    simp only [A, _root_.sum_apply]
    rw [lp.coeFn_sum]
    simp only [Finset.sum_apply, rightRegular_apply]
  apply sparse_mask_of_convolution_bound (wordProduct s ℓ) A hA
  calc
    ‖A‖ = ‖(∑ i, rightRegular (s i)) ^ ℓ‖ := by
      dsimp only [A]
      rw [sum_wordProduct]
    _ ≤ ‖∑ i, rightRegular (s i)‖ ^ ℓ := norm_pow_le' _ hℓ
    _ ≤ ((Fintype.card I : ℝ) * ρ) ^ ℓ := pow_le_pow_left₀ (norm_nonneg _) havg ℓ
    _ = (Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ := mul_pow _ _ _
    _ ≤ ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊ := Nat.le_ceil _

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
universe u
open Finset
attribute [local instance] Classical.propDecidable
variable {G : Type*}
variable [Group G]

theorem solution {I : Type*} [Fintype I] (s : I → G)
    {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (havg : ‖∑ i, rightRegular (s i)‖ ≤ (Fintype.card I : ℝ) * ρ) (ℓ : ℕ) (hℓ : 0 < ℓ) :
    ∃ a : G → Word I ℓ → Bool,
      (∀ x, (rowOnes a x).card ≤ ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊) ∧
      ∀ y, (columnZeros a (wordProduct s ℓ) y).card ≤
        ⌈(Fintype.card I : ℝ) ^ ℓ * ρ ^ ℓ⌉₊ := by
  first
    | exact OAI.Dixmier.sparse_mask_for_words s _hρ havg ℓ hℓ
    | exact OAI.Dixmier.sparse_mask_for_words
    | (apply OAI.Dixmier.sparse_mask_for_words <;> assumption)
    | (intros; apply OAI.Dixmier.sparse_mask_for_words <;> assumption)
