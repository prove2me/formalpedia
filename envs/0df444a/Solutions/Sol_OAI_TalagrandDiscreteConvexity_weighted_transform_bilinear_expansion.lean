-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.weighted_transform_bilinear_expansion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:51:28.956488+00:00
-- url     : https://prove2.me/submissions/dcbba113-ede3-4501-b974-37706199b12a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/FiniteParseval.lean:L26-L48
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.weighted_transform_bilinear_expansion. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FourierWeights

-- ---- from OAI.Combinatorics.DiscreteConvexity.FiniteParseval ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Finite Parseval identities from a weighted kernel

The algebraic statement below separates finite-sum rearrangement from the
concrete kernel identity. Neither the expansion nor the Parseval identity
requires nonnegative weights.
-/

namespace TalagrandDiscreteConvexity

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Expanding a weighted product of transforms gives the associated kernel. -/
theorem weighted_transform_bilinear_expansion
    (K : I → J → ℝ) (r : I → ℝ) (f g : J → ℝ) :
    (∑ u, r u * (∑ x, f x * K u x) * (∑ y, g y * K u y)) =
      ∑ x, ∑ y, f x * g y * (∑ u, r u * K u x * K u y) := by
  calc
    _ = ∑ u, ∑ x, ∑ y, f x * g y * (r u * K u x * K u y) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [mul_assoc, Fintype.sum_mul_sum]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ x, ∑ y, ∑ u, f x * g y * (r u * K u x * K u y) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ x, ∑ y, f x * g y * (∑ u, r u * K u x * K u y) := by
      simp only [Finset.mul_sum]

variable [DecidableEq J]

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.weighted_transform_bilinear_expansion := @_root_.OAI.TalagrandDiscreteConvexity.weighted_transform_bilinear_expansion
