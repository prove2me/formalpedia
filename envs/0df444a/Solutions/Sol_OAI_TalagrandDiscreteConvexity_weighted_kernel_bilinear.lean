-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.weighted_kernel_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:52:21.806969+00:00
-- url     : https://prove2.me/submissions/6ffba724-d927-4b28-9517-79efe8048343

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/FiniteParseval.lean:L52-L71
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.weighted_kernel_bilinear. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_weighted_transform_bilinear_expansion

-- ---- from OAI.Combinatorics.DiscreteConvexity.FiniteParseval ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

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

variable [DecidableEq J]

/-- A diagonal weighted kernel preserves the corresponding bilinear form. -/
theorem weighted_kernel_bilinear
    (K : I → J → ℝ) (r : I → ℝ) (μ : J → ℝ)
    (hkernel : ∀ x y, (∑ u, r u * K u x * K u y) =
      if x = y then μ x else 0) (f g : J → ℝ) :
    (∑ u, r u * (∑ x, f x * K u x) * (∑ y, g y * K u y)) =
      ∑ x, μ x * f x * g x := by
  rw [weighted_transform_bilinear_expansion]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [hkernel]
  calc
    (∑ y, f x * g y * (if x = y then μ x else 0)) =
        f x * g x * (if x = x then μ x else 0) := by
      apply Finset.sum_eq_single_of_mem x (Finset.mem_univ x)
      intro y _ hy
      rw [ite_eq_right (Ne.symm hy), mul_zero]
    _ = μ x * f x * g x := by
      rw [ite_eq_left rfl]
      ring

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.weighted_kernel_bilinear := @_root_.OAI.TalagrandDiscreteConvexity.weighted_kernel_bilinear
