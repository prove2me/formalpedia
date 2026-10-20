-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.largeWeightFamily_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:25:34.253578+00:00
-- url     : https://prove2.me/submissions/4aab8b10-5c86-4aee-83d0-6828eb289cf8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/Bins.lean:L100-L116
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.largeWeightFamily_cost_le. The node keeps its source
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
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_outright_weight_le

-- ---- from OAI.Combinatorics.DiscreteConvexity.Bins ----
namespace OAI

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem subfamily_weight_sum_le {q : ℝ} {W : Finset α → ℝ}
    (hq : 0 ≤ q) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1) (A : Family α) :
    (∑ U ∈ A, q ^ U.card * W U) ≤ 1 := by
  exact (Finset.sum_le_univ_sum_of_nonneg
    (fun U => mul_nonneg (pow_nonneg hq _) (hW U))).trans hglobal

/-- All large weights together have cost at most one sixty-fourth. -/
theorem largeWeightFamily_cost_le {q : ℝ} {W : Finset α → ℝ}
    (hq : 0 ≤ q) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1) :
    cost (q / (2 : ℝ) ^ 70) (largeWeightFamily W) ≤ 1 / 64 := by
  calc
    _ ≤ ∑ U ∈ largeWeightFamily W, (1 / 64 : ℝ) * (q ^ U.card * W U) := by
      apply Finset.sum_le_sum
      intro U hU
      have hw := mem_largeWeightFamily.mp hU
      simpa only [mul_assoc] using outright_weight_le
        (Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hw.1)) hq hw.2
    _ = (1 / 64 : ℝ) * ∑ U ∈ largeWeightFamily W, q ^ U.card * W U := by
      rw [Finset.mul_sum]
    _ ≤ (1 / 64 : ℝ) * 1 := mul_le_mul_of_nonneg_left
      (subfamily_weight_sum_le hq hW hglobal _) (by norm_num)
    _ = 1 / 64 := by ring

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.largeWeightFamily_cost_le := @_root_.OAI.TalagrandDiscreteConvexity.largeWeightFamily_cost_le
