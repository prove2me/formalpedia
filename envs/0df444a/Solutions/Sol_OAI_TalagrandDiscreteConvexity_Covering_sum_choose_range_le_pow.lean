-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.Covering.sum_choose_range_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:27:09.436413+00:00
-- url     : https://prove2.me/submissions/fe67002e-6f6e-48be-b89a-af2f249f4acb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringBinomialBounds.lean:L27-L42
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.Covering.sum_choose_range_le_pow. The node keeps its source
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

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoveringBinomialBounds ----
namespace OAI

/-!
# Counting bounded-size subsets

Subsets of cardinality at most `r` are counted by a partial binomial sum.
The elementary bound by `(1 + B.card)^r` includes `r = 0` and empty `B`.
-/

namespace TalagrandDiscreteConvexity.Covering

open scoped BigOperators

/-- A partial binomial sum is bounded by the number of length-`r` words
over an alphabet with `n + 1` letters. -/
theorem sum_choose_range_le_pow (n r : ℕ) :
    (∑ i ∈ Finset.range (r + 1), Nat.choose n i) ≤ (1 + n) ^ r := by
  calc
    (∑ i ∈ Finset.range (r + 1), Nat.choose n i)
        ≤ ∑ i ∈ Finset.range (r + 1), n ^ i * Nat.choose r i := by
      apply Finset.sum_le_sum
      intro i hi
      have hc : 1 ≤ Nat.choose r i :=
        Nat.choose_pos (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      exact (Nat.choose_le_pow n i).trans (by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (n ^ i) hc)
    _ = (n + 1) ^ r := by
      simpa using (add_pow n 1 r).symm
    _ = (1 + n) ^ r := by rw [Nat.add_comm]

end TalagrandDiscreteConvexity.Covering

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.Covering
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.Covering.sum_choose_range_le_pow := @_root_.OAI.TalagrandDiscreteConvexity.Covering.sum_choose_range_le_pow
