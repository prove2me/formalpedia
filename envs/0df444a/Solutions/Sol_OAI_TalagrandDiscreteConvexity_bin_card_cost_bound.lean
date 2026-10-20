-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.bin_card_cost_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:24:04.546631+00:00
-- url     : https://prove2.me/submissions/9d6bc454-784d-4ec7-bc9b-8e2de11d0087

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/BinNumerics.lean:L142-L160
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.bin_card_cost_bound. The node keeps its source
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

-- ---- from OAI.Combinatorics.DiscreteConvexity.BinNumerics ----
namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

/-- The lower edge of a bin bounds its cardinality at the reduced density. -/
theorem bin_card_cost_bound {n r h : ℕ} {q : ℝ} (hq : 0 < q)
    (hw : (n : ℝ) * q ^ r * (1 / 2 : ℝ) ^ (h + 1) ≤ 1) :
    (n : ℝ) * (q / (2 : ℝ) ^ 70) ^ r ≤ (2 : ℝ) ^ (h + 1) := by
  have hrho : q / (2 : ℝ) ^ 70 ≤ q := div_le_self hq.le (by norm_num)
  have hden : (1 / 2 : ℝ) ^ (h + 1) * (2 : ℝ) ^ (h + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (n : ℝ) * (q / (2 : ℝ) ^ 70) ^ r ≤ (n : ℝ) * q ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrho r) (by positivity)
    _ = ((n : ℝ) * q ^ r * (1 / 2 : ℝ) ^ (h + 1)) * (2 : ℝ) ^ (h + 1) := by
      calc
        (n : ℝ) * q ^ r = ((n : ℝ) * q ^ r) *
            ((1 / 2 : ℝ) ^ (h + 1) * (2 : ℝ) ^ (h + 1)) := by rw [hden, mul_one]
        _ = _ := by ring
    _ ≤ 1 * (2 : ℝ) ^ (h + 1) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ = (2 : ℝ) ^ (h + 1) := one_mul _

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.bin_card_cost_bound := @_root_.OAI.TalagrandDiscreteConvexity.bin_card_cost_bound
