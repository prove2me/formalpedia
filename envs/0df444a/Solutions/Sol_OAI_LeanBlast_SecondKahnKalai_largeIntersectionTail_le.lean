-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.largeIntersectionTail_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:20:40.970737+00:00
-- url     : https://prove2.me/submissions/1b8c52d6-59c9-4acc-b044-f5858b5ef860

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/LocalFailureNumerics.lean:L63-L77
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.largeIntersectionTail_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics

-- ---- from OAI.Combinatorics.GraphThreshold.LocalFailureNumerics ----
namespace OAI

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

/-- A term beyond half the capacity has the required exponential decay. -/
theorem large_intersection_power_le {m r : ℕ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-50)) (hr : m < 2 * r) :
    q ^ r ≤ Real.exp (-25 * (m : ℝ)) := by
  have hr' : (m : ℝ) < 2 * (r : ℝ) := by exact_mod_cast hr
  calc
    q ^ r ≤ Real.exp (-50) ^ r := pow_le_pow_left₀ hq0 hq r
    _ = Real.exp ((r : ℝ) * (-50)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-25 * (m : ℝ)) := Real.exp_le_exp.mpr (by linarith)

theorem largeIntersectionTail_le {m : ℕ} {q : ℝ}
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp (-50)) :
    largeIntersectionTail m q ≤ (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) := by
  have hsum : (∑ r ∈ range (m + 1), (m.choose r : ℝ)) = (2 : ℝ) ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  unfold largeIntersectionTail
  calc
    (∑ r ∈ range (m + 1), if m < 2 * r then (m.choose r : ℝ) * q ^ r else 0) ≤
        ∑ r ∈ range (m + 1), (m.choose r : ℝ) * Real.exp (-25 * (m : ℝ)) := by
      apply sum_le_sum
      intro r hr
      split_ifs with h
      · exact mul_le_mul_of_nonneg_left (large_intersection_power_le hq0 hq h) (by positivity)
      · positivity
    _ = (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) := by rw [← sum_mul, hsum]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.largeIntersectionTail_le := @_root_.OAI.LeanBlast.SecondKahnKalai.largeIntersectionTail_le
