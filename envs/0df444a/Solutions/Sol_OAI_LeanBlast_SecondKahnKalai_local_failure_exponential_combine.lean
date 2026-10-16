-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.local_failure_exponential_combine
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:21:46.276057+00:00
-- url     : https://prove2.me/submissions/4f1ca5aa-487e-44eb-b47c-98108ddd0441

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/LocalFailureNumerics.lean:L79-L101
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.local_failure_exponential_combine. The node keeps its source
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

theorem two_lt_exp_one : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two

theorem two_pow_le_exp_nat (m : ℕ) : (2 : ℝ) ^ m ≤ Real.exp (m : ℝ) := by
  calc
    (2 : ℝ) ^ m ≤ Real.exp 1 ^ m := pow_le_pow_left₀ (by norm_num) two_lt_exp_one.le m
    _ = Real.exp (m : ℝ) := by rw [← Real.exp_nat_mul]; simp

theorem local_failure_exponential_combine {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (-10 * (m : ℝ)) +
        Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) ≤
      Real.exp (-9 * (m : ℝ)) := by
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hterm : Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m *
      Real.exp (-25 * (m : ℝ)) ≤ Real.exp (-10 * (m : ℝ)) := by
    calc
      Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) ≤
          Real.exp (10 * (m : ℝ)) * Real.exp (m : ℝ) * Real.exp (-25 * (m : ℝ)) := by
        gcongr
        exact two_pow_le_exp_nat m
      _ = Real.exp (-14 * (m : ℝ)) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-10 * (m : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp (m : ℝ) :=
    two_lt_exp_one.le.trans (Real.exp_le_exp.mpr hm1)
  calc
    Real.exp (-10 * (m : ℝ)) +
        Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) ≤
      2 * Real.exp (-10 * (m : ℝ)) := by linarith
    _ ≤ Real.exp (m : ℝ) * Real.exp (-10 * (m : ℝ)) := by gcongr
    _ = Real.exp (-9 * (m : ℝ)) := by rw [← Real.exp_add]; congr 1; ring

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.local_failure_exponential_combine := @_root_.OAI.LeanBlast.SecondKahnKalai.local_failure_exponential_combine
