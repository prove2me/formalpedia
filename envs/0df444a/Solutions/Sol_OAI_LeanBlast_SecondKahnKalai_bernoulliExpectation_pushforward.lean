-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:33:42.486588+00:00
-- url     : https://prove2.me/submissions/73a9da6d-11d7-4bac-a606-e7f81a190c5b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/BernoulliCoupling.lean:L59-L73
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_pushforward. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling

-- ---- from OAI.Combinatorics.GraphThreshold.BernoulliCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem bernoulliExpectation_pushforward (p : ℝ) (T : Finset X → Finset X)
    (F : Finset X → ℝ) :
    bernoulliExpectation p (fun W => F (T W)) =
      ∑ Y : Finset X, bernoulliExpectation p (fun W => if T W = Y then 1 else 0) * F Y := by
  unfold bernoulliExpectation
  calc
    (∑ W : Finset X, bernoulliWeight p W * F (T W)) =
        ∑ W : Finset X, ∑ Y : Finset X,
          (bernoulliWeight p W * (if T W = Y then 1 else 0)) * F Y := by
      apply Finset.sum_congr rfl
      intro W _
      simp [mul_ite, ite_mul]
    _ = ∑ Y : Finset X, ∑ W : Finset X,
          (bernoulliWeight p W * (if T W = Y then 1 else 0)) * F Y := Finset.sum_comm
    _ = _ := by simp only [Finset.sum_mul]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_pushforward := @_root_.OAI.LeanBlast.SecondKahnKalai.bernoulliExpectation_pushforward
