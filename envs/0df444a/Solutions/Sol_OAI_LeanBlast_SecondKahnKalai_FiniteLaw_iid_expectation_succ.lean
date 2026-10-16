-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.FiniteLaw.iid_expectation_succ
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:34:50.895305+00:00
-- url     : https://prove2.me/submissions/5828a8c3-9e86-4064-baad-c63500dcae5d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/AdaptiveTrials.lean:L40-L56
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.FiniteLaw.iid_expectation_succ. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials

-- ---- from OAI.Combinatorics.GraphThreshold.AdaptiveTrials ----
namespace OAI

/-!
# Finite adaptive trials

The draws are independent, but whether an attempt succeeds may depend on the
entire current state. The head-tail identity below performs the conditioning
explicitly. No independence assumption is made about success indicators.
-/

noncomputable section
open scoped BigOperators

universe u v

namespace LeanBlast.SecondKahnKalai

variable {State : Type u} {Ω : Type v}

namespace FiniteLaw

variable [Fintype Ω]

/-- Exact finite conditional-expectation identity for a fresh independent draw. -/
theorem iid_expectation_succ (μ : FiniteLaw Ω) (n : ℕ)
    (f : (Fin (n + 1) → Ω) → ℝ) :
    (μ.iid (n + 1)).expectation f =
      μ.expectation (fun head => (μ.iid n).expectation (fun tail => f (Fin.cases head tail))) := by
  unfold expectation
  rw [← (trialSplitEquiv Ω n).sum_comp
    (fun draws => (μ.iid (n + 1)).weight draws * f draws)]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro head _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  change (μ.iid (n + 1)).weight (Fin.cases head tail) * f (Fin.cases head tail) = _
  rw [iid_weight_cons]
  ring

end FiniteLaw

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai OAI.LeanBlast.SecondKahnKalai.FiniteLaw
open scoped BigOperators


theorem solution.{v} : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.FiniteLaw.iid_expectation_succ.{v} := @_root_.OAI.LeanBlast.SecondKahnKalai.FiniteLaw.iid_expectation_succ.{v}
