-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.adaptiveRun_rank_failure_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:36:52.692193+00:00
-- url     : https://prove2.me/submissions/33820925-d0e6-4884-8e57-57ea2defc2fd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/AdaptiveTrials.lean:L127-L156
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.adaptiveRun_rank_failure_bound. The node keeps its source
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

end FiniteLaw

theorem adaptiveRun_rank_le (rank : State → ℕ) (step : State → Ω → State)
    (hstep : ∀ state draw, rank (step state draw) ≤ rank state)
    (n : ℕ) (initial : State) (draws : Fin n → Ω) :
    rank (adaptiveRun step n initial draws) ≤ rank initial := by
  induction n generalizing initial with
  | zero => exact le_rfl
  | succ n ih =>
      exact (ih (step initial (draws 0)) (fun i => draws i.succ)).trans (hstep _ _)

/-- On a trajectory that is still incomplete, every nonfailed attempt consumes
at least one unit of rank. The conclusion includes the final positive rank. -/
theorem adaptiveRun_rank_failure_bound (rank : State → ℕ) (step : State → Ω → State)
    (hstep : ∀ state draw, rank (step state draw) ≤ rank state)
    (n : ℕ) (initial : State) (draws : Fin n → Ω)
    (hincomplete : rank (adaptiveRun step n initial draws) ≠ 0) :
    n + rank (adaptiveRun step n initial draws) ≤
      rank initial + adaptiveFailureCount step (rankFailure rank step) n initial draws := by
  induction n generalizing initial with
  | zero => simp [adaptiveRun, adaptiveFailureCount]
  | succ n ih =>
      have htail := ih (step initial (draws 0)) (fun i => draws i.succ) hincomplete
      have hdecrease := hstep initial (draws 0)
      have hinit : rank initial ≠ 0 := by
        have hbound := adaptiveRun_rank_le rank step hstep (n + 1) initial draws
        omega
      change (n + 1) + rank (adaptiveRun step n (step initial (draws 0))
          (fun i => draws i.succ)) ≤
        rank initial + ((if rankFailure rank step initial (draws 0) then 1 else 0) +
          adaptiveFailureCount step (rankFailure rank step) n (step initial (draws 0))
            (fun i => draws i.succ))
      by_cases hprogress : rank (step initial (draws 0)) < rank initial
      · have hbad : rankFailure rank step initial (draws 0) = false := by
          simp [rankFailure, hprogress]
        simp [hbad]
        omega
      · have hbad : rankFailure rank step initial (draws 0) = true := by
          simp [rankFailure, hinit, hprogress]
        simp [hbad]
        omega

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.adaptiveRun_rank_failure_bound.{u,v} := @_root_.OAI.LeanBlast.SecondKahnKalai.adaptiveRun_rank_failure_bound.{u,v}
