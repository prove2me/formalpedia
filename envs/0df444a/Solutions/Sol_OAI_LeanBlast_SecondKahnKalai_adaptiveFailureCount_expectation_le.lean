-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.adaptiveFailureCount_expectation_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:35:37.290403+00:00
-- url     : https://prove2.me/submissions/9a529fa1-1730-4742-9423-fce3d5743dae

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/AdaptiveTrials.lean:L74-L110
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.adaptiveFailureCount_expectation_le. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_FiniteLaw_iid_expectation_succ

-- ---- from OAI.Combinatorics.GraphThreshold.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_add (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    μ.expectation (fun ω => f ω + g ω) = μ.expectation f + μ.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

end LeanBlast.SecondKahnKalai

end

end OAI

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

/-- A uniform state-dependent failure bound controls expected total failures.
This proof conditions at every step on the actual preceding draw and state. -/
theorem adaptiveFailureCount_expectation_le [Fintype Ω]
    (μ : FiniteLaw Ω) (step : State → Ω → State) (bad : State → Ω → Bool)
    (q : ℝ) (hbad : ∀ state, μ.prob (fun draw => bad state draw = true) ≤ q)
    (n : ℕ) (initial : State) :
    (μ.iid n).expectation (fun draws => (adaptiveFailureCount step bad n initial draws : ℝ)) ≤
      (n : ℝ) * q := by
  induction n generalizing initial with
  | zero => simp [adaptiveFailureCount]
  | succ n ih =>
      rw [FiniteLaw.iid_expectation_succ]
      have hstep : ∀ head,
          (μ.iid n).expectation (fun tail =>
            (adaptiveFailureCount step bad (n + 1) initial (Fin.cases head tail) : ℝ)) ≤
          (if bad initial head then (1 : ℝ) else 0) + (n : ℝ) * q := by
        intro head
        by_cases hbad : bad initial head = true
        · simpa only [adaptiveFailureCount, Fin.cases_zero, Fin.cases_succ, hbad,
            ite_true, Nat.cast_add, Nat.cast_one, FiniteLaw.expectation_add,
            FiniteLaw.expectation_const] using add_le_add_right (ih (step initial head)) 1
        · simpa only [adaptiveFailureCount, Fin.cases_zero, Fin.cases_succ, hbad,
            Bool.false_eq_true, ite_false, Nat.zero_add, zero_add] using ih (step initial head)
      have h := (μ.expectation_mono hstep).trans_eq
        (μ.expectation_add (fun head => if bad initial head then (1 : ℝ) else 0)
          (fun _ => (n : ℝ) * q))
      have hindicator : μ.expectation (fun head => if bad initial head then (1 : ℝ) else 0) =
          μ.prob (fun draw => bad initial draw = true) := by
        classical
        unfold FiniteLaw.expectation FiniteLaw.prob
        apply Finset.sum_congr rfl
        intro draw _
        cases hdraw : bad initial draw <;> simp [hdraw]
      rw [FiniteLaw.expectation_const, hindicator] at h
      have hlocal := hbad initial
      push_cast
      linarith

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.adaptiveFailureCount_expectation_le.{u,v} := @_root_.OAI.LeanBlast.SecondKahnKalai.adaptiveFailureCount_expectation_le.{u,v}
