-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.adaptive_rank_completion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:38:35.582598+00:00
-- url     : https://prove2.me/submissions/4fa206f4-6ace-470f-a7a3-f496189c0ce3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/AdaptiveTrials.lean:L183-L223
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.adaptive_rank_completion. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_adaptiveFailureCount_expectation_le
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_adaptiveRun_rank_failure_bound

-- ---- from OAI.Combinatorics.GraphThreshold.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_smul (μ : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expectation (fun ω => c * f ω) = c * μ.expectation f := by
  simp [expectation, Finset.mul_sum, mul_left_comm]

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

theorem prob_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob P = μ.expectation (fun ω => if P ω then 1 else 0) := by
  classical
  simp [prob, expectation, mul_ite]

theorem prob_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) :
    μ.prob P ≤ μ.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω
  · simp [hp, hPQ ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg ω]

theorem prob_compl (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob (fun ω => ¬ P ω) = 1 - μ.prob P := by
  classical
  have h : μ.prob P + μ.prob (fun ω => ¬ P ω) = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← μ.total]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hp : P ω <;> simp [hp]
  linarith

theorem prob_le_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hP : ∀ ω, P ω → 1 ≤ f ω) : μ.prob P ≤ μ.expectation f := by
  classical
  rw [prob_eq_expectation]
  apply μ.expectation_mono
  intro ω
  by_cases hp : P ω
  · simpa [hp] using hP ω hp
  · simpa [hp] using hf ω

theorem prob_ge_le_expectation_div (μ : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) {t : ℝ} (ht : 0 < t) :
    μ.prob (fun ω => t ≤ f ω) ≤ μ.expectation f / t := by
  have h := μ.prob_le_expectation (fun ω => t ≤ f ω) (fun ω => t⁻¹ * f ω)
    (fun ω => mul_nonneg (inv_nonneg.mpr ht.le) (hf ω))
    (fun ω hω => by simpa [ht.ne'] using mul_le_mul_of_nonneg_left hω (inv_nonneg.mpr ht.le))
  rw [expectation_smul] at h
  simpa [div_eq_mul_inv, mul_comm] using h

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

theorem rankFailure_probability_le [Fintype Ω] (μ : FiniteLaw Ω)
    (rank : State → ℕ) (step : State → Ω → State)
    (hprogress : ∀ state, rank state ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun draw => rank (step state draw) < rank state))
    (state : State) :
    μ.prob (fun draw => rankFailure rank step state draw = true) ≤ (1 / 4 : ℝ) := by
  by_cases hz : rank state = 0
  · simp [rankFailure, hz, FiniteLaw.prob]
  · have heq : μ.prob (fun draw => rankFailure rank step state draw = true) =
        1 - μ.prob (fun draw => rank (step state draw) < rank state) := by
      simpa [rankFailure, hz] using
        μ.prob_compl (fun draw => rank (step state draw) < rank state)
    rw [heq]
    linarith [hprogress state hz]

/-- Noncompletion by time `4*s` forces at least `3*s+1` failed attempts. -/
theorem adaptive_incomplete_many_failures (rank : State → ℕ) (step : State → Ω → State)
    (hstep : ∀ state draw, rank (step state draw) ≤ rank state)
    (s : ℕ) (initial : State) (hinitial : rank initial ≤ s)
    (draws : Fin (4 * s) → Ω)
    (hincomplete : rank (adaptiveRun step (4 * s) initial draws) ≠ 0) :
    3 * s + 1 ≤ adaptiveFailureCount step (rankFailure rank step) (4 * s) initial draws := by
  have h := adaptiveRun_rank_failure_bound rank step hstep (4 * s) initial draws hincomplete
  omega

/-- Adaptive finite completion bound. Only fresh draws are independent.
The chance of progress can depend arbitrarily on the current state.
The case `s=0` is included. -/
theorem adaptive_rank_completion [Fintype Ω] (μ : FiniteLaw Ω)
    (rank : State → ℕ) (step : State → Ω → State)
    (hstep : ∀ state draw, rank (step state draw) ≤ rank state)
    (hprogress : ∀ state, rank state ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun draw => rank (step state draw) < rank state))
    (s : ℕ) (initial : State) (hinitial : rank initial ≤ s) :
    (2 / 3 : ℝ) ≤ (μ.iid (4 * s)).prob
      (fun draws => rank (adaptiveRun step (4 * s) initial draws) = 0) := by
  let ν := μ.iid (4 * s)
  let F : (Fin (4 * s) → Ω) → ℝ := fun draws =>
    adaptiveFailureCount step (rankFailure rank step) (4 * s) initial draws
  have hF : ∀ draws, 0 ≤ F draws := fun _ => Nat.cast_nonneg _
  have hexpected := adaptiveFailureCount_expectation_le μ step (rankFailure rank step)
    (1 / 4) (rankFailure_probability_le μ rank step hprogress) (4 * s) initial
  have hE : ν.expectation F ≤ (s : ℝ) := by
    convert hexpected using 1
    push_cast
    ring
  have ht : 0 < 3 * (s : ℝ) + 1 := by positivity
  have hsubset : ν.prob (fun draws => rank (adaptiveRun step (4 * s) initial draws) ≠ 0) ≤
      ν.prob (fun draws => 3 * (s : ℝ) + 1 ≤ F draws) := by
    apply ν.prob_mono
    intro draws hinc
    have h := adaptive_incomplete_many_failures rank step hstep s initial hinitial draws hinc
    dsimp [F]
    exact_mod_cast h
  have hMarkov := ν.prob_ge_le_expectation_div F hF ht
  have hbad : ν.prob (fun draws => rank (adaptiveRun step (4 * s) initial draws) ≠ 0) ≤
      (s : ℝ) / (3 * (s : ℝ) + 1) :=
    (hsubset.trans hMarkov).trans (div_le_div_of_nonneg_right hE ht.le)
  have hratio : (s : ℝ) / (3 * (s : ℝ) + 1) ≤ (1 / 3 : ℝ) := by
    apply (div_le_iff₀ ht).mpr
    linarith
  have hbad' := hbad.trans hratio
  have hcomplement := ν.prob_compl
    (fun draws => rank (adaptiveRun step (4 * s) initial draws) = 0)
  change (2 / 3 : ℝ) ≤ ν.prob (fun draws => rank (adaptiveRun step (4 * s) initial draws) = 0)
  linarith

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators


theorem solution.{u,v} : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.adaptive_rank_completion.{u,v} := @_root_.OAI.LeanBlast.SecondKahnKalai.adaptive_rank_completion.{u,v}
