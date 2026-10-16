-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.local_failure_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:05:53.70129+00:00
-- url     : https://prove2.me/submissions/e957805c-bb99-4a62-854e-c3c37da6f730

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/LocalFailure.lean:L250-L285
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.local_failure_bound. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction
import Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_local_failure_exponential_combine
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_resampling_large_fragment_bound
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_resampling_small_density_bound

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

theorem prob_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) :
    μ.prob P ≤ μ.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω
  · simp [hp, hPQ ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg ω]

theorem prob_union_le (μ : FiniteLaw Ω) (P Q : Ω → Prop) :
    μ.prob (fun ω => P ω ∨ Q ω) ≤ μ.prob P + μ.prob Q := by
  classical
  rw [prob, prob, prob, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg]

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.ResamplingEvents ----
namespace OAI

/-! # Success and failure of a local resampling transition -/

noncomputable section

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

theorem localFailure_iff (ν : FiniteLaw B) (A : B → Finset X) (ρ : ℝ) (m : ℕ)
    (W : Finset X) (c b : B) :
    LocalFailure ν A ρ m W c b ↔
      resamplingZ ν A ρ (W ∪ A c) < Real.exp (-10 * (m : ℝ)) ∨
        m / 2 < (A b \ W).card := by
  simp only [LocalFailure, LocalSuccess, not_and_or, not_le]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.LocalFailure ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! # Local failure of the actual resampling experiment -/

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B]

theorem local_failure_bound (ν : FiniteLaw B) (A : B → Finset X)
    {ρ a : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (m : ℕ) (hm : 1 ≤ m) (hsize : ∀ b, (A b).card ≤ m)
    (hspread : IsSpread ν A a) (ha : 0 ≤ a) (hratio : a / ρ ≤ Real.exp (-50)) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob
      (fun cb => LocalFailure ν A ρ m W cb.1 cb.2)) ≤ Real.exp (-9 * (m : ℝ)) := by
  classical
  let μ : FiniteLaw (Finset X) := bernoulliLaw ρ hρ.le hρ1.le
  let low (W : Finset X) (cb : B × B) : Prop :=
    resamplingZ ν A ρ (resamplingY A W cb.1) < Real.exp (-10 * (m : ℝ))
  let big (W : Finset X) (cb : B × B) : Prop :=
    Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W cb.1) ∧
      m / 2 < (A cb.2 \ W).card
  have hpoint (W : Finset X) :
      (resamplingLaw ν A ρ W hν hρ).prob (fun cb => LocalFailure ν A ρ m W cb.1 cb.2) ≤
      (resamplingLaw ν A ρ W hν hρ).prob (low W) +
        (resamplingLaw ν A ρ W hν hρ).prob (big W) := by
    apply le_trans ((resamplingLaw ν A ρ W hν hρ).prob_mono (Q := fun cb => low W cb ∨ big W cb) ?_)
      ((resamplingLaw ν A ρ W hν hρ).prob_union_le (low W) (big W))
    intro cb hcb
    rcases (localFailure_iff ν A ρ m W cb.1 cb.2).mp hcb with hlow | hfrag
    · exact Or.inl hlow
    · by_cases hl : low W cb
      · exact Or.inl hl
      · exact Or.inr ⟨le_of_not_gt hl, hfrag⟩
  calc
    _ ≤ μ.expectation (fun W => (resamplingLaw ν A ρ W hν hρ).prob (low W) +
        (resamplingLaw ν A ρ W hν hρ).prob (big W)) := μ.expectation_mono hpoint
    _ = μ.expectation (fun W => (resamplingLaw ν A ρ W hν hρ).prob (low W)) +
        μ.expectation (fun W => (resamplingLaw ν A ρ W hν hρ).prob (big W)) :=
      μ.expectation_add _ _
    _ ≤ Real.exp (-10 * (m : ℝ)) +
        Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) :=
      add_le_add (resampling_small_density_bound ν A hν hρ hρ1 (Real.exp_pos _).le)
        (resampling_large_fragment_bound ν A hν hρ hρ1 m hsize hspread ha hratio)
    _ ≤ Real.exp (-9 * (m : ℝ)) := local_failure_exponential_combine hm

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.local_failure_bound := @_root_.OAI.LeanBlast.SecondKahnKalai.local_failure_bound
