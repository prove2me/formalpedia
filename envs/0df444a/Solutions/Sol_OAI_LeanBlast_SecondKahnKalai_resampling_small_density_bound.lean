-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.resampling_small_density_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:04:39.72731+00:00
-- url     : https://prove2.me/submissions/f904d0f4-26b4-4c58-b228-14b54a38642e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/LocalFailure.lean:L231-L248
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.resampling_small_density_bound. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_pushforward
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliExpectation_resamplingZ

-- ---- from OAI.Combinatorics.GraphThreshold.FiniteProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

theorem prob_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob P = μ.expectation (fun ω => if P ω then 1 else 0) := by
  classical
  simp [prob, expectation, mul_ite]

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.BernoulliCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem finset_eq_indicator_product (U V : Finset X) :
    (if U = V then (1 : ℝ) else 0) =
      ∏ x, if (x ∈ U ↔ x ∈ V) then (1 : ℝ) else 0 := by
  rw [Fintype.prod_boole]
  have h : (∀ x : X, x ∈ U ↔ x ∈ V) ↔ U = V :=
    ⟨Finset.ext, fun h => by subst V; simp⟩
  simp only [h]

theorem bernoulli_union_fixed_mass (p : ℝ) (A Y : Finset X) :
    bernoulliExpectation p (fun W => if W ∪ A = Y then 1 else 0) =
      ∏ x, if x ∈ A then (if x ∈ Y then (1 : ℝ) else 0)
        else (if x ∈ Y then p else 1 - p) := by
  let f : X → Bool → ℝ := fun x b =>
    if (b = true ∨ x ∈ A) ↔ x ∈ Y then 1 else 0
  have hf : (fun W : Finset X => if W ∪ A = Y then (1 : ℝ) else 0) =
      (fun W => ∏ x, f x (decide (x ∈ W))) := by
    funext W
    simpa [f] using finset_eq_indicator_product (W ∪ A) Y
  rw [hf, bernoulliExpectation_product]
  apply Finset.prod_congr rfl
  intro x _
  by_cases ha : x ∈ A <;> by_cases hy : x ∈ Y <;> simp [f, ha, hy]

theorem bernoulli_union_fixed_mass_mul (p : ℝ) (A Y : Finset X) :
    p ^ A.card * bernoulliExpectation p (fun W => if W ∪ A = Y then 1 else 0) =
      if A ⊆ Y then bernoulliWeight p Y else 0 := by
  rw [bernoulli_union_fixed_mass]
  by_cases hAY : A ⊆ Y
  · rw [ite_eq_left hAY]
    have hp : p ^ A.card = ∏ x : X, if x ∈ A then p else 1 := by
      rw [Fintype.prod_ite_mem]
      simp
    rw [hp, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro x _
    by_cases ha : x ∈ A
    · simp [ha, hAY ha]
    · simp [ha]
  · rw [ite_eq_right hAY]
    obtain ⟨x, hxa, hxy⟩ := Finset.not_subset.mp hAY
    have hz : (∏ x, if x ∈ A then (if x ∈ Y then (1 : ℝ) else 0)
        else (if x ∈ Y then p else 1 - p)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ x)
      simp [hxa, hxy]
    rw [hz, mul_zero]

theorem bernoulli_union_fixed_mass_div (p : ℝ) (hp : p ≠ 0) (A Y : Finset X) :
    bernoulliExpectation p (fun W => if W ∪ A = Y then 1 else 0) =
      (if A ⊆ Y then bernoulliWeight p Y else 0) / p ^ A.card := by
  apply (eq_div_iff (pow_ne_zero _ hp)).2
  simpa only [mul_comm] using bernoulli_union_fixed_mass_mul p A Y

/-- Forcing all coordinates of `A` to be present gives the literal Bernoulli
law conditioned on containing `A`. -/
theorem bernoulliExpectation_union_fixed (p : ℝ) (hp : p ≠ 0)
    (A : Finset X) (F : Finset X → ℝ) :
    bernoulliExpectation p (fun W => F (W ∪ A)) =
      bernoulliExpectation p (fun Y => if A ⊆ Y then F Y / p ^ A.card else 0) := by
  rw [bernoulliExpectation_pushforward]
  unfold bernoulliExpectation
  apply Finset.sum_congr rfl
  intro Y _
  rw [← bernoulliExpectation, bernoulli_union_fixed_mass_div p hp A Y]
  by_cases hAY : A ⊆ Y <;> simp [hAY]
  ring

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.Resampling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

theorem resampling_expectation_source (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (W : Finset X) (f : B → ℝ) :
    (resamplingLaw ν A ρ W hν hρ).expectation (fun cb => f cb.1) = ν.expectation f := by
  simp only [FiniteLaw.expectation, resamplingLaw_weight, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_mul, resampling_source_marginal ν A hν hρ W c]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.ResamplingDensity ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

attribute [local instance] Classical.propDecidable

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B]

/-- Mixture expansion before using the Bernoulli union identity. -/
theorem bernoulliExpectation_resampling_source (ν : FiniteLaw B) (A : B → Finset X)
    (ρ : ℝ) (F : Finset X → ℝ) :
    bernoulliExpectation ρ (fun W => ν.expectation (fun c => F (resamplingY A W c))) =
      ∑ c, ν.weight c * bernoulliExpectation ρ (fun W => F (W ∪ A c)) := by
  simp only [bernoulliExpectation, FiniteLaw.expectation, resamplingY, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro W _
  ring_nf

theorem resampling_source_density (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : ρ ≠ 0) (F : Finset X → ℝ) :
    bernoulliExpectation ρ (fun W => ν.expectation (fun c => F (resamplingY A W c))) =
      bernoulliExpectation ρ (fun Y => resamplingZ ν A ρ Y * F Y) := by
  rw [bernoulliExpectation_resampling_source, bernoulliExpectation_resamplingZ]
  apply Finset.sum_congr rfl
  intro c _
  rw [bernoulliExpectation_union_fixed ρ hρ]

theorem resampling_density (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (F : Finset X → ℝ) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).expectation
      (fun cb => F (resamplingY A W cb.1))) =
      bernoulliExpectation ρ (fun Y => resamplingZ ν A ρ Y * F Y) := by
  calc
    _ = bernoulliExpectation ρ (fun W => ν.expectation
        (fun c => F (resamplingY A W c))) := by
      unfold bernoulliExpectation
      apply Finset.sum_congr rfl
      intro W _
      exact congrArg (fun x => bernoulliWeight ρ W * x)
        (resampling_expectation_source ν A hν hρ W (fun c => F (resamplingY A W c)))
    _ = _ := resampling_source_density ν A hρ.ne' F

/-- Event form of the observed-set density formula, used for small-`Z`
failure events in the actual resampling procedure. -/
theorem resampling_density_prob (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (P : Finset X → Prop) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob
      (fun cb => P (resamplingY A W cb.1))) =
      bernoulliExpectation ρ (fun Y => if P Y then resamplingZ ν A ρ Y else 0) := by
  classical
  simpa only [FiniteLaw.prob_eq_expectation, mul_ite, mul_one, mul_zero] using
    resampling_density ν A hν hρ (fun Y => if P Y then 1 else 0)

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

/-- The density identity bounds the probability of a small denominator by
the cutoff itself. -/
theorem resampling_small_density_bound (ν : FiniteLaw B) (A : B → Finset X)
    {ρ τ : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ < 1) (hτ : 0 ≤ τ) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob
      (fun cb => resamplingZ ν A ρ (resamplingY A W cb.1) < τ)) ≤ τ := by
  classical
  rw [resampling_density_prob ν A hν hρ (fun Y => resamplingZ ν A ρ Y < τ)]
  let μ : FiniteLaw (Finset X) := bernoulliLaw ρ hρ.le hρ1.le
  change μ.expectation _ ≤ τ
  calc
    _ ≤ μ.expectation (fun _ => τ) := by
      apply μ.expectation_mono
      intro Y
      split_ifs with hY
      · exact hY.le
      · exact hτ
    _ = τ := μ.expectation_const τ

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.resampling_small_density_bound := @_root_.OAI.LeanBlast.SecondKahnKalai.resampling_small_density_bound
