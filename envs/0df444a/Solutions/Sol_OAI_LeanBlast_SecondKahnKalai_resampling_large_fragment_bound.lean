-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:03:37.27629+00:00
-- url     : https://prove2.me/submissions/4aa4c708-2469-4f9c-b1b4-ae0542057893

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/LocalFailure.lean:L167-L229
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_bound. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_bernoulliProbability_subset
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_intersection_truncated_moment_le
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_largeIntersectionTail_le
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_resampling_large_fragment_term_le

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

end FiniteLaw

variable {X : Type*} [Fintype X] [DecidableEq X]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.SpreadCounting ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Exact intersection counting for a finite, weighted spread family.

No injectivity of the label map and no strict positivity of individual weights
is required. The fixed target is an arbitrary finite set, and may be empty.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

/-- Raw-sum form of the truncated moment estimate. -/
theorem intersection_truncated_sum_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {t : ℝ} (ht : 0 ≤ t)
    (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ c, if Q (A c ∩ T).card then μ.weight c * t ^ (A c ∩ T).card else 0) ≤
      ∑ r ∈ Finset.range (m + 1),
        if Q r then (m.choose r : ℝ) * (a * t) ^ r else 0 := by
  simpa only [FiniteLaw.expectation, mul_ite, mul_zero] using
    intersection_truncated_moment_le hs ha hT ht Q

/-- Inverse-parameter truncated moment, retaining an arbitrary tail predicate. -/
theorem intersection_inverse_truncated_sum_le
    {μ : FiniteLaw B} {A : B → Finset X} {a : ℝ}
    (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {ρ : ℝ} (hρ : 0 < ρ)
    (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ c, if Q (A c ∩ T).card then μ.weight c * (ρ⁻¹) ^ (A c ∩ T).card else 0) ≤
      ∑ r ∈ Finset.range (m + 1),
        if Q r then (m.choose r : ℝ) * (a / ρ) ^ r else 0 := by
  simpa only [div_eq_mul_inv] using
    intersection_truncated_sum_le hs ha hT (inv_nonneg.mpr hρ.le) Q

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- from OAI.Combinatorics.GraphThreshold.LocalFailure ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! # Local failure of the actual resampling experiment -/

noncomputable section

open Finset

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [Fintype X] [DecidableEq X] [Fintype B]

omit [Fintype X] [Fintype B] in
private theorem inverse_power_card_cancel (A : B → Finset X) {ρ : ℝ}
    (hρ : 0 < ρ) (c b : B) :
    (ρ⁻¹) ^ (A b).card * ρ ^ (A b \ A c).card =
      (ρ⁻¹) ^ (A c ∩ A b).card := by
  have hc : (A b).card = (A b \ A c).card + (A c ∩ A b).card := by
    simpa only [Finset.inter_comm] using (Finset.card_sdiff_add_card_inter (A b) (A c)).symm
  rw [hc, pow_add]
  calc
    ((ρ⁻¹) ^ (A b \ A c).card * (ρ⁻¹) ^ (A c ∩ A b).card) *
        ρ ^ (A b \ A c).card =
      ((ρ⁻¹) ^ (A b \ A c).card * ρ ^ (A b \ A c).card) *
        (ρ⁻¹) ^ (A c ∩ A b).card := by ring
    _ = (ρ⁻¹) ^ (A c ∩ A b).card := by simp [inv_pow, hρ.ne']

private theorem local_bernoulliExpectation_sum {ι : Type*} [Fintype ι]
    (ρ : ℝ) (f : ι → Finset X → ℝ) :
    bernoulliExpectation ρ (fun W => ∑ i, f i W) =
      ∑ i, bernoulliExpectation ρ (f i) := by
  simp only [bernoulliExpectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem resampling_large_fragment_pair_bound (ν : FiniteLaw B) (A : B → Finset X)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) (c b : B) :
    bernoulliExpectation ρ (fun W =>
      if Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W c) ∧
          m / 2 < (A b \ W).card then resamplingWeight ν A ρ W (c, b) else 0) ≤
      if m < 2 * (A c ∩ A b).card then
        Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b * (ρ⁻¹) ^ (A c ∩ A b).card
      else 0 := by
  classical
  let μ : FiniteLaw (Finset X) := bernoulliLaw ρ hρ.le hρ1.le
  by_cases hlarge : m < 2 * (A c ∩ A b).card
  · rw [ite_eq_left hlarge]
    calc
      _ ≤ μ.expectation (fun W =>
          (Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b * (ρ⁻¹) ^ (A b).card) *
            (if A b \ A c ⊆ W then 1 else 0)) := by
        apply μ.expectation_mono
        intro W
        simpa only [hlarge, true_and, mul_ite, mul_one, mul_zero] using
          resampling_large_fragment_term_le ν A hρ m W c b
      _ = (Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b * (ρ⁻¹) ^ (A b).card) *
          ρ ^ (A b \ A c).card := by
        rw [FiniteLaw.expectation_smul]
        congr 1
        change bernoulliExpectation ρ (fun W => if A b \ A c ⊆ W then 1 else 0) = _
        rw [← bernoulliProbability_subset ρ (A b \ A c)]
        simp only [bernoulliExpectation, bernoulliProbability, mul_ite, mul_one, mul_zero]
        apply Finset.sum_congr rfl
        intro W _
        by_cases hW : A b \ A c ⊆ W <;> simp [hW]
      _ = Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b *
          ((ρ⁻¹) ^ (A b).card * ρ ^ (A b \ A c).card) := by ring
      _ = _ := by rw [inverse_power_card_cancel A hρ c b]
  · rw [ite_eq_right hlarge]
    calc
      _ ≤ μ.expectation (fun _ => 0) := by
        apply μ.expectation_mono
        intro W
        simpa only [hlarge, false_and, ite_false] using
          resampling_large_fragment_term_le ν A hρ m W c b
      _ = 0 := μ.expectation_const 0

theorem resampling_large_fragment_bound (ν : FiniteLaw B) (A : B → Finset X)
    {ρ a : ℝ} (hν : ν.IsPositive) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (m : ℕ) (hsize : ∀ b, (A b).card ≤ m) (hspread : IsSpread ν A a)
    (ha : 0 ≤ a) (hratio : a / ρ ≤ Real.exp (-50)) :
    bernoulliExpectation ρ (fun W => (resamplingLaw ν A ρ W hν hρ).prob
      (fun cb => Real.exp (-10 * (m : ℝ)) ≤
          resamplingZ ν A ρ (resamplingY A W cb.1) ∧
        m / 2 < (A cb.2 \ W).card)) ≤
      Real.exp (10 * (m : ℝ)) * (2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ)) := by
  classical
  have hpair (b : B) :
      (∑ c, bernoulliExpectation ρ (fun W =>
        if Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W c) ∧
            m / 2 < (A b \ W).card then resamplingWeight ν A ρ W (c, b) else 0)) ≤
      (Real.exp (10 * (m : ℝ)) * ν.weight b) * largeIntersectionTail m (a / ρ) := by
    calc
      _ ≤ ∑ c, if m < 2 * (A c ∩ A b).card then
          Real.exp (10 * (m : ℝ)) * ν.weight c * ν.weight b *
            (ρ⁻¹) ^ (A c ∩ A b).card else 0 := by
        apply Finset.sum_le_sum
        intro c _
        exact resampling_large_fragment_pair_bound ν A hρ hρ1 m c b
      _ = (Real.exp (10 * (m : ℝ)) * ν.weight b) *
          ∑ c, if m < 2 * (A c ∩ A b).card then
            ν.weight c * (ρ⁻¹) ^ (A c ∩ A b).card else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        split_ifs <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (intersection_inverse_truncated_sum_le hspread ha (hsize b) hρ
          (fun r => m < 2 * r))
        (mul_nonneg (Real.exp_pos _).le (ν.nonneg b))
  calc
    _ = ∑ b, ∑ c, bernoulliExpectation ρ (fun W =>
        if Real.exp (-10 * (m : ℝ)) ≤ resamplingZ ν A ρ (resamplingY A W c) ∧
            m / 2 < (A b \ W).card then resamplingWeight ν A ρ W (c, b) else 0) := by
      simp only [FiniteLaw.prob, resamplingLaw_weight, Fintype.sum_prod_type]
      conv_lhs => arg 2; ext W; rw [Finset.sum_comm]
      rw [local_bernoulliExpectation_sum]
      simp_rw [local_bernoulliExpectation_sum]
      apply Finset.sum_congr rfl
      intro target _
      apply Finset.sum_congr rfl
      intro source _
      congr 1
      funext drawn
      split_ifs <;> rfl
    _ ≤ ∑ b, (Real.exp (10 * (m : ℝ)) * ν.weight b) * largeIntersectionTail m (a / ρ) :=
      Finset.sum_le_sum (fun b _ => hpair b)
    _ = Real.exp (10 * (m : ℝ)) * largeIntersectionTail m (a / ρ) := by
      calc
        _ = (Real.exp (10 * (m : ℝ)) * largeIntersectionTail m (a / ρ)) *
            ∑ b, ν.weight b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by rw [ν.total, mul_one]
    _ ≤ Real.exp (10 * (m : ℝ)) * ((2 : ℝ) ^ m * Real.exp (-25 * (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (largeIntersectionTail_le (div_nonneg ha hρ.le) hratio)
        (Real.exp_pos _).le
    _ = _ := by ring

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_bound := @_root_.OAI.LeanBlast.SecondKahnKalai.resampling_large_fragment_bound
