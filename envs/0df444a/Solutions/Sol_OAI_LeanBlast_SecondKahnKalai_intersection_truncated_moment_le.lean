-- Prove2me | solution 1 for OAI.LeanBlast.SecondKahnKalai.intersection_truncated_moment_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:53:10.899165+00:00
-- url     : https://prove2.me/submissions/2d6e8ff7-83b2-4c1b-a53a-2ed97052fc7c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GraphThreshold/SpreadCounting.lean:L139-L157
-- (upload_full_project.md Phase 4): solution for node OAI.LeanBlast.SecondKahnKalai.intersection_truncated_moment_le. The node keeps its source
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
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_expectation_intersection_eq_sum
import Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_intersection_card_ge_le_subsets

-- ---- from OAI.Combinatorics.GraphThreshold.SpreadCounting ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! Exact intersection counting for a finite, weighted spread family.

No injectivity of the label map and no strict positivity of individual weights
is required. The fixed target is an arbitrary finite set, and may be empty.
-/

noncomputable section

open scoped BigOperators

namespace LeanBlast.SecondKahnKalai

variable {X B : Type*} [DecidableEq X] [Fintype B]

/-- The spread bound also holds for the empty test set, by normalization. -/
theorem IsSpread.containment_le {μ : FiniteLaw B} {A : B → Finset X} {a : ℝ}
    (hs : IsSpread μ A a) (J : Finset X) :
    μ.prob (fun c => J ⊆ A c) ≤ a ^ J.card := by
  classical
  by_cases hJ : J.Nonempty
  · exact hs J hJ
  · have hJ' : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
    simp [hJ', FiniteLaw.prob, μ.total]

/-- Exact binomial count of potential witnesses bounds the intersection tail. -/
theorem intersection_card_ge_le_target {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (T : Finset X) (r : ℕ) :
    μ.prob (fun c => r ≤ (A c ∩ T).card) ≤
      (T.card.choose r : ℝ) * a ^ r := by
  classical
  calc
    μ.prob (fun c => r ≤ (A c ∩ T).card) ≤
        ∑ J ∈ T.powersetCard r, μ.prob (fun c => J ⊆ A c) :=
      intersection_card_ge_le_subsets μ A T r
    _ ≤ ∑ J ∈ T.powersetCard r, a ^ r := by
      apply Finset.sum_le_sum
      intro J hJ
      simpa [(Finset.mem_powersetCard.mp hJ).2] using hs.containment_le J
    _ = (T.card.choose r : ℝ) * a ^ r := by simp

/-- Uniform capacity version, including `r = 0` and empty target sets. -/
theorem intersection_card_ge_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) (r : ℕ) :
    μ.prob (fun c => r ≤ (A c ∩ T).card) ≤
      (m.choose r : ℝ) * a ^ r := by
  apply (intersection_card_ge_le_target hs T r).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha r)
  exact_mod_cast Nat.choose_le_choose r hT

/-- The exact intersection histogram is bounded by the same binomial count. -/
theorem intersection_card_eq_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) (r : ℕ) :
    μ.prob (fun c => (A c ∩ T).card = r) ≤
      (m.choose r : ℝ) * a ^ r := by
  classical
  apply le_trans _ (intersection_card_ge_le hs ha hT r)
  unfold FiniteLaw.prob
  apply Finset.sum_le_sum
  intro c hc
  by_cases hcr : (A c ∩ T).card = r
  · simp [hcr]
  · simp only [ite_eq_right hcr]
    split_ifs <;> first | exact μ.nonneg c | exact le_rfl

/-- Any nonnegative function of the intersection admits a binomial majorant. -/
theorem expectation_intersection_le_binomial {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) (g : ℕ → ℝ) (hg : ∀ r, 0 ≤ g r) :
    μ.expectation (fun c => g (A c ∩ T).card) ≤
      ∑ r ∈ Finset.range (m + 1), (m.choose r : ℝ) * a ^ r * g r := by
  rw [expectation_intersection_eq_sum μ A hT g]
  exact Finset.sum_le_sum fun r _ =>
    mul_le_mul_of_nonneg_right (intersection_card_eq_le hs ha hT r) (hg r)

/-- A predicate can truncate the intersection generating function arbitrarily. -/
theorem intersection_truncated_moment_le {μ : FiniteLaw B} {A : B → Finset X}
    {a : ℝ} (hs : IsSpread μ A a) (ha : 0 ≤ a) {m : ℕ}
    {T : Finset X} (hT : T.card ≤ m) {t : ℝ} (ht : 0 ≤ t)
    (Q : ℕ → Prop) [DecidablePred Q] :
    μ.expectation (fun c => if Q (A c ∩ T).card then t ^ (A c ∩ T).card else 0) ≤
      ∑ r ∈ Finset.range (m + 1),
        if Q r then (m.choose r : ℝ) * (a * t) ^ r else 0 := by
  calc
    _ ≤ ∑ r ∈ Finset.range (m + 1),
        (m.choose r : ℝ) * a ^ r * (if Q r then t ^ r else 0) := by
      apply expectation_intersection_le_binomial hs ha hT
        (fun r => if Q r then t ^ r else 0)
      intro r
      split_ifs <;> first | exact pow_nonneg ht r | exact le_rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hQ : Q r <;> simp [hQ, mul_pow, mul_assoc]

end LeanBlast.SecondKahnKalai

end

end OAI

-- ---- platform node ----
open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.LeanBlast.SecondKahnKalai.intersection_truncated_moment_le := @_root_.OAI.LeanBlast.SecondKahnKalai.intersection_truncated_moment_le
