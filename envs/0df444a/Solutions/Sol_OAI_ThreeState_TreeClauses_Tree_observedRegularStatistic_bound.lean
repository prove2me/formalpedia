-- Prove2me | solution 1 for OAI.ThreeState.TreeClauses.Tree.observedRegularStatistic_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:33:38.199798+00:00
-- url     : https://prove2.me/submissions/a3d2da8f-ee03-42aa-b8e7-571673d2d008

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThreeStateClauses/RegularStatistics.lean:L88-L100
-- (upload_full_project.md Phase 4): solution for node OAI.ThreeState.TreeClauses.Tree.observedRegularStatistic_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThreeStateTreeClauses
import Definitions.Def_OAI_Probability_ThreeStateClauses_RadialAlgebra
import Definitions.Def_OAI_Probability_ThreeStateClauses_PosteriorLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_DiscreteLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_Products
import Definitions.Def_OAI_Probability_ThreeStateClauses_Degradation
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularLaw
import Definitions.Def_OAI_Probability_ThreeStateClauses_BranchMoments
import Definitions.Def_OAI_Probability_ThreeStateClauses_CompactLimits
import Definitions.Def_OAI_Probability_ThreeStateClauses_RegularStatistics

-- ---- from OAI.Probability.ThreeStateClauses.RegularStatistics ----
namespace OAI

/-! Regular Statistics. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {α β : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

lemma spinScore_abs (i : Spin) : |spinScore i| ≤ 2 := by
  unfold spinScore; split_ifs <;> norm_num

lemma abs_multiset_sum_bound {α : Type*} (f : α → ℝ) (C : ℝ) (hf : ∀ a, |f a| ≤ C)
    (s : Multiset α) : |(s.map f).sum| ≤ (s.card:ℝ)*C := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
    exact (abs_add_le _ _).trans (by linarith [hf a])

lemma observedRegularStatistic_bound (b : ℕ) (lam : ℝ) (ℓ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ o, |observedRegularStatistic b lam ℓ o| ≤ C := by
  induction ℓ with
  | zero => exact ⟨2, by norm_num, spinScore_abs⟩
  | succ ℓ ih =>
    obtain ⟨C,hC,hbound⟩ := ih
    refine ⟨(b:ℝ)*C/|((b:ℝ)*lam)|, by positivity, ?_⟩
    intro s
    change |if s.card=b then _ else 0| ≤ _
    split_ifs with h
    · rw [abs_div]
      exact div_le_div_of_nonneg_right (by simpa only [h] using abs_multiset_sum_bound _ C hbound s) (abs_nonneg _)
    · simp only [abs_zero]; positivity

end ThreeState.TreeClauses.Tree

end

end OAI

-- ---- platform node ----
open OAI OAI.ThreeState OAI.ThreeState.TreeClauses OAI.ThreeState.TreeClauses.Tree
open scoped BigOperators ENNReal NNReal Topology
open Filter
open Set MeasureTheory
open scoped BigOperators
open ThreeState.TreeClauses.Experiment


theorem solution : type_of% @_root_.OAI.ThreeState.TreeClauses.Tree.observedRegularStatistic_bound := @_root_.OAI.ThreeState.TreeClauses.Tree.observedRegularStatistic_bound
