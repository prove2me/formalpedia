-- Prove2me | solution 2 for OAI.EntropyRateDimension.Typed.entropyLoss_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:44:10.922255+00:00
-- url     : https://prove2.me/submissions/0544d58c-7656-472c-bee1-26b0590b4eba

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/EntropyBudget.lean:L55-L88
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.entropyLoss_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget
import Theorems.Thm_OAI_EntropyRateDimension_FiniteEntropy_entropy_le_log_card

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem negMulLog_sum_le {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    Real.negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, Real.negMulLog (p i) := by
  have hterm : ∀ i ∈ s,
      -(p i) * Real.log (∑ j ∈ s, p j) ≤ Real.negMulLog (p i) := by
    intro i hi
    rcases eq_or_lt_of_le (hp i hi) with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonpos_left
        (Real.log_le_log h (Finset.single_le_sum hp hi)) (neg_nonpos.mpr (hp i hi))
  have heq : (∑ i ∈ s, -(p i) * Real.log (∑ j ∈ s, p j)) =
      Real.negMulLog (∑ i ∈ s, p i) := by
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    rfl
  rw [← heq]
  exact Finset.sum_le_sum hterm

theorem observableEntropy_le {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p f ≤ entropy s p := by
  classical
  calc
    observableEntropy s p f ≤
        ∑ b ∈ s.image f, ∑ a ∈ s.filter (fun a => f a = b), Real.negMulLog (p a) := by
      apply Finset.sum_le_sum
      intro b _
      exact negMulLog_sum_le _ _ (fun a ha => hp a (Finset.mem_filter.mp ha).1)
    _ = entropy s p :=
      Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _

theorem entropy_nonneg {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∀ a ∈ s, p a ≤ 1) : 0 ≤ entropy s p :=
  Finset.sum_nonneg (fun a ha => Real.negMulLog_nonneg (hp a ha) (hp1 a ha))

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.EntropyBudget ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open FiniteEntropy FairPairs FiniteCondition MeasureEntropy MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] [DecidableEq β]

omit [Fintype β] in
theorem entropyLoss_le (S : System α) (tag : α → β) {n : ℕ}
    (w : Fin n → α) (ρ : ℝ) :
    entropyLoss S tag w ρ ≤ (n : ℝ)*Real.log (Fintype.card α) := by
  classical
  let p := fun v : Fin n → α => S.wordWeight v / FiniteCondition.mass S.wordWeight (tagWord tag) w
  let s := fiber (tagWord tag) w
  have hp : ∀ v ∈ s, 0 ≤ p v := fun v _ =>
    (div_pos (S.wordWeight_pos v) (mass_pos S.wordWeight S.wordWeight_pos (tagWord tag) w)).le
  have hp1 : ∑ v ∈ s, p v=1 := fiber_normalized_sum S.wordWeight S.wordWeight_pos (tagWord tag) w
  have hle := (observableEntropy_le s p (fun v => (S.completeMap v).2) hp).trans
    (entropy_le_log_card s p hp hp1)
  have hs : (0 : ℝ)<s.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨w,by simp [s,fiber]⟩
  have ht : (s.card : ℝ) ≤ (Fintype.card α : ℝ)^n := by
    have hc := Finset.card_le_card (Finset.subset_univ s)
    simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using
      (show (s.card : ℝ) ≤ (Finset.card (Finset.univ : Finset (Fin n → α)) : ℝ) by exact_mod_cast hc)
  have hlog := Real.log_le_log hs ht
  rw [Real.log_pow] at hlog
  let f := fun v : Fin n → α => ⌊(S.completeMap v).2/ρ⌋
  have hm : ∀ b, 0 ≤ FiniteEntropy.mass s p f b := FiniteEntropy.mass_nonneg s p f hp
  have hnon : 0 ≤ observableEntropy s p f := by
    apply FiniteEntropy.entropy_nonneg _ _ (fun b _ => hm b)
    intro b hb
    exact (Finset.single_le_sum (fun c _ => hm c) hb).trans_eq
      ((FiniteEntropy.mass_sum s p f).trans hp1)
  dsimp only [entropyLoss,law,FiniteCondition.law]
  rw [Law.ofObservable_entropy,Law.ofObservable_gridEntropy]
  have hl : Real.log 2≠0 := (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne'
  change (observableEntropy s p (fun v => (S.completeMap v).2)/Real.log 2-
    observableEntropy s p (fun v => ⌊(S.completeMap v).2/ρ⌋)/Real.log 2)*Real.log 2 ≤ _
  field_simp
  linarith

end EntropyRateDimension.Typed

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open FiniteEntropy FairPairs FiniteCondition MeasureEntropy MeasureTheory
open scoped BigOperators ENNReal


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.Typed.entropyLoss_le.{uα,uβ} := @_root_.OAI.EntropyRateDimension.Typed.entropyLoss_le.{uα,uβ}
