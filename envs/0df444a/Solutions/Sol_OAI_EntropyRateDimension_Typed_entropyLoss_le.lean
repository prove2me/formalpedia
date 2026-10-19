-- Prove2me | solution 1 for OAI.EntropyRateDimension.Typed.entropyLoss_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:28:44.02372+00:00
-- url     : https://prove2.me/submissions/bd0b8921-6094-4fcd-9836-f2c0881e8327

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
universe uα uβ
open FiniteEntropy FairPairs FiniteCondition MeasureEntropy MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] [DecidableEq β]
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy in
theorem hn2_entropy_le_log_card {α : Type*} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hs : ∑ a ∈ s, p a = 1) :
    FiniteEntropy.entropy s p ≤ Real.log s.card := by
  have hne : s.Nonempty := by
    rcases s.eq_empty_or_nonempty with h | h
    · rw [h] at hs; simp at hs
    · exact h
  have hn : (0:ℝ) < s.card := by exact_mod_cast hne.card_pos
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := s) (w := fun _ => (s.card:ℝ)⁻¹) (p := p)
    (fun _ _ => by positivity) (by rw [Finset.sum_const, nsmul_eq_mul]; field_simp)
    (fun i hi => Set.mem_Ici.mpr (hp i hi))
  simp only [smul_eq_mul, ← Finset.mul_sum, hs, mul_one] at hJ
  unfold FiniteEntropy.entropy
  have e : Real.negMulLog (s.card:ℝ)⁻¹ = (s.card:ℝ)⁻¹ * Real.log s.card := by
    rw [Real.negMulLog, Real.log_inv]; ring
  rw [e] at hJ
  have := mul_le_mul_of_nonneg_left hJ hn.le
  rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul, one_mul] at this

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy in
theorem hn2_obsEnt_nonneg {α β : Type*} [DecidableEq β] (s : Finset α) (p : α → ℝ) (f : α → β)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hs : ∑ a ∈ s, p a = 1) : 0 ≤ observableEntropy s p f := by
  classical
  unfold observableEntropy FiniteEntropy.entropy
  apply Finset.sum_nonneg
  intro b _
  apply Real.negMulLog_nonneg (mass_nonneg s p f hp b)
  rw [← hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a ha _ => hp a ha)

omit [Fintype β] in
theorem solution (S : System α) (tag : α → β) {n : ℕ}
    (w : Fin n → α) (ρ : ℝ) :
    entropyLoss S tag w ρ ≤ (n : ℝ)*Real.log (Fintype.card α) := by
  classical
  unfold entropyLoss
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set ν := law S tag w with hν
  have hge : 0 ≤ ν.gridEntropy ρ := by
    unfold FairPairs.Law.gridEntropy
    exact div_nonneg (hn2_obsEnt_nonneg _ _ _ (fun x hx => (ν.prob_pos x hx).le) ν.prob_sum) hl2.le
  have hsh : ν.shannonEntropy * Real.log 2 ≤ Real.log ν.support.card := by
    unfold FairPairs.Law.shannonEntropy
    rw [div_mul_cancel₀ _ hl2.ne']
    exact hn2_entropy_le_log_card _ _ (fun x hx => (ν.prob_pos x hx).le) ν.prob_sum
  have hcard : ν.support.card ≤ Fintype.card α ^ n := by
    rw [hν]
    simp only [Typed.law, FiniteCondition.law, FairPairs.Law.ofObservable_support]
    refine Finset.card_image_le.trans ((Finset.card_le_univ _).trans ?_)
    simp
  have hpos : 0 < ν.support.card := by
    rcases ν.support.eq_empty_or_nonempty with h | h
    · have := ν.prob_sum; rw [h] at this; simp at this
    · exact h.card_pos
  have hlog : Real.log ν.support.card ≤ n * Real.log (Fintype.card α) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by exact_mod_cast hpos)
    exact_mod_cast hcard
  nlinarith

