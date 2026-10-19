-- Prove2me | solution 1 for OAI.EntropyRateDimension.MeasureEntropy.random_observation_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:05:37.382989+00:00
-- url     : https://prove2.me/submissions/bcbef1cc-f11f-43ee-8321-eb65fcfc08f9

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
universe uα uβ uX
open MeasureTheory
open scoped BigOperators ENNReal
theorem h41n_oe_bound {α : Type*} [Fintype α] (p : α → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (z : α → ℤ) :
    |FiniteEntropy.observableEntropy Finset.univ p z| ≤ Fintype.card α := by
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  have hm : ∀ b, 0 ≤ FiniteEntropy.mass Finset.univ p z b ∧
      FiniteEntropy.mass Finset.univ p z b ≤ 1 := by
    intro b
    refine ⟨FiniteEntropy.mass_nonneg _ _ _ (fun a _ => hp a) b, ?_⟩
    rw [← hp1]
    unfold FiniteEntropy.mass
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun a _ _ => hp a)
  rw [abs_of_nonneg (Finset.sum_nonneg fun b _ => Real.negMulLog_nonneg (hm b).1 (hm b).2)]
  calc _ ≤ ∑ b ∈ Finset.univ.image z, (1:ℝ) :=
        Finset.sum_le_sum fun b _ =>
          (Real.negMulLog_le_one_sub_self (hm b).1).trans (by linarith [(hm b).1])
    _ = ((Finset.univ.image z).card : ℝ) := by simp
    _ ≤ Fintype.card α := by
        exact_mod_cast Finset.card_image_le.trans (by simp)

theorem solution {X : Type uX} {α : Type uα} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (f : α → X → ℤ) (hf : ∀ i, Measurable (f i)) (s : Finset ℤ)
    (hs : ∀ i, ∀ᵐ y ∂μ, f i y ∈ s) :
    Integrable (fun y => FiniteEntropy.observableEntropy Finset.univ p (fun i => f i y)) μ := by
  have hmeas : Measurable (fun y => fun i => f i y) := measurable_pi_lambda _ hf
  have hG : Measurable (fun z : α → ℤ => FiniteEntropy.observableEntropy Finset.univ p z) :=
    measurable_of_countable _
  apply Integrable.of_bound (hG.comp hmeas).aestronglyMeasurable (Fintype.card α)
  exact Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]; exact h41n_oe_bound p hp hp1 _

