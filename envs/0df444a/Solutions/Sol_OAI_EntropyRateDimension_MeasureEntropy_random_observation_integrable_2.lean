-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.random_observation_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:36:18.605963+00:00
-- url     : https://prove2.me/submissions/3eaa9ae7-98a6-4002-a1ef-424780a8f8e7

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/KernelEntropy.lean:L96-L124
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.random_observation_integrable. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem observableEntropy_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) : observableEntropy s p f = entropy t (mass s p f) := by
  classical
  apply Finset.sum_subset
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hf a ha
  · intro b _ hb
    rw [mass_eq_zero_of_not_mem s p f hb, Real.negMulLog_zero]

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.KernelEntropy ----
namespace OAI

universe uα uβ uX

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal

theorem random_observation_integrable {X : Type uX} {α : Type uα} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (f : α → X → ℤ) (hf : ∀ i, Measurable (f i)) (s : Finset ℤ)
    (hs : ∀ i, ∀ᵐ y ∂μ, f i y ∈ s) :
    Integrable (fun y => FiniteEntropy.observableEntropy Finset.univ p (fun i => f i y)) μ := by
  classical
  let K : X → ℤ → ℝ := fun y b => FiniteEntropy.mass Finset.univ p (fun i => f i y) b
  have hk (y : X) (b : ℤ) : K y b=∑ i, if f i y=b then p i else 0 := by
    simp only [K,FiniteEntropy.mass,Finset.sum_filter]
  have hmK (b : ℤ) : Measurable (fun y => K y b) := by
    simp_rw [hk]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.ite
      (measurableSet_eq_fun (hf i) measurable_const) measurable_const)
  have hpK (y : X) (b : ℤ) : 0 ≤ K y b ∧ K y b ≤ 1 := by
    refine ⟨FiniteEntropy.mass_nonneg _ _ _ (fun i _ => hp i) _,?_⟩
    change (∑ i ∈ Finset.univ.filter (fun i => f i y=b), p i) ≤ 1
    rw [← hp1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hp i)
  have hi (b : ℤ) : Integrable (fun y => Real.negMulLog (K y b)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (Real.continuous_negMulLog.measurable.comp (hmK b)).aestronglyMeasurable
    filter_upwards [] with y
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.negMulLog_nonneg (hpK y b).1 (hpK y b).2)]
    exact (Real.negMulLog_le_one_sub_self (hpK y b).1).trans (sub_le_self _ (hpK y b).1)
  apply (integrable_finsetSum s (fun b _ => hi b)).congr
  filter_upwards [ae_all_iff.mpr hs] with y hy
  exact (FiniteEntropy.observableEntropy_on_superset Finset.univ s p _ (fun i _ => hy i)).symm

end EntropyRateDimension.MeasureEntropy

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal


theorem solution.{uα,uX} : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.random_observation_integrable.{uα,uX} := @_root_.OAI.EntropyRateDimension.MeasureEntropy.random_observation_integrable.{uα,uX}
