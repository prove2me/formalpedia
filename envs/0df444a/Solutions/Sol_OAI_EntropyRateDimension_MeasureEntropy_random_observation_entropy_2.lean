-- Prove2me | solution 2 for OAI.EntropyRateDimension.MeasureEntropy.random_observation_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:34:39.939801+00:00
-- url     : https://prove2.me/submissions/7c5b4bae-055a-4e8c-a0e6-4a3a061c23e5

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/KernelEntropy.lean:L33-L94
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.MeasureEntropy.random_observation_entropy. The node keeps its source
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

-- ---- from OAI.MeasureTheory.SelfSimilar.MeasureEntropy ----
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

theorem entropy_eq_sum {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f = ∑ b ∈ s, Real.negMulLog (mass μ f b) := by
  apply tsum_eq_sum
  intro b hb
  rw [mass_eq_zero_of_ae μ f s hs hb, Real.negMulLog_zero]

theorem mass_map {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (g : β → γ) (hg : Measurable g) (c : γ) :
    mass (μ.map f) g c = mass μ (g ∘ f) c := by
  unfold mass Measure.real
  change ((μ.map f) (g ⁻¹' {c})).toReal = _
  rw [Measure.map_apply hf ((measurableSet_singleton c).preimage hg)]
  rfl

theorem mass_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (ν : ι → Measure α) [∀ i, IsFiniteMeasure (ν i)] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i) (f : α → β) (b : β) :
    mass μ f b = ∑ i, w i*mass (ν i) f b := by
  unfold mass
  rw [hm]
  simp only [Measure.real_def, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw i)]

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.KernelEntropy ----
namespace OAI

universe uα uβ uX

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal

theorem finite_entropy_integral {X : Type uX} {β : Type uβ} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset β) (p : X → β → ℝ)
    (hm : ∀ b ∈ s, Measurable (fun y => p y b))
    (hp : ∀ b ∈ s, ∀ y, 0 ≤ p y b ∧ p y b ≤ 1) :
    (∫ y, ∑ b ∈ s, Real.negMulLog (p y b) ∂μ) ≤
      ∑ b ∈ s, Real.negMulLog (∫ y, p y b ∂μ) := by
  have hi (b) (hb : b ∈ s) : Integrable (fun y => p y b) μ :=
    (integrable_const (1 : ℝ)).mono' (hm b hb).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (hp b hb y).1]; exact (hp b hb y).2))
  have hni (b) (hb : b ∈ s) : Integrable (fun y => Real.negMulLog (p y b)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (Real.continuous_negMulLog.measurable.comp (hm b hb)).aestronglyMeasurable
    filter_upwards [] with y
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.negMulLog_nonneg (hp b hb y).1 (hp b hb y).2)]
    exact (Real.negMulLog_le_one_sub_self (hp b hb y).1).trans (sub_le_self _ (hp b hb y).1)
  rw [integral_finsetSum s hni]
  apply Finset.sum_le_sum
  intro b hb
  exact Real.concaveOn_negMulLog.le_map_integral Real.continuous_negMulLog.continuousOn
    isClosed_Ici (Filter.Eventually.of_forall (fun y => (hp b hb y).1)) (hi b hb) (hni b hb)

theorem random_observation_entropy {X : Type uX} {α : Type uα} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (F : α → X → ℝ) (hF : ∀ i, Measurable (F i))
    (hm : ν=∑ i, ENNReal.ofReal (p i) • μ.map (F i))
    (f : ℝ → ℤ) (hf : Measurable f) (s : Finset ℤ)
    (hs : ∀ i, ∀ᵐ y ∂μ, f (F i y) ∈ s) :
    (∫ y, FiniteEntropy.observableEntropy Finset.univ p (fun i => f (F i y)) ∂μ) ≤ entropy ν f := by
  classical
  let K : X → ℤ → ℝ := fun y b => FiniteEntropy.mass Finset.univ p (fun i => f (F i y)) b
  have hk (y : X) (b : ℤ) : K y b=∑ i, if f (F i y)=b then p i else 0 := by
    simp only [K,FiniteEntropy.mass,Finset.sum_filter]
  have hmK (b : ℤ) : Measurable (fun y => K y b) := by
    simp_rw [hk]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.ite
      (measurableSet_eq_fun (hf.comp (hF i)) measurable_const) measurable_const)
  have hpK (y : X) (b : ℤ) : 0 ≤ K y b ∧ K y b ≤ 1 := by
    refine ⟨FiniteEntropy.mass_nonneg _ _ _ (fun i _ => hp i) _,?_⟩
    change (∑ i ∈ Finset.univ.filter (fun i => f (F i y)=b), p i) ≤ 1
    rw [← hp1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hp i)
  have hmi (i : α) : IsProbabilityMeasure (μ.map (F i)) :=
    (Measure.isProbabilityMeasure_map_iff (hF i).aemeasurable).2 inferInstance
  let := hmi
  have hsupport : ∀ᵐ x ∂ν, f x ∈ s := by
    rw [hm]
    rw [ae_iff]
    simp only [Measure.coe_finsetSum,Finset.sum_apply,Measure.smul_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hh : ∀ᵐ x ∂μ.map (F i), f x ∈ s :=
      (ae_map_iff (hF i).aemeasurable (hf (s.finite_toSet.measurableSet))).mpr (hs i)
    rw [ae_iff] at hh
    rw [hh,smul_zero]
  have hmasses (b : ℤ) : (∫ y, K y b ∂μ)=mass ν f b := by
    rw [mass_mixture ν (fun i => μ.map (F i)) p hp hm f]
    simp_rw [hk]
    have hint (i : α) : Integrable (fun y => if f (F i y)=b then p i else 0) μ := by
      have hh : MeasurableSet {y | f (F i y)=b} :=
        measurableSet_eq_fun (hf.comp (hF i)) (measurable_const (a := b))
      have h := (integrable_const (p i) : Integrable (fun _ : X => p i) μ).indicator hh
      exact h.congr (Filter.Eventually.of_forall (fun y => by
        rw [Set.indicator_apply]
        rfl))
    rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [mass_map μ _ (hF i) f hf]
    have hind : (fun y => if f (F i y)=b then p i else 0) =
        ({y | f (F i y)=b} : Set X).indicator (fun _ => p i) := by
          funext y
          rw [Set.indicator_apply]
          rfl
    rw [hind,integral_indicator_const (p i) (show MeasurableSet {y | f (F i y)=b} from
      measurableSet_eq_fun (hf.comp (hF i)) (measurable_const (a := b)))]
    simp only [smul_eq_mul,mass,Function.comp_apply,mul_comm]
  have he : (fun y => FiniteEntropy.observableEntropy Finset.univ p (fun i => f (F i y))) =ᵐ[μ]
      fun y => ∑ b ∈ s, Real.negMulLog (K y b) := by
    filter_upwards [ae_all_iff.mpr hs] with y hy
    exact FiniteEntropy.observableEntropy_on_superset Finset.univ s p _ (fun i _ => hy i)
  rw [integral_congr_ae he,entropy_eq_sum ν f s hsupport]
  simpa only [hmasses] using finite_entropy_integral μ s K (fun b _ => hmK b) (fun b _ y => hpK y b)

end EntropyRateDimension.MeasureEntropy

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal


theorem solution.{uα,uX} : type_of% @_root_.OAI.EntropyRateDimension.MeasureEntropy.random_observation_entropy.{uα,uX} := @_root_.OAI.EntropyRateDimension.MeasureEntropy.random_observation_entropy.{uα,uX}
