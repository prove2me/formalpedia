-- Prove2me | solution 1 for LipBernoulli.MultiUtility.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T09:30:15.122549+00:00
-- url     : https://prove2.me/submissions/208afc0b-1ed1-499c-ba78-09ba2cba344d

import Mathlib
import Definitions.Def_LipBernoulli_MultiUtility_Setting
import Definitions.Def_LipBernoulli_MultiUtility_KR

open MeasureTheory
open scoped ENNReal NNReal

section
open MeasureTheory Filter
open scoped Topology
namespace LipBernoulli.MultiUtility.Fresh

noncomputable def approxMap {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) (n : ℕ) : SimpleFunc X X :=
  SimpleFunc.approxOn id measurable_id Set.univ e (Set.mem_univ e) n

lemma approxMap_tendsto {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e x : X) :
    Tendsto (fun n => approxMap e n x) atTop (𝓝 x) := by
  exact SimpleFunc.tendsto_approxOn measurable_id (Set.mem_univ e) (by simp)

lemma approxMap_dist_le {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e x : X) (n : ℕ) :
    dist x (approxMap e n x) ≤ dist x e := by
  have hh := SimpleFunc.edist_approxOn_le measurable_id (Set.mem_univ e) x n
  change edist (approxMap e n x) x ≤ edist e x at hh
  rw [edist_dist,edist_dist] at hh
  have hr := (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hh
  simpa only [dist_comm] using hr

lemma approxMap_image_dist_le {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e x : X) (n : ℕ) :
    dist e (approxMap e n x) ≤ 2*dist e x := by
  have hh := dist_triangle e x (approxMap e n x)
  have he := approxMap_dist_le e x n
  rw [dist_comm x e] at he
  linarith

lemma approxMap_error_integrable {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) (μ : Measure X)
    (hm : Integrable (fun x => dist e x) μ) (n : ℕ) :
    Integrable (fun x => dist x (approxMap e n x)) μ := by
  apply hm.mono' ((measurable_id.dist (approxMap e n).measurable).aestronglyMeasurable)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg,dist_comm x e,id_eq] using approxMap_dist_le e x n

lemma approxMap_image_moment {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) (μ : Measure X)
    (hm : Integrable (fun x => dist e x) μ) (n : ℕ) :
    Integrable (fun x => dist e (approxMap e n x)) μ := by
  apply (hm.const_mul 2).mono' ((measurable_const.dist (approxMap e n).measurable).aestronglyMeasurable)
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg] using approxMap_image_dist_le e x n

lemma approxMap_error_tendsto {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) (μ : Measure X)
    (hm : Integrable (fun x => dist e x) μ) :
    Tendsto (fun n => ∫ x, dist x (approxMap e n x) ∂μ) atTop (𝓝 0) := by
  have hh := tendsto_integral_of_dominated_convergence (fun x => dist e x)
    (fun n => (measurable_id.dist (approxMap e n).measurable).aestronglyMeasurable)
    hm (fun n => by
      filter_upwards [] with x
      simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg,dist_comm x e,id_eq] using approxMap_dist_le e x n)
    (by
      filter_upwards [] with x
      simpa only [dist_self] using tendsto_const_nhds.dist (approxMap_tendsto e x))
  simpa only [id_eq,dist_self,integral_zero] using hh

end LipBernoulli.MultiUtility.Fresh
end

section
open MeasureTheory Finset
open scoped Classical
namespace LipBernoulli.MultiUtility.Fresh

lemma simple_preimage_partition {X Y : Type*} [MeasurableSpace X] (p : SimpleFunc X Y)
    (s : Set Y) : p ⁻¹' s = ⋃ a ∈ p.range, if a ∈ s then p ⁻¹' {a} else ∅ := by
  classical
  ext x
  simp only [Set.mem_preimage, Set.mem_iUnion]
  constructor
  · intro hx
    exact ⟨p x,p.mem_range_self x,by simp [hx]⟩
  · rintro ⟨a,ha,hx⟩
    by_cases hs : a ∈ s
    · simp only [hs,ite_true,Set.mem_preimage,Set.mem_singleton_iff] at hx
      simpa only [hx] using hs
    · simp [hs] at hx

lemma signed_simple_map_eq_sum {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : SignedMeasure X) (p : SimpleFunc X Y) :
    μ.map p = ∑ a ∈ p.range, μ (p ⁻¹' {a}) • (Measure.dirac a).toSignedMeasure := by
  classical
  ext s hs
  rw [VectorMeasure.map_apply μ p.measurable hs, simple_preimage_partition]
  have hd : Set.PairwiseDisjoint (↑p.range) (fun a => if a ∈ s then p ⁻¹' {a} else ∅) := by
    intro a ha b hb hab
    change Disjoint (if a ∈ s then p ⁻¹' {a} else ∅) (if b ∈ s then p ⁻¹' {b} else ∅)
    by_cases hsa : a ∈ s <;> by_cases hsb : b ∈ s
    · simp only [hsa,hsb,ite_true]
      exact (Set.disjoint_singleton.mpr hab).preimage p
    · simp [hsa,hsb]
    · simp [hsa,hsb]
    · simp [hsa,hsb]
  rw [μ.of_biUnion_finset hd (by
    intro a ha
    split_ifs
    · exact p.measurableSet_fiber a
    · exact MeasurableSet.empty)]
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases h : a ∈ s
  · simp [h,Measure.toSignedMeasure_apply_measurable hs,measureReal_def,Measure.dirac_apply' _ hs]
  · simp [h,Measure.toSignedMeasure_apply_measurable hs,measureReal_def,Measure.dirac_apply' _ hs]

lemma signed_simple_map_finitelySupported {X : Type*} [MeasurableSpace X]
    (μ : SignedMeasure X) (p : SimpleFunc X X) : IsFinitelySupported (μ.map p) :=
  ⟨p.range,fun a => μ (p ⁻¹' {a}),signed_simple_map_eq_sum μ p⟩

lemma signed_map_univ {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : SignedMeasure X) {p : X → Y} (hp : Measurable p) :
    μ.map p Set.univ = μ Set.univ := by
  rw [VectorMeasure.map_apply μ hp MeasurableSet.univ,Set.preimage_univ]

end LipBernoulli.MultiUtility.Fresh
end

section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace LipBernoulli.MultiUtility.Fresh

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.SeparableSpace X]

lemma integrable_dist_of_pair_moment (ν : Measure X) [IsFiniteMeasure ν] (e : X)
    (h : ∫⁻ z : X × X, edist z.1 z.2 ∂(ν.prod ν) < ∞) :
    Integrable (fun x => dist e x) ν := by
  by_cases hν : ν = 0
  · subst ν
    simp
  have : NeZero ν := ⟨hν⟩
  have hp : Integrable (fun z : X × X => dist z.1 z.2) (ν.prod ν) := by
    refine ⟨(continuous_fst.dist continuous_snd).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg,edist_dist] using h
  obtain ⟨y,hy⟩ := hp.prod_right_ae.exists
  apply ((integrable_const (dist e y)).add hy).mono'
    (continuous_const.dist continuous_id).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg,Pi.add_apply,id_eq] using dist_triangle e y x

lemma pair_moment_of_integrable_dist (ν : Measure X) [IsFiniteMeasure ν] (e : X)
    (h : Integrable (fun x => dist e x) ν) :
    ∫⁻ z : X × X, edist z.1 z.2 ∂(ν.prod ν) < ∞ := by
  have hp : Integrable (fun z : X × X => dist z.1 z.2) (ν.prod ν) := by
    apply ((h.comp_fst ν).add (h.comp_snd ν)).mono'
      (continuous_fst.dist continuous_snd).aestronglyMeasurable
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg,dist_comm z.1 e,Pi.add_apply] using
      dist_triangle z.1 e z.2
  have hh := hp.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_norm] at hh
  simpa only [Real.norm_eq_abs,abs_of_nonneg dist_nonneg,edist_dist] using hh

lemma kr_iff_moment (e : X) (μ : SignedMeasure X) :
    μ ∈ KR X ↔ μ Set.univ = 0 ∧ Integrable (fun x => dist e x) μ.totalVariation := by
  constructor
  · intro h
    exact ⟨h.1,integrable_dist_of_pair_moment μ.totalVariation e h.2⟩
  · rintro ⟨hm,hi⟩
    exact ⟨hm,pair_moment_of_integrable_dist μ.totalVariation e hi⟩

omit [TopologicalSpace.SeparableSpace X] in
lemma lipschitz_integrable_of_moment (ν : Measure X) [IsFiniteMeasure ν] (e : X)
    (hm : Integrable (fun x => dist e x) ν) {f : X → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : Integrable f ν := by
  apply ((integrable_const |f e|).add (hm.const_mul (L : ℝ))).mono'
    hf.continuous.aestronglyMeasurable
  filter_upwards [] with x
  have h := hf.dist_le_mul x e
  have ha := abs_add_le (f x-f e) (f e)
  rw [sub_add_cancel] at ha
  rw [Real.dist_eq] at h
  simp only [Real.norm_eq_abs,Pi.add_apply]
  rw [dist_comm e x]
  linarith

lemma kr_lipschitz_integrable (e : X) {μ : SignedMeasure X} (hμ : μ ∈ KR X)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    Integrable f μ.totalVariation :=
  lipschitz_integrable_of_moment μ.totalVariation e ((kr_iff_moment e μ).mp hμ).2 hf

end LipBernoulli.MultiUtility.Fresh
end

section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipBernoulli.MultiUtility.Fresh
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.SeparableSpace X]

omit [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma kr_zero : (0 : SignedMeasure X) ∈ KR X := by
  simp [KR,SignedMeasure.totalVariation_zero]

lemma kr_add (e : X) {μ ν : SignedMeasure X} (hμ : μ ∈ KR X) (hν : ν ∈ KR X) :
    μ+ν ∈ KR X := by
  rw [kr_iff_moment e] at hμ hν ⊢
  refine ⟨by simp [hμ.1,hν.1],?_⟩
  simp only [SignedMeasure.totalVariation_eq_variation] at hμ hν ⊢
  exact VectorMeasure.Integrable.add_vectorMeasure hμ.2 hν.2

lemma kr_sub (e : X) {μ ν : SignedMeasure X} (hμ : μ ∈ KR X) (hν : ν ∈ KR X) :
    μ-ν ∈ KR X := by
  rw [kr_iff_moment e] at hμ hν ⊢
  refine ⟨by simp [hμ.1,hν.1],?_⟩
  simp only [SignedMeasure.totalVariation_eq_variation] at hμ hν ⊢
  exact VectorMeasure.Integrable.sub_vectorMeasure hμ.2 hν.2

lemma kr_smul (e : X) (c : ℝ) {μ : SignedMeasure X} (hμ : μ ∈ KR X) : c • μ ∈ KR X := by
  rw [kr_iff_moment e] at hμ ⊢
  refine ⟨by simp [hμ.1],?_⟩
  simp only [SignedMeasure.totalVariation_eq_variation] at hμ ⊢
  exact VectorMeasure.Integrable.smul_vectorMeasure hμ.2 c

lemma kr_finset_sum (e : X) {ι : Type*} (s : Finset ι) (μ : ι → SignedMeasure X)
    (hμ : ∀ i ∈ s, μ i ∈ KR X) : ∑ i ∈ s, μ i ∈ KR X := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (kr_zero (X := X))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact kr_add e (hμ a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hμ i (Finset.mem_insert_of_mem hi)))

lemma kr_map_of_moment (e : X) {μ : SignedMeasure X} (hμ : μ ∈ KR X)
    {p : X → X} (hp : Measurable p)
    (hm : Integrable (fun x => dist e (p x)) μ.totalVariation) : μ.map p ∈ KR X := by
  rw [kr_iff_moment e]
  refine ⟨by simpa only [VectorMeasure.map_apply μ hp MeasurableSet.univ,Set.preimage_univ] using hμ.1,?_⟩
  simp only [SignedMeasure.totalVariation_eq_variation] at hm ⊢
  exact VectorMeasure.Integrable.map (continuous_const.dist continuous_id).aestronglyMeasurable hm

end LipBernoulli.MultiUtility.Fresh
end

section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipBernoulli.MultiUtility.Fresh

variable {X : Type*} [MeasurableSpace X]

lemma krIntegral_eq_vectorIntegral {μ : SignedMeasure X} {f : X → ℝ}
    (hf : Integrable f μ.totalVariation) :
    krIntegral μ f = ∫ᵛ x, f x ∂<•μ := by
  have hparts := integrable_add_measure.mp hf
  have hp : μ.toJordanDecomposition.posPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using hparts.1
  have hn : μ.toJordanDecomposition.negPart.toSignedMeasure.Integrable f := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using hparts.2
  change (∫ x, f x ∂μ.toJordanDecomposition.posPart) -
    (∫ x, f x ∂μ.toJordanDecomposition.negPart) = _
  rw [← VectorMeasure.integral_toSignedMeasure,← VectorMeasure.integral_toSignedMeasure,
    ← VectorMeasure.integral_sub_vectorMeasure hp hn]
  congr 1
  exact μ.toSignedMeasure_toJordanDecomposition

lemma krIntegral_add {μ ν : SignedMeasure X} {f : X → ℝ}
    (hf : Integrable f μ.totalVariation) (hg : Integrable f ν.totalVariation) :
    krIntegral (μ+ν) f = krIntegral μ f + krIntegral ν f := by
  have hf' : μ.Integrable f := by simpa only [SignedMeasure.totalVariation_eq_variation] using hf
  have hg' : ν.Integrable f := by simpa only [SignedMeasure.totalVariation_eq_variation] using hg
  rw [krIntegral_eq_vectorIntegral (by simpa only [SignedMeasure.totalVariation_eq_variation] using hf'.add_vectorMeasure hg'),
    krIntegral_eq_vectorIntegral hf,krIntegral_eq_vectorIntegral hg]
  exact VectorMeasure.integral_add_vectorMeasure hf' hg'

lemma krIntegral_sub {μ ν : SignedMeasure X} {f : X → ℝ}
    (hf : Integrable f μ.totalVariation) (hg : Integrable f ν.totalVariation) :
    krIntegral (μ-ν) f = krIntegral μ f - krIntegral ν f := by
  have hf' : μ.Integrable f := by simpa only [SignedMeasure.totalVariation_eq_variation] using hf
  have hg' : ν.Integrable f := by simpa only [SignedMeasure.totalVariation_eq_variation] using hg
  rw [krIntegral_eq_vectorIntegral (by simpa only [SignedMeasure.totalVariation_eq_variation] using hf'.sub_vectorMeasure hg'),
    krIntegral_eq_vectorIntegral hf,krIntegral_eq_vectorIntegral hg]
  exact VectorMeasure.integral_sub_vectorMeasure hf' hg'

lemma krIntegral_smul {μ : SignedMeasure X} {f : X → ℝ}
    (hf : Integrable f μ.totalVariation) (c : ℝ) :
    krIntegral (c • μ) f = c * krIntegral μ f := by
  have hf' : μ.Integrable f := by simpa only [SignedMeasure.totalVariation_eq_variation] using hf
  rw [krIntegral_eq_vectorIntegral (by simpa only [SignedMeasure.totalVariation_eq_variation] using hf'.smul_vectorMeasure c),
    krIntegral_eq_vectorIntegral hf,VectorMeasure.integral_smul_vectorMeasure]
  rfl

lemma krIntegral_toSignedMeasure (ν : Measure X) [IsFiniteMeasure ν] (f : X → ℝ)
    (hf : Integrable f ν) : krIntegral ν.toSignedMeasure f = ∫ x, f x ∂ν := by
  rw [krIntegral_eq_vectorIntegral (by
    simpa only [SignedMeasure.totalVariation_eq_variation,Measure.variation_toSignedMeasure] using hf),
    VectorMeasure.integral_toSignedMeasure]

lemma krIntegral_dirac [MeasurableSingletonClass X] (x : X) (f : X → ℝ) :
    krIntegral (Measure.dirac x).toSignedMeasure f = f x := by
  rw [krIntegral_toSignedMeasure _ _ (integrable_dirac (by simp)),integral_dirac]

lemma krIntegral_const (μ : SignedMeasure X) (c : ℝ) :
    krIntegral μ (fun _ => c) = c * μ Set.univ := by
  simp only [krIntegral,integral_const,smul_eq_mul]
  rw [μ.apply_eq_posPart_real_sub_negPart_real MeasurableSet.univ]
  ring

lemma krIntegral_fun_sub {μ : SignedMeasure X} {f g : X → ℝ}
    (hf : Integrable f μ.totalVariation) (hg : Integrable g μ.totalVariation) :
    krIntegral μ (fun x => f x-g x) = krIntegral μ f-krIntegral μ g := by
  simp only [krIntegral]
  have hp := integrable_add_measure.mp hf
  have hq := integrable_add_measure.mp hg
  rw [integral_sub hp.1 hq.1,integral_sub hp.2 hq.2]
  ring

lemma krIntegral_fun_smul (μ : SignedMeasure X) (f : X → ℝ) (c : ℝ) :
    krIntegral μ (fun x => c*f x) = c*krIntegral μ f := by
  simp only [krIntegral,integral_const_mul]
  ring

lemma abs_krIntegral_le {μ : SignedMeasure X} {f : X → ℝ}
    (hf : Integrable f μ.totalVariation) :
    |krIntegral μ f| ≤ ∫ x, |f x| ∂μ.totalVariation := by
  have hp := integrable_add_measure.mp hf
  calc
    |krIntegral μ f| ≤ |∫ x,f x ∂μ.toJordanDecomposition.posPart| +
      |∫ x,f x ∂μ.toJordanDecomposition.negPart| := abs_sub _ _
    _ ≤ (∫ x,|f x| ∂μ.toJordanDecomposition.posPart)+
      (∫ x,|f x| ∂μ.toJordanDecomposition.negPart) :=
      add_le_add (abs_integral_le_integral_abs) (abs_integral_le_integral_abs)
    _ = _ := (integral_add_measure hp.1.abs hp.2.abs).symm

end LipBernoulli.MultiUtility.Fresh
end

section
open MeasureTheory
namespace LipBernoulli.MultiUtility.Fresh
variable {X : Type*} [MeasurableSpace X]

lemma krIntegral_map {μ : SignedMeasure X} {p : X → X} (hp : Measurable p)
    {f : X → ℝ} (hf : Measurable f)
    (hcomp : Integrable (fun x => f (p x)) μ.totalVariation) :
    krIntegral (μ.map p) f = krIntegral μ (fun x => f (p x)) := by
  have hc : μ.Integrable (f ∘ p) := by
    simpa only [SignedMeasure.totalVariation_eq_variation,Function.comp_def] using hcomp
  have hm : (μ.map p).Integrable f := VectorMeasure.Integrable.map hf.aestronglyMeasurable hc
  rw [krIntegral_eq_vectorIntegral (by simpa only [SignedMeasure.totalVariation_eq_variation] using hm),
    krIntegral_eq_vectorIntegral hcomp]
  exact VectorMeasure.integral_map hp hf.aestronglyMeasurable hc

end LipBernoulli.MultiUtility.Fresh
end

section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace LipBernoulli.MultiUtility.Fresh
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.SeparableSpace X]

omit [BorelSpace X] [TopologicalSpace.SeparableSpace X] in
lemma krIntegral_lipschitz_bound (e : X) {μ : SignedMeasure X} (hμ : μ ∈ KR X)
    {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ENNReal.ofReal |krIntegral μ f| ≤ (L : ℝ≥0∞)*krNorm μ := by
  by_cases hL : L = 0
  · subst L
    have he : f = fun _ => f e := by
      funext x
      apply dist_le_zero.mp
      simpa using hf.dist_le_mul x e
    rw [he,krIntegral_const,hμ.1,mul_zero]
    simp
  have hLp : 0 < (L : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hL)
  let g : X → ℝ := fun x => (1/(L : ℝ))*f x
  have hg : LipschitzWith 1 g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hf.dist_le_mul x y
    rw [Real.dist_eq] at h
    change |(1/(L:ℝ))*f x-(1/(L:ℝ))*f y| ≤ 1*dist x y
    rw [← mul_sub,abs_mul,abs_of_pos (one_div_pos.mpr hLp),one_mul]
    simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using
      (div_le_iff₀ hLp).mpr (by simpa only [mul_comm] using h)
  have hh : ENNReal.ofReal |krIntegral μ g| ≤ krNorm μ :=
    le_iSup_of_le g (le_iSup_of_le hg le_rfl)
  have he : (L : ℝ)*|krIntegral μ g| = |krIntegral μ f| := by
    rw [show krIntegral μ g = (1/(L:ℝ))*krIntegral μ f from krIntegral_fun_smul μ f _,
      abs_mul,abs_of_pos (one_div_pos.mpr hLp)]
    field_simp
  calc
    _ = (L : ℝ≥0∞)*ENNReal.ofReal |krIntegral μ g| := by
      rw [← ENNReal.ofReal_coe_nnreal,← ENNReal.ofReal_mul hLp.le,he]
    _ ≤ _ := mul_le_mul' le_rfl hh

lemma krNorm_le_moment (e : X) {μ : SignedMeasure X} (hμ : μ ∈ KR X) :
    krNorm μ ≤ ENNReal.ofReal (∫ x,dist e x ∂μ.totalVariation) := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  have hi := kr_lipschitz_integrable e hμ hf
  have hc : Integrable (fun _ : X => f e) μ.totalVariation := integrable_const _
  have he : krIntegral μ (fun x => f x-f e) = krIntegral μ f := by
    rw [krIntegral_fun_sub hi hc,krIntegral_const,hμ.1,mul_zero,sub_zero]
  rw [← he]
  apply ENNReal.ofReal_le_ofReal
  apply (abs_krIntegral_le (hi.sub hc)).trans
  apply integral_mono (hi.sub hc).abs ((kr_iff_moment e μ).mp hμ).2
  intro x
  have h := hf.dist_le_mul x e
  simpa only [Pi.sub_apply,Real.dist_eq,NNReal.coe_one,one_mul,dist_comm x e] using h

lemma krNorm_ne_top (e : X) {μ : SignedMeasure X} (hμ : μ ∈ KR X) : krNorm μ ≠ ⊤ :=
  ne_of_lt ((krNorm_le_moment e hμ).trans_lt ENNReal.ofReal_lt_top)

end LipBernoulli.MultiUtility.Fresh
end

section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipBernoulli.MultiUtility.Fresh
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace.SeparableSpace X]

lemma krNorm_sub_map_le (e : X) {μ : SignedMeasure X} (hμ : μ ∈ KR X)
    {p : X → X} (hp : Measurable p)
    (hm : Integrable (fun x => dist e (p x)) μ.totalVariation) :
    krNorm (μ - μ.map p) ≤ ENNReal.ofReal (∫ x, dist x (p x) ∂μ.totalVariation) := by
  have he := ((kr_iff_moment e μ).mp hμ).2
  have herr : Integrable (fun x => dist x (p x)) μ.totalVariation := by
    apply (he.add hm).mono' (measurable_id.dist hp).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
    simpa only [id_eq,Pi.add_apply,dist_comm x e] using dist_triangle x e (p x)
  have hmap := kr_map_of_moment e hμ hp hm
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  have hi := kr_lipschitz_integrable e hμ hf
  have hip := kr_lipschitz_integrable e hmap hf
  have hic : Integrable (fun x => f (p x)) μ.totalVariation := by
    apply ((integrable_const |f e|).add hm).mono'
      (hf.continuous.measurable.comp hp).aestronglyMeasurable
    filter_upwards [] with x
    have hd := hf.dist_le_mul (p x) e
    have ha := abs_add_le (f (p x)-f e) (f e)
    rw [sub_add_cancel] at ha
    simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hd
    change |f (p x)| ≤ |f e| + dist e (p x)
    rw [dist_comm (p x) e] at hd
    linarith
  have hid : krIntegral (μ-μ.map p) f = krIntegral μ (fun x => f x-f (p x)) := by
    rw [krIntegral_sub hi hip,krIntegral_map hp hf.continuous.measurable hic,
      krIntegral_fun_sub hi hic]
  rw [hid]
  apply ENNReal.ofReal_le_ofReal
  apply (abs_krIntegral_le (hi.sub hic)).trans
  apply integral_mono (hi.sub hic).abs herr
  intro x
  simpa only [Pi.sub_apply,Real.dist_eq,NNReal.coe_one,one_mul] using hf.dist_le_mul x (p x)

end LipBernoulli.MultiUtility.Fresh
end

section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace LipBernoulli.MultiUtility.Fresh

noncomputable def approxSigned {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) (μ : SignedMeasure X) (n : ℕ) : SignedMeasure X :=
  μ.map (approxMap e n)

lemma approxSigned_mem_KR {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) {μ : SignedMeasure X}
    (hμ : μ ∈ KR X) (n : ℕ) : approxSigned e μ n ∈ KR X := by
  exact kr_map_of_moment e hμ (approxMap e n).measurable
    (approxMap_image_moment e μ.totalVariation ((kr_iff_moment e μ).mp hμ).2 n)

lemma approxSigned_finitelySupported {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) (μ : SignedMeasure X) (n : ℕ) :
    IsFinitelySupported (approxSigned e μ n) :=
  signed_simple_map_finitelySupported μ (approxMap e n)

lemma approxSigned_norm_tendsto {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) {μ : SignedMeasure X}
    (hμ : μ ∈ KR X) :
    Tendsto (fun n => krNorm (μ-approxSigned e μ n)) atTop (𝓝 0) := by
  have hm := ((kr_iff_moment e μ).mp hμ).2
  have he : Tendsto (fun n => ENNReal.ofReal (∫ x, dist x (approxMap e n x) ∂μ.totalVariation))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp (approxMap_error_tendsto e μ.totalVariation hm)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun _ => zero_le)
  intro n
  exact krNorm_sub_map_le e hμ (approxMap e n).measurable
    (approxMap_image_moment e μ.totalVariation hm n)

lemma exists_finite_kr_approx {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) {μ : SignedMeasure X}
    (hμ : μ ∈ KR X) : ∃ σ : ℕ → SignedMeasure X,
      (∀ n, σ n ∈ KR X ∧ IsFinitelySupported (σ n)) ∧
      Tendsto (fun n => krNorm (μ-σ n)) atTop (𝓝 0) :=
  ⟨approxSigned e μ,fun n => ⟨approxSigned_mem_KR e hμ n,approxSigned_finitelySupported e μ n⟩,
    approxSigned_norm_tendsto e hμ⟩

end LipBernoulli.MultiUtility.Fresh
end

section

open MeasureTheory
open scoped ENNReal NNReal
namespace LipBernoulli.MultiUtility.Fresh

variable {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X]

noncomputable def molecule (x y : X) : SignedMeasure X :=
  (Measure.dirac x).toSignedMeasure - (Measure.dirac y).toSignedMeasure

omit [MetricSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma molecule_self (x : X) : molecule x x = 0 := by simp [molecule]

omit [MetricSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma molecule_add (x y z : X) : molecule x y + molecule y z = molecule x z := by
  unfold molecule
  abel

omit [MetricSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma dirac_totalVariation (x : X) :
    (Measure.dirac x).toSignedMeasure.totalVariation = Measure.dirac x := by
  rw [SignedMeasure.totalVariation_eq_variation, Measure.variation_toSignedMeasure]

omit [MetricSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma molecule_variation_le (x y : X) :
    (molecule x y).totalVariation ≤ Measure.dirac x + Measure.dirac y := by
  rw [SignedMeasure.totalVariation_eq_variation]
  simpa [molecule] using VectorMeasure.variation_sub_le
    (μ := (Measure.dirac x).toSignedMeasure) (ν := (Measure.dirac y).toSignedMeasure)

lemma molecule_mem_KR (x y : X) : molecule x y ∈ KR X := by
  apply (kr_iff_moment x (molecule x y)).mpr
  constructor
  · simp [molecule]
  · have hx : Integrable (fun z => dist x z) (Measure.dirac x) := integrable_dirac (by simp)
    have hy : Integrable (fun z => dist x z) (Measure.dirac y) := integrable_dirac (by simp)
    exact (hx.add_measure hy).mono_measure (molecule_variation_le x y)

lemma molecule_integral (x y : X) (f : X → ℝ) :
    krIntegral (molecule x y) f = f x - f y := by
  have hx : Integrable f (Measure.dirac x).toSignedMeasure.totalVariation := by
    rw [dirac_totalVariation]
    exact integrable_dirac (by simp)
  have hy : Integrable f (Measure.dirac y).toSignedMeasure.totalVariation := by
    rw [dirac_totalVariation]
    exact integrable_dirac (by simp)
  rw [molecule, krIntegral_sub hx hy, krIntegral_dirac, krIntegral_dirac]

lemma molecule_norm_le (x y : X) : krNorm (molecule x y) ≤ ENNReal.ofReal (dist x y) := by
  apply iSup_le
  intro f
  apply iSup_le
  intro hf
  rw [molecule_integral]
  apply ENNReal.ofReal_le_ofReal
  simpa [Real.dist_eq] using hf.dist_le_mul x y

end LipBernoulli.MultiUtility.Fresh
end

section

open MeasureTheory
open scoped ENNReal NNReal
namespace LipBernoulli.MultiUtility.Fresh

variable {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [TopologicalSpace.SeparableSpace X] [BorelSpace X] in
lemma finite_zero_mass_molecular_representation (e : X) {μ : SignedMeasure X}
    (hfinite : IsFinitelySupported μ) (hmass : μ Set.univ = 0) :
    ∃ s : Finset X, ∃ c : X → ℝ, μ = ∑ x ∈ s, c x • molecule x e := by
  classical
  obtain ⟨s, c, hrep⟩ := hfinite
  have hsum : ∑ x ∈ s, c x = 0 := by
    have h := congrArg (fun ν : SignedMeasure X => ν Set.univ) hrep
    simpa [hmass, Finset.sum_apply, smul_apply,
      Measure.toSignedMeasure_apply_measurable] using h.symm
  refine ⟨s, c, ?_⟩
  calc
    μ = ∑ x ∈ s, c x • (Measure.dirac x).toSignedMeasure := hrep
    _ = ∑ x ∈ s, c x • molecule x e := by
      simp only [molecule, smul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_smul, hsum, zero_smul, sub_zero]

end LipBernoulli.MultiUtility.Fresh
end

section

open MeasureTheory
open scoped ENNReal NNReal
namespace LipBernoulli.MultiUtility.Fresh

variable {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma functional_finite_recovery (e : X) (Φ : SignedMeasure X → ℝ)
    (hadd : ∀ μ ∈ KR X, ∀ ν ∈ KR X, Φ (μ + ν) = Φ μ + Φ ν)
    (hsmul : ∀ c : ℝ, ∀ μ ∈ KR X, Φ (c • μ) = c * Φ μ)
    (u : X → ℝ) (hu0 : u e = 0) {L : ℝ≥0} (hu : LipschitzWith L u)
    (hmatch : ∀ x, Φ (molecule x e) = u x)
    {μ : SignedMeasure X} (hμ : μ ∈ KR X) (hfinite : IsFinitelySupported μ) :
    Φ μ = krIntegral μ u := by
  classical
  obtain ⟨s, c, rfl⟩ := finite_zero_mass_molecular_representation e hfinite hμ.1
  have hzero : Φ 0 = 0 := by
    simpa using hsmul 0 (molecule e e) (molecule_mem_KR e e)
  have hterm : ∀ x, c x • molecule x e ∈ KR X :=
    fun x => kr_smul e (c x) (molecule_mem_KR x e)
  have hsumKR : ∀ t : Finset X, (∑ x ∈ t, c x • molecule x e) ∈ KR X :=
    fun t => kr_finset_sum e t _ (fun x _ => hterm x)
  have hsum : ∀ t : Finset X,
      Φ (∑ x ∈ t, c x • molecule x e) = krIntegral (∑ x ∈ t, c x • molecule x e) u := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp [hzero, krIntegral, SignedMeasure.toJordanDecomposition_zero,
        JordanDecomposition.zero_posPart, JordanDecomposition.zero_negPart]
    | @insert x t hx ih =>
      rw [Finset.sum_insert hx, hadd _ (hterm x) _ (hsumKR t),
        krIntegral_add (kr_lipschitz_integrable e (hterm x) hu)
          (kr_lipschitz_integrable e (hsumKR t) hu), ih,
        hsmul _ _ (molecule_mem_KR x e),
        krIntegral_smul (kr_lipschitz_integrable e (molecule_mem_KR x e) hu),
        molecule_integral, hu0, sub_zero, hmatch]
  exact hsum s

end LipBernoulli.MultiUtility.Fresh
end

section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace LipBernoulli.MultiUtility.Fresh
variable {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma functional_full_recovery (e : X) (Φ : SignedMeasure X → ℝ) (C : ℝ≥0)
    (hadd : ∀ μ ∈ KR X, ∀ ν ∈ KR X, Φ (μ + ν) = Φ μ + Φ ν)
    (hsmul : ∀ c : ℝ, ∀ μ ∈ KR X, Φ (c • μ) = c * Φ μ)
    (hbound : ∀ μ ∈ KR X, ENNReal.ofReal |Φ μ| ≤ (C : ℝ≥0∞) * krNorm μ)
    (u : X → ℝ) (hu0 : u e = 0) (hu : LipschitzWith C u)
    (hmatch : ∀ x, Φ (molecule x e) = u x)
    {μ : SignedMeasure X} (hμ : μ ∈ KR X) : Φ μ = krIntegral μ u := by
  obtain ⟨σ,hσ,hlim⟩ := exists_finite_kr_approx e hμ
  have hm : ∀ n, μ-σ n ∈ KR X := fun n => kr_sub e hμ (hσ n).1
  have hb : ∀ n, ENNReal.ofReal |Φ μ-krIntegral μ u| ≤
      (C : ℝ≥0∞)*krNorm (μ-σ n)+(C : ℝ≥0∞)*krNorm (μ-σ n) := by
    intro n
    have hΦ := hadd (μ-σ n) (hm n) (σ n) (hσ n).1
    rw [sub_add_cancel] at hΦ
    have hI := krIntegral_sub (kr_lipschitz_integrable e hμ hu)
      (kr_lipschitz_integrable e (hσ n).1 hu)
    have hf := functional_finite_recovery e Φ hadd hsmul u hu0 hu hmatch (hσ n).1 (hσ n).2
    have he : Φ μ-krIntegral μ u = Φ (μ-σ n)-krIntegral (μ-σ n) u := by
      rw [hI]
      linarith
    rw [he]
    calc
      _ ≤ ENNReal.ofReal (|Φ (μ-σ n)|+|krIntegral (μ-σ n) u|) :=
        ENNReal.ofReal_le_ofReal (abs_sub _ _)
      _ = ENNReal.ofReal |Φ (μ-σ n)|+ENNReal.ofReal |krIntegral (μ-σ n) u| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := add_le_add (hbound _ (hm n)) (krIntegral_lipschitz_bound e (hm n) hu)
  have hc : Tendsto (fun n => (C : ℝ≥0∞)*krNorm (μ-σ n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top)
  have hz : ENNReal.ofReal |Φ μ-krIntegral μ u| ≤ 0 :=
    ge_of_tendsto (by simpa only [add_zero] using hc.add hc) (Filter.Eventually.of_forall hb)
  have hab : |Φ μ-krIntegral μ u| ≤ 0 := ENNReal.ofReal_eq_zero.mp (le_antisymm hz zero_le)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hab (abs_nonneg _)))

end LipBernoulli.MultiUtility.Fresh
end

section

open MeasureTheory
open scoped ENNReal NNReal
namespace LipBernoulli.MultiUtility.Fresh

variable {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
  [MeasurableSpace X] [BorelSpace X]

lemma functional_molecule_recovery (e : X) (Φ : SignedMeasure X → ℝ) (C : ℝ≥0)
    (hadd : ∀ μ ∈ KR X, ∀ ν ∈ KR X, Φ (μ + ν) = Φ μ + Φ ν)
    (hsmul : ∀ c : ℝ, ∀ μ ∈ KR X, Φ (c • μ) = c * Φ μ)
    (hbound : ∀ μ ∈ KR X, ENNReal.ofReal |Φ μ| ≤ (C : ℝ≥0∞) * krNorm μ) :
    let u : X → ℝ := fun x => Φ (molecule x e)
    u e = 0 ∧ LipschitzWith C u ∧
      ∀ x y, Φ (molecule x y) = u x - u y := by
  dsimp only
  have hzero : Φ 0 = 0 := by
    simpa using hsmul 0 (molecule e e) (molecule_mem_KR e e)
  have hdiff : ∀ x y, Φ (molecule x y) = Φ (molecule x e) - Φ (molecule y e) := by
    intro x y
    have h := hadd (molecule x y) (molecule_mem_KR x y)
      (molecule y e) (molecule_mem_KR y e)
    rw [molecule_add] at h
    linarith
  refine ⟨by rw [molecule_self, hzero], ?_, hdiff⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← hdiff x y]
  have hb := (hbound (molecule x y) (molecule_mem_KR x y)).trans
    (mul_le_mul' le_rfl (molecule_norm_le x y))
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.coe_nonneg dist_nonneg)).mp
  simpa only [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal] using hb

lemma functions_eq_of_molecule_integrals (e : X) (u v : X → ℝ)
    (hu : u e = 0) (hv : v e = 0)
    (h : ∀ μ ∈ KR X, krIntegral μ u = krIntegral μ v) : u = v := by
  funext x
  have hx := h (molecule x e) (molecule_mem_KR x e)
  simpa only [molecule_integral, hu, hv, sub_zero] using hx

end LipBernoulli.MultiUtility.Fresh
end

section
open MeasureTheory
open scoped ENNReal NNReal
namespace LipBernoulli.MultiUtility.Fresh

/-- Theorem 2.3, p. 7: `KR(X)* ≅ Lip₀(X)` for a separable metric space `X` pointed at `e`, through
`u ↦ (μ ↦ ∫ u dμ)`. (a) every `u ∈ Lip₀(X)` with Lipschitz constant `L` gives a linear functional on
`KR(X)` of norm at most `L`; (b) every linear functional `Φ` on `KR(X)` with `|Φ μ| ≤ C ‖μ‖_KR` is
integration against some `C`-Lipschitz `u` vanishing at `e`; (c) `u` is determined by its functional.
(a) and (b) with the same `C` make the bijection isometric. -/
theorem native_theorem_2_3 {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) :
    (∀ (u : X → ℝ) (L : ℝ≥0), u e = 0 → LipschitzWith L u →
      (∀ μ ∈ KR X, ∀ ν ∈ KR X, krIntegral (μ + ν) u = krIntegral μ u + krIntegral ν u) ∧
      (∀ c : ℝ, ∀ μ ∈ KR X, krIntegral (c • μ) u = c * krIntegral μ u) ∧
      (∀ μ ∈ KR X, ENNReal.ofReal |krIntegral μ u| ≤ (L : ℝ≥0∞) * krNorm μ)) ∧
    (∀ (Φ : SignedMeasure X → ℝ) (C : ℝ≥0),
      (∀ μ ∈ KR X, ∀ ν ∈ KR X, Φ (μ + ν) = Φ μ + Φ ν) →
      (∀ c : ℝ, ∀ μ ∈ KR X, Φ (c • μ) = c * Φ μ) →
      (∀ μ ∈ KR X, ENNReal.ofReal |Φ μ| ≤ (C : ℝ≥0∞) * krNorm μ) →
      ∃ u : X → ℝ, u e = 0 ∧ LipschitzWith C u ∧ ∀ μ ∈ KR X, Φ μ = krIntegral μ u) ∧
    (∀ u v : X → ℝ, u e = 0 → v e = 0 →
      (∃ L : ℝ≥0, LipschitzWith L u) → (∃ L : ℝ≥0, LipschitzWith L v) →
      (∀ μ ∈ KR X, krIntegral μ u = krIntegral μ v) → u = v) := by
  refine ⟨?_,?_,?_⟩
  · intro u L _hu0 hu
    refine ⟨?_,?_,?_⟩
    · intro μ hμ ν hν
      exact krIntegral_add (kr_lipschitz_integrable e hμ hu) (kr_lipschitz_integrable e hν hu)
    · intro c μ hμ
      exact krIntegral_smul (kr_lipschitz_integrable e hμ hu) c
    · intro μ hμ
      exact krIntegral_lipschitz_bound e hμ hu
  · intro Φ C hadd hsmul hbound
    let u : X → ℝ := fun x => Φ (molecule x e)
    obtain ⟨hu0,hu,_hxy⟩ := functional_molecule_recovery e Φ C hadd hsmul hbound
    refine ⟨u,hu0,hu,?_⟩
    intro μ hμ
    exact functional_full_recovery e Φ C hadd hsmul hbound u hu0 hu (fun _ => rfl) hμ
  · intro u v hu hv _hLu _hLv h
    exact functions_eq_of_molecule_integrals e u v hu hv h

end LipBernoulli.MultiUtility.Fresh
end

open LipBernoulli.MultiUtility

theorem solution {X : Type*} [MetricSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] (e : X) :
    (∀ (u : X → ℝ) (L : ℝ≥0), u e = 0 → LipschitzWith L u →
      (∀ μ ∈ KR X, ∀ ν ∈ KR X, krIntegral (μ + ν) u = krIntegral μ u + krIntegral ν u) ∧
      (∀ c : ℝ, ∀ μ ∈ KR X, krIntegral (c • μ) u = c * krIntegral μ u) ∧
      (∀ μ ∈ KR X, ENNReal.ofReal |krIntegral μ u| ≤ (L : ℝ≥0∞) * krNorm μ)) ∧
    (∀ (Φ : SignedMeasure X → ℝ) (C : ℝ≥0),
      (∀ μ ∈ KR X, ∀ ν ∈ KR X, Φ (μ + ν) = Φ μ + Φ ν) →
      (∀ c : ℝ, ∀ μ ∈ KR X, Φ (c • μ) = c * Φ μ) →
      (∀ μ ∈ KR X, ENNReal.ofReal |Φ μ| ≤ (C : ℝ≥0∞) * krNorm μ) →
      ∃ u : X → ℝ, u e = 0 ∧ LipschitzWith C u ∧ ∀ μ ∈ KR X, Φ μ = krIntegral μ u) ∧
    (∀ u v : X → ℝ, u e = 0 → v e = 0 →
      (∃ L : ℝ≥0, LipschitzWith L u) → (∃ L : ℝ≥0, LipschitzWith L v) →
      (∀ μ ∈ KR X, krIntegral μ u = krIntegral μ v) → u = v)  := by
  exact Fresh.native_theorem_2_3 e
