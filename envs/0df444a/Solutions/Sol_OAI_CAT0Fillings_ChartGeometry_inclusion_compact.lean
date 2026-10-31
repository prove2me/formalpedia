-- Prove2me | solution 1 for OAI.CAT0Fillings.ChartGeometry.inclusion_compact
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T02:59:13.433014+00:00
-- url     : https://prove2.me/submissions/1a14e5df-5891-4814-bf4b-3437462a9401

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002

section
-- module Solutions.OAIQ29_C0.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `aemeasurable_pi_lambda` (with `f` implicit). -/
theorem _root_.AEMeasurable.of_eval {δ ι : Type*} [Countable ι] {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {μ : MeasureTheory.Measure δ} {f : δ → ∀ i, π i}
    (h : ∀ i, AEMeasurable (fun a => f a i) μ) : AEMeasurable f μ := aemeasurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_CountableTests
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings.Foundations
open MeasureTheory Set Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_countable_current_tests (d : ℕ) :
    ∃ (b : ℕ → ℕ → X → ℝ) (π : ℕ → ℕ → Fin d → X → ℝ),
      (∀ K j, Admissible (b K j) (π K j)) ∧
      ∀ S T : Functional X d, IsMetricCurrent S → IsMetricCurrent T →
        (∀ K j, S (b K j) (π K j) = T (b K j) (π K j)) → S = T := by
  choose p hp using fun K : ℕ => TopologicalSpace.exists_dense_seq (TestClass (X := X) d K)
  refine ⟨fun K j => (p K j).val.1,fun K j i => (p K j).val.2 i,?_,?_⟩
  · intro K j
    exact ⟨(p K j).boundedLip,fun i => ⟨K,(p K j).property.2.2 i⟩⟩
  · intro S T hS hT heq
    have he (K : ℕ) : TestClass.eval (K := K) S = TestClass.eval (K := K) T := by
      apply (hp K).equalizer (IsMetricCurrent.testClass_continuous hS K) (IsMetricCurrent.testClass_continuous hT K)
      funext j
      exact heq K j
    funext b π
    by_cases h : Admissible b π
    · obtain ⟨K,q,hb,hπ⟩ := admissible_mem_testClass h
      have hh := congrFun (he K) q
      simpa only [TestClass.eval,hb,hπ] using hh
    · rw [hS.offDomain b π h,hT.offDomain b π h]

theorem ae_eq_of_ae_test_eq {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {d : ℕ} {S T : A → Functional X d}
    (hS : ∀ᵐ a ∂μ, IsMetricCurrent (S a)) (hT : ∀ᵐ a ∂μ, IsMetricCurrent (T a))
    (he : ∀ b π, Admissible b π → ∀ᵐ a ∂μ, S a b π = T a b π) :
    ∀ᵐ a ∂μ, S a = T a := by
  obtain ⟨b,π,ha,hex⟩ := exists_countable_current_tests (X := X) d
  have hc : ∀ᵐ a ∂μ, ∀ K j, S a (b K j) (π K j) = T a (b K j) (π K j) :=
    ae_all_iff.mpr fun K => ae_all_iff.mpr fun j => he _ _ (ha K j)
  filter_upwards [hS,hT,hc] with a hs ht h
  exact hex _ _ hs ht h

end CAT0Fillings.Foundations

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_BorelAction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
universe u
attribute [local instance] Classical.propDecidable
namespace BorelCoefficients
variable {X : Type u} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}

lemma borelAction_congr_ae (hT : IsMetricCurrent T) {b c : X → ℝ}
    (hbc : b =ᵐ[μ] c) (π : Fin k → X → ℝ) :
    borelAction μ hT b π = borelAction μ hT c π := by
  by_cases hb : Integrable b μ
  · have hc := hb.congr hbc
    by_cases hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)
    · rw [borelAction_of_integrable μ hT hb π hπ, borelAction_of_integrable μ hT hc π hπ,
        (Integrable.toL1_eq_toL1_iff b c hb hc).mpr hbc]
    · simp only [borelAction, dite_eq_left hb, dite_eq_left hc, dite_eq_right hπ]
  · have hc : ¬Integrable c μ := fun hc => hb (hc.congr hbc.symm)
    simp only [borelAction, dite_eq_right hb, dite_eq_right hc]

end BorelCoefficients
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_Poincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {ν : Measure E} [IsFiniteMeasure ν]

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] [IsFiniteMeasure ν] in
lemma convolution_direction_bound {f η : E → ℝ} (hf : LocallyIntegrable f μ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x)
    {v : E} (hv : DirectionalVariation f v μ ν) (z : E) :
    |((f ⋆[(lsmul ℝ ℝ).precompR E, μ] fderiv ℝ η) z) v| ≤
      ∫ x, η (z-x) ∂ν := by
  let φ : E → ℝ := fun x => η (z-x)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hη.comp (contDiff_const.sub contDiff_id)
  have hcφ : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.subLeft z)
  have hd (x : E) : fderiv ℝ φ x = -(fderiv ℝ η (z-x)) := by
    have hh := ((hη.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (z-x)).hasFDerivAt.comp x
      ((hasFDerivAt_const z x).sub (hasFDerivAt_id x))
    simpa [φ,Function.comp_def] using hh.fderiv
  have hb := hv φ hφ hcφ
  simp only [hd,neg_apply,neg_mul,integral_neg,abs_neg] at hb
  have he : (fun x => |φ x|) = (fun x => η (z-x)) := by
    funext x
    exact abs_of_nonneg (hη0 _)
  rw [he] at hb
  rw [convolution_precompR_apply (lsmul ℝ ℝ) hf (hc.fderiv ℝ)
    (hη.continuous_fderiv (by simp)), convolution_def]
  simpa only [lsmul_apply,smul_eq_mul,mul_comm] using hb

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma continuous_kernelIntegral {η : E → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) : Continuous (fun z => ∫ x, η (z-x) ∂ν) := by
  obtain ⟨C,hbound⟩ := hη.bounded_above_of_compact_support hc
  exact continuous_of_dominated (bound := fun _ => C)
    (fun z => ((hη.comp (continuous_const.sub continuous_id)).aestronglyMeasurable))
    (fun z => ae_of_all _ fun x => hbound (z-x)) (integrable_const C)
    (ae_of_all _ fun x => hη.comp (continuous_id.sub continuous_const))

lemma kernelIntegral_ball_bound {η : E → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) (hint : ∫ x, η x ∂μ = 1)
    {ε : ℝ} (hs : Function.support η ⊆ closedBall 0 ε) (a : E) (r : ℝ) :
    (∫ z in closedBall a r, ∫ x, η (z-x) ∂ν ∂μ) ≤ ν.real (closedBall a (r+ε)) := by
  let Q := closedBall a r
  let A := closedBall a (r+ε)
  have : IsFiniteMeasure (μ.restrict Q) := ⟨by simp [Q,measure_closedBall_lt_top]⟩
  obtain ⟨C,hC⟩ := hη.bounded_above_of_compact_support hc
  have hp : Integrable (fun p : E × E => η (p.1-p.2)) ((μ.restrict Q).prod ν) :=
    Integrable.of_bound (hη.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable C
      (ae_of_all _ fun p => hC _)
  have hfub := integral_integral_swap (f := fun z x => η (z-x)) hp
  change (∫ z, ∫ x, η (z-x) ∂ν ∂μ.restrict Q) ≤ _
  rw [hfub]
  have hz (x : E) : Integrable (fun z => η (z-x)) μ := by
    exact (hη.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.subRight x))
  have hpoint (x : E) : (∫ z in Q, η (z-x) ∂μ) ≤ A.indicator (fun _ => (1:ℝ)) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      calc _ ≤ ∫ z, η (z-x) ∂μ := setIntegral_le_integral (hz x) (ae_of_all _ fun z => hη0 _)
        _ = 1 := by rw [integral_sub_right_eq_self, hint]
    · rw [indicator_of_notMem hx]
      have he : ∀ z ∈ Q, η (z-x) = 0 := by
        intro z hz
        by_contra hn
        have hn' : z-x ∈ closedBall 0 ε := hs hn
        have hd : dist x a ≤ r+ε := calc
          dist x a ≤ dist x z + dist z a := dist_triangle _ _ _
          _ ≤ ε + r := add_le_add (by simpa [dist_eq_norm, norm_sub_rev] using hn') hz
          _ = r+ε := add_comm _ _
        exact hx hd
      rw [setIntegral_congr_fun measurableSet_closedBall he,integral_zero]
  have hm := integral_mono hp.integral_prod_right
    ((integrable_const (1:ℝ) : Integrable (fun _ : E => (1:ℝ)) ν).indicator measurableSet_closedBall)
    hpoint
  exact hm.trans_eq (by rw [integral_indicator measurableSet_closedBall]; simp)

lemma euclidean_opNorm_le_coordinate_bound {k : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ i, |L (EuclideanSpace.basisFun (Fin k) ℝ i)| ≤ B) : ‖L‖ ≤ k*B := by
  apply L.opNorm_le_bound (by positivity)
  intro x
  have he := congrArg L ((EuclideanSpace.basisFun (Fin k) ℝ).sum_repr x)
  rw [map_sum] at he
  rw [←he]
  calc _ ≤ ∑ i : Fin k, ‖L (((EuclideanSpace.basisFun (Fin k) ℝ).repr x).ofLp i •
        EuclideanSpace.basisFun (Fin k) ℝ i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin k, ‖x‖*B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [map_smul,norm_smul]
      apply mul_le_mul _ (hb i) (abs_nonneg _) (norm_nonneg _)
      simpa using (PiLp.norm_apply_le ((EuclideanSpace.basisFun (Fin k) ℝ).repr x) i)
    _ = k*B*‖x‖ := by simp; ring

lemma mollified_gradient_integral_bound {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {m : Measure (EuclideanSpace ℝ (Fin k))} [m.IsAddHaarMeasure]
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ν]
    (hf : LocallyIntegrable f m)
    (hv : ∀ i, DirectionalVariation f (EuclideanSpace.basisFun (Fin k) ℝ i) m ν)
    (η : ContDiffBump (0 : EuclideanSpace ℝ (Fin k))) (a : EuclideanSpace ℝ (Fin k)) (r : ℝ) :
    (∫ z in closedBall a r,
      ‖(f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), m]
        fderiv ℝ (η.normed m)) z‖ ∂m) ≤ k * ν.real (closedBall a (r+η.rOut)) := by
  have hc := η.hasCompactSupport_normed (μ := m)
  have hd := (η.contDiff_normed (μ := m) (n := (⊤ : ℕ∞))).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg := (hc.fderiv ℝ).continuous_convolution_right
    ((lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k))) hf hd
  have hb (z : EuclideanSpace ℝ (Fin k)) :
      ‖(f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), m]
          fderiv ℝ (η.normed m)) z‖ ≤ k * ∫ x, η.normed m (z-x) ∂ν := by
    apply euclidean_opNorm_le_coordinate_bound _ (integral_nonneg fun x => η.nonneg_normed _)
    intro i
    exact convolution_direction_bound hf η.contDiff_normed hc η.nonneg_normed (hv i) z
  have hk := (continuous_kernelIntegral (ν := ν) η.continuous_normed hc).const_mul (k:ℝ)
  have hm := integral_mono
    (hg.norm.continuousOn.integrableOn_compact (μ := m) (isCompact_closedBall a r))
    (hk.continuousOn.integrableOn_compact (μ := m) (isCompact_closedBall a r)) hb
  rw [integral_const_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (kernelIntegral_ball_bound η.continuous_normed hc η.nonneg_normed η.integral_normed
      (by rw [η.support_normed_eq]; exact ball_subset_closedBall) a r) (Nat.cast_nonneg k))

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_Oscillation
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV

lemma integral_abs_le_of_ae_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {F : ℕ → α → ℝ} (hf : Integrable f μ) (hF : ∀ j, Integrable (F j) μ)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x))) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ j in atTop, (∫ x, |F j x| ∂μ) ≤ C) : (∫ x, |f x| ∂μ) ≤ C := by
  have hl' : ∀ᵐ x ∂μ, Tendsto (fun j => ENNReal.ofReal |F j x|) atTop
      (𝓝 (ENNReal.ofReal |f x|)) := hl.mono fun x hx => ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx.abs
  have hfat : (∫⁻ x, ENNReal.ofReal |f x| ∂μ) ≤
      liminf (fun j => ∫⁻ x, ENNReal.ofReal |F j x| ∂μ) atTop := by
    calc _ = ∫⁻ x, liminf (fun j => ENNReal.ofReal |F j x|) atTop ∂μ :=
        lintegral_congr_ae (hl'.mono fun _ hx => hx.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le' (fun j => (hF j).abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hu : liminf (fun j => ∫⁻ x, ENNReal.ofReal |F j x| ∂μ) atTop ≤ ENNReal.ofReal C := by
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    filter_upwards [hbound] with j hj
    rw [←ofReal_integral_eq_lintegral_ofReal (hF j).abs (ae_of_all _ fun x => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hj
  rw [←ofReal_integral_eq_lintegral_ofReal hf.abs (ae_of_all _ fun x => abs_nonneg _)] at hfat
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (hfat.trans hu)

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_Approximation
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.BorelCoefficients
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
variable {k : ℕ} {T : Functional X k}
variable (μ : Measure X) [IsFiniteMeasure μ]

lemma borelAction_const_coord (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π : Fin k → X → ℝ)
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) (c : ℝ)
    (hc : ∀ x, π i x = c) : borelAction μ hT f π = 0 := by
  simpa using borelAction_locality_mul μ hT hμ hf (BoundedLip.const 1) π hπ
    ⟨i, univ, c, isOpen_univ, subset_univ _, fun x _ => hc x⟩

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelClamp_lipschitz {c ε : ℝ} {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : LipschitzWith K (levelClamp c ε u) :=
  (hu.const_min (c + ε)).const_max (c - ε)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelClamp_eq {c ε : ℝ} {u : X → ℝ} {x : X} (h : |u x - c| < ε) :
    levelClamp c ε u x = u x := by
  obtain ⟨hlo, hhi⟩ := abs_lt.mp h
  dsimp [levelClamp]
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma levelClamp_tendsto (c : ℝ) (u : X → ℝ) (x : X) :
    Tendsto (fun n : ℕ => levelClamp c (1 / (n + 1)) u x) atTop (𝓝 c) := by
  have hd : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using (tendsto_const_nhds.sub hd :
      Tendsto (fun n : ℕ => c - 1 / (n + 1 : ℝ)) atTop (𝓝 (c - 0))))
    (by simpa using (tendsto_const_nhds.add hd :
      Tendsto (fun n : ℕ => c + 1 / (n + 1 : ℝ)) atTop (𝓝 (c + 0))))
  · intro n
    dsimp [levelClamp]
    simpa only [one_div] using (le_max_left (c - 1 / (n + 1 : ℝ)) (min (c + 1 / (n + 1 : ℝ)) (u x)))
  · intro n
    simp only [levelClamp, one_div]
    apply max_le _ (min_le_left _ _)
    have h : 0 ≤ 1 / (n + 1 : ℝ) := by positivity
    simpa only [one_div] using (show c - 1 / (n + 1 : ℝ) ≤ c + 1 / (n + 1 : ℝ) by linarith)

lemma borelAction_eq_levelClamp (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π : Fin k → X → ℝ)
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) (c : ℝ)
    (hc : ∀ x, f x ≠ 0 → π i x = c) {ε : ℝ} (hε : 0 < ε) :
    borelAction μ hT f π =
      borelAction μ hT f (Function.update π i (levelClamp c ε (π i))) := by
  classical
  obtain ⟨K, hK⟩ := hπ i
  let v := levelClamp c ε (π i)
  let w : X → ℝ := fun x => π i x - v x
  let ζ : X → ℝ := fun x => max 0 (ε - dist (π i x) c)
  have hv : LipschitzWith K v := levelClamp_lipschitz hK
  have hw : ∃ L : ℝ≥0, LipschitzWith L w := ⟨K + K, hK.sub hv⟩
  have hζ : BoundedLip ζ := by
    apply Foundations.boundedLip_of_lipschitz
    have hd : LipschitzWith K (fun x => dist (π i x) c) :=
      by simpa only [one_mul, Function.comp_def] using (LipschitzWith.dist_left c).comp hK
    simpa using ((LipschitzWith.const ε).sub hd).const_max 0
  let ρ := Function.update π i w
  have hρ : ∀ j, ∃ L : ℝ≥0, LipschitzWith L (ρ j) := by
    intro j
    by_cases hji : j = i
    · simpa [ρ, hji] using hw
    · simpa [ρ, Function.update_of_ne hji] using hπ j
  have hz : borelAction μ hT (fun x => f x * ζ x) ρ = 0 := by
    apply borelAction_locality_mul μ hT hμ hf hζ ρ hρ
    refine ⟨i, {x | dist (π i x) c < ε}, 0,
      isOpen_lt (hK.continuous.dist continuous_const) continuous_const, ?_, ?_⟩
    · intro x hx
      change max 0 (ε - dist (π i x) c) ≠ 0 at hx
      change dist (π i x) c < ε
      by_contra h
      exact hx (max_eq_left (by linarith [le_of_not_gt h]))
    · intro x hx
      simp only [ρ, Function.update_self]
      change π i x - levelClamp c ε (π i) x = 0
      rw [levelClamp_eq (by simpa [Real.dist_eq] using hx), sub_self]
  have heq : (fun x => f x * ζ x) = ε • f := by
    funext x
    by_cases hfx : f x = 0
    · simp [hfx]
    · simp [ζ, hc x hfx, max_eq_right hε.le, mul_comm]
  rw [heq, borelAction_smul μ hT hf ρ ε hρ] at hz
  have hzero : borelAction μ hT f ρ = 0 := (mul_eq_zero.mp hz).resolve_left hε.ne'
  have hlin := borelAction_linearCoord μ hT hμ hf π hπ i v ⟨K, hv⟩ 1 (-1)
  have hform : Function.update π i (fun x => 1 * π i x + -1 * v x) = ρ := by
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg]
    rfl
  rw [hform, hzero] at hlin
  linarith

theorem borelAction_locality_level (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {f : X → ℝ} (hf : Integrable f μ) (π : Fin k → X → ℝ)
    (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j)) (i : Fin k) (c : ℝ)
    (hc : ∀ x, f x ≠ 0 → π i x = c) : borelAction μ hT f π = 0 := by
  classical
  let πs (n : ℕ) := Function.update π i (levelClamp c (1 / (n + 1)) (π i))
  let π₀ := Function.update π i (fun _ => c)
  have hLip : ∀ j, ∃ K : ℝ≥0, ∀ n, LipschitzWith K (πs n j) := by
    intro j
    by_cases hji : j = i
    · obtain ⟨K,hK⟩ := hπ i
      exact ⟨K, fun _ => by simpa [πs, hji] using levelClamp_lipschitz hK⟩
    · obtain ⟨K,hK⟩ := hπ j
      exact ⟨K, fun _ => by simpa [πs, Function.update_of_ne hji] using hK⟩
  have hpt : ∀ j x, Tendsto (fun n => πs n j x) atTop (𝓝 (π₀ j x)) := by
    intro j x
    by_cases hji : j = i
    · simpa [πs, π₀, hji] using levelClamp_tendsto c (π i) x
    · simp [πs, π₀, Function.update_of_ne hji]
  have hlim := borelAction_sequentialContinuity μ hT hμ hf π₀ πs hLip hpt
  have heq (n : ℕ) : borelAction μ hT f (πs n) = borelAction μ hT f π :=
    (borelAction_eq_levelClamp μ hT hμ hf π hπ i c hc (by positivity)).symm
  simp only [heq] at hlim
  have heq' := tendsto_nhds_unique hlim (tendsto_const_nhds)
  have hπ₀ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π₀ j) := by
    intro j
    by_cases hji : j = i
    · exact ⟨0, by simp [π₀, hji]⟩
    · simpa [π₀, Function.update_of_ne hji] using hπ j
  rw [← heq']
  exact borelAction_const_coord μ hT hμ hf π₀ hπ₀ i c (by simp [π₀])

end CAT0Fillings.BorelCoefficients
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_Carriers
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X]

lemma borelAction_mul_zero_of_lip {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : ∀ b π, Admissible b π → T (fun x => w x * b x) π = 0)
    {f : X → ℝ} (hf : Integrable f (currentMassMeasure hT))
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction (currentMassMeasure hT) hT (fun x => w x * f x) π = 0 := by
  let μ := currentMassMeasure hT
  obtain ⟨B,hB⟩ := hw.2
  have hbnd : ∀ᵐ x ∂μ, ‖w x‖ ≤ B := Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hB x
  have hfi : Integrable (fun x => w x * f x) μ := by
    simpa only [mul_comm] using hf.mul_bdd hw.continuous.aestronglyMeasurable hbnd
  obtain ⟨g,hg⟩ := exists_lipschitz_approximation μ hf
  have hgi n : Integrable (fun x => w x * (g n).val x) μ :=
    integrable_boundedLip μ (hw.mul (g n).property)
  have hlim : Tendsto (fun n => ∫ x, |w x * (g n).val x - w x * f x| ∂μ) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg fun x => abs_nonneg _) (fun n => ?_)
      (by simpa only [mul_zero] using hg.const_mul B)
    rw [←integral_const_mul]
    apply integral_mono ((hgi n).sub hfi).abs (((integrable_boundedLip μ (g n).property).sub hf).abs.const_mul B)
    intro x
    change |w x * (g n).val x - w x * f x| ≤ B * |(g n).val x - f x|
    rw [←mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
  have ht := borelAction_tendsto μ hT (currentMassMeasure_controls hT) hfi hgi hlim π hπ
  have he n : borelAction μ hT (fun x => w x * (g n).val x) π = 0 := by
    rw [borelAction_eq μ hT (currentMassMeasure_controls hT) ⟨hw.mul (g n).property,hπ⟩]
    exact hz _ _ ⟨(g n).property,hπ⟩
  simp only [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma massMeasure_nonzero_zero_of_mul_zero {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : ∀ b π, Admissible b π → T (fun x => w x * b x) π = 0) :
    currentMassMeasure hT {x | w x ≠ 0} = 0 := by
  let E (n : ℕ) : Set X := {x | 1 / (n+1:ℝ) ≤ |w x|}
  have hE n : MeasurableSet (E n) := measurableSet_le measurable_const hw.continuous.abs.measurable
  have hzero n : restrictCurrent hT (E n) = 0 := by
    funext b π
    by_cases hab : Admissible b π
    · obtain ⟨B,hB⟩ := hab.1.2
      let f : X → ℝ := (E n).indicator (fun x => b x / w x)
      have hfm : Measurable f := (hab.1.continuous.measurable.div hw.continuous.measurable).indicator (hE n)
      have hfB x : ‖f x‖ ≤ max B 0 * (n+1:ℝ) := by
        by_cases hx : x ∈ E n
        · have hw0 : 0 < |w x| := lt_of_lt_of_le (by positivity : (0:ℝ) < 1/(n+1:ℝ)) hx
          simp only [f,indicator_of_mem hx,Real.norm_eq_abs,abs_div]
          apply (div_le_iff₀ hw0).mpr
          have hc : (1:ℝ) ≤ (n+1:ℝ)*|w x| := by
            simpa only [mul_comm] using (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mp hx
          calc |b x| ≤ max B 0 := (hB x).trans (le_max_left _ _)
            _ ≤ max B 0 * ((n+1:ℝ)*|w x|) := le_mul_of_one_le_right (le_max_right _ _) hc
            _ = _ := by ring
        · simp only [f,indicator_of_notMem hx,norm_zero]
          positivity
      have hfi : Integrable f (currentMassMeasure hT) :=
        (integrable_const (max B 0 * (n+1:ℝ))).mono' hfm.aestronglyMeasurable (Eventually.of_forall hfB)
      rw [restrictCurrent_apply hT (E n) hab]
      have he : (E n).indicator b = fun x => w x * f x := by
        funext x
        by_cases hx : x ∈ E n
        · have hw0 : w x ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity : (0:ℝ)<1/(n+1:ℝ)) hx)
          simp only [f,indicator_of_mem hx]
          field_simp
        · simp [f,hx]
      rw [he]
      exact borelAction_mul_zero_of_lip hT hw hz hfi π hab.2
    · simp [restrictCurrent,hab]
  have hμ n : currentMassMeasure hT (E n) = 0 := by
    have hm := restriction_mass hT (hE n)
    rw [hzero n] at hm
    have hm0 : mass (0 : Functional X k) = 0 := mass_zero k
    rw [hm0] at hm
    exact (ENNReal.toReal_eq_zero_iff _).mp hm.symm |>.resolve_right (measure_ne_top _ _)
  have hsub : {x | w x ≠ 0} ⊆ ⋃ n, E n := by
    intro x hx
    have hw0 : 0 < |w x| := abs_pos.mpr hx
    obtain ⟨n,hn⟩ := exists_nat_gt (1/|w x|)
    apply mem_iUnion.mpr
    refine ⟨n,?_⟩
    change 1 / (n+1:ℝ) ≤ |w x|
    apply (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mpr
    have hh := (div_lt_iff₀ hw0).mp hn
    nlinarith
  exact measure_mono_null hsub (measure_iUnion_null fun n => hμ n)

lemma mul_action_zero_of_massMeasure_nonzero_zero {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    T (fun x => w x * b x) π = 0 := by
  have he : (fun x => w x * b x) =ᵐ[currentMassMeasure hT] 0 := by
    filter_upwards [show ∀ᵐ x ∂currentMassMeasure hT, w x = 0 from ae_iff.mpr hz] with x hx
    simp [hx]
  rw [←borelAction_eq _ hT (currentMassMeasure_controls hT) ⟨hw.mul hab.1,hab.2⟩,
    borelAction_congr_ae _ hT he,borelAction_of_integrable _ hT (integrable_zero X ℝ _) π hab.2]
  simp

lemma boundary_mul_zero_of_massMeasure {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    boundarySucc T (fun x => w x * b x) π = 0 := by
  let E : Set X := {x | w x = 0}
  have hE : MeasurableSet E := hw.continuous.measurable (measurableSet_singleton 0)
  have he : (fun _ : X => (1:ℝ)) =ᵐ[currentMassMeasure hT] E.indicator (fun _ => (1:ℝ)) := by
    filter_upwards [show ∀ᵐ x ∂currentMassMeasure hT, w x = 0 from ae_iff.mpr hz] with x hx
    exact (indicator_of_mem (show x ∈ E from hx) (fun _ : X => (1:ℝ))).symm
  let σ := Matrix.vecCons (fun x => w x * b x) π
  have hσ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (σ j) :=
    fun j => Fin.cases (hw.mul hab.1).1 (fun i => hab.2 i) j
  rw [boundarySucc,ite_eq_left ⟨hw.mul hab.1,hab.2⟩]
  change T (fun _ => 1) σ = 0
  rw [←borelAction_eq _ hT (currentMassMeasure_controls hT) ⟨BoundedLip.const 1,hσ⟩,
    borelAction_congr_ae _ hT he]
  apply borelAction_locality_level _ hT (currentMassMeasure_controls hT)
    ((integrable_const (1:ℝ)).indicator hE) σ hσ 0 0
  intro x hx
  have hxE : x ∈ E := mem_of_indicator_ne_zero hx
  change w x * b x = 0
  rw [show w x = 0 from hxE,zero_mul]

lemma massMeasure_boundary_nonzero_zero {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0) :
    currentMassMeasure hB {x | w x ≠ 0} = 0 := by
  apply massMeasure_nonzero_zero_of_mul_zero hB hw
  intro b π hab
  exact boundary_mul_zero_of_massMeasure hT hw hz hab

lemma massMeasure_restrict_nonzero_zero {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {E : Set X} (hE : MeasurableSet E)
    {w : X → ℝ} (hz : currentMassMeasure hT {x | w x ≠ 0} = 0) :
    currentMassMeasure (restrictCurrent_isMetricCurrent hT hE) {x | w x ≠ 0} = 0 := by
  rw [restriction_massMeasure hT hE]
  exact le_antisymm ((Measure.restrict_le_self _).trans_eq hz) bot_le

lemma massMeasure_superlevelSlice_nonzero_zero {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hB : IsMetricCurrent (boundarySucc T))
    {u : X → ℝ} (hu : Continuous u) (t : ℝ)
    (hS : IsMetricCurrent (superlevelSlice hT hB u t))
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure hT {x | w x ≠ 0} = 0) :
    currentMassMeasure hS {x | w x ≠ 0} = 0 := by
  have hE : MeasurableSet {x | t < u x} := measurableSet_lt measurable_const hu.measurable
  have hBT := massMeasure_boundary_nonzero_zero hT hB hw hz
  have hRT := massMeasure_restrict_nonzero_zero hT hE hz
  have hRB := massMeasure_restrict_nonzero_zero hB hE hBT
  apply massMeasure_nonzero_zero_of_mul_zero hS hw
  intro b π hab
  change restrictCurrent hB _ (fun x => w x * b x) π -
    boundarySucc (restrictCurrent hT _) (fun x => w x * b x) π = 0
  rw [mul_action_zero_of_massMeasure_nonzero_zero (restrictCurrent_isMetricCurrent hB hE) hw hRB hab,
    boundary_mul_zero_of_massMeasure (restrictCurrent_isMetricCurrent hT hE) hw hRT hab,sub_self]

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slices_FullCarrier
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
lemma boundedLip_sub_const [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ) :
    BoundedLip (fun x => u x-t) :=
  boundedLip_of_lipschitz (hu.1.choose_spec.sub (LipschitzWith.const t))

omit [Nonempty X] in
lemma weightedCurrent_boundedLip_isMetricCurrent [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w) :
    IsMetricCurrent (weightedCurrent (currentMassMeasure hT) hT w) := by
  obtain ⟨B,hB⟩ := hw.2
  apply weightedCurrent_isMetricCurrent _ hT (currentMassMeasure_controls hT)
    (integrable_boundedLip _ hw) (M := ⟨max B 0,le_max_right _ _⟩)
  exact Eventually.of_forall fun x => (hB x).trans (le_max_left _ _)

omit [Nonempty X] in
lemma weightedCurrent_boundedLip_apply [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {w : X → ℝ} (hw : BoundedLip w)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    weightedCurrent (currentMassMeasure hT) hT w b π = T (fun x => w x * b x) π := by
  rw [weightedCurrent,ite_eq_left hab]
  exact borelAction_eq _ hT (currentMassMeasure_controls hT) ⟨hw.mul hab.1,hab.2⟩

lemma massMeasure_normalSlice_nonzero_zero {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) {u : X → ℝ} (hu : Continuous u) (t : ℝ)
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure h.metric {x | w x ≠ 0} = 0) :
    currentMassMeasure (normalSlice_approx h u t).metric {x | w x ≠ 0} = 0 := by
  classical
  by_cases hs : NormalApprox k (superlevelSlice h.normal.1 h.normal.2 u t)
  · have he : normalSlice h u t = superlevelSlice h.normal.1 h.normal.2 u t := ite_eq_left hs
    apply massMeasure_nonzero_zero_of_mul_zero _ hw
    intro b π hab
    rw [he]
    exact mul_action_zero_of_massMeasure_nonzero_zero hs.metric hw
      (massMeasure_superlevelSlice_nonzero_zero h.normal.1 h.normal.2 hu t hs.metric hw hz) hab
  · have he : normalSlice h u t = 0 := ite_eq_right hs
    apply massMeasure_nonzero_zero_of_mul_zero _ hw
    intro b π hab
    rw [he]
    rfl

lemma massMeasure_fullSlice_nonzero_zero {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (π : Fin k → X → ℝ) (hπ : ∀ i, Continuous (π i))
    {w : X → ℝ} (hw : BoundedLip w)
    (hz : currentMassMeasure h.metric {x | w x ≠ 0} = 0) (z : Euc k) :
    currentMassMeasure (fullSlice_approx h π z).metric {x | w x ≠ 0} = 0 := by
  induction k with
  | zero => exact hz
  | succ k ih =>
    exact ih (normalSlice_approx h (π 0) (Prism.split k z).1) (Fin.tail π)
      (fun i => hπ i.succ) (massMeasure_normalSlice_nonzero_zero h (hπ 0) _ hw hz) (Prism.split k z).2

lemma ae_superlevelSlice_weighted_integral {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π)
    {φ : ℝ → ℝ} (hφ : BoundedLip (φ ∘ u)) :
    ∀ᵐ t : ℝ, superlevelSlice hT.1 hT.2.2.1 u t (fun x => φ (u x)*b x) π =
      φ t * superlevelSlice hT.1 hT.2.2.1 u t b π := by
  obtain ⟨S,G,hG,hG0,hS,hGI,hact,hweight⟩ := integerRectifiable_scalar_coarea hT.1 hT.2.1 hX hK
  filter_upwards [ae_superlevelSlice_eq_coarea hT.1 hT.2.1 hT.2.2.1
    (boundedLip_of_lipschitz hK) (hS.mono fun _ ht => ht.1) hact hweight,hweight b π hab φ hφ] with t he ht
  simpa only [he] using ht

lemma NormalApprox.ae_superlevelSlice_weighted {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π)
    {φ : ℝ → ℝ} (hφ : BoundedLip (φ ∘ u)) :
    ∀ᵐ t : ℝ, superlevelSlice h.normal.1 h.normal.2 u t (fun x => φ (u x)*b x) π =
      φ t * superlevelSlice h.normal.1 h.normal.2 u t b π := by
  have hcopy := h
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hcopy
  obtain ⟨ψ,hψ,μs,νs,μ,ν,hμs,hμ,hνs,hν,hμlim,hνlim⟩ :=
    exists_joint_weak_controlling_subsequence (fun j => (hTs j).1)
      (fun j => (hTs j).2.2.1) C C hM hN hlim (boundarySucc_weak_limit hlim)
  have hweak := ae_superlevelSlice_weak_tendsto (fun j => (hTs (ψ j)).1) h.normal.1
    (fun j => (hTs (ψ j)).2.2.1) h.normal.2 μs νs μ ν hμs hμ hνs hν hμlim hνlim
    (fun b π => (hlim b π).comp hψ.tendsto_atTop) (boundedLip_of_lipschitz hK)
  have ht := ae_all_iff.mpr (fun j => ae_superlevelSlice_weighted_integral (hTs (ψ j)) hX hK hab hφ)
  filter_upwards [hweak,ht] with t hwt he
  have hl := hwt (fun x => φ (u x)*b x) π
  have hr := (hwt b π).const_mul (φ t)
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

lemma ae_normalSlice_mul_level {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} (hu : BoundedLip u)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hab : Admissible b π) :
    ∀ᵐ t : ℝ, normalSlice h u t (fun x => (u x-t)*b x) π = 0 := by
  have hs := h.ae_superlevelSlice_weighted hX hu.1.choose_spec hab
    (φ := id) (by simpa only [Function.comp_def,id_eq] using hu)
  filter_upwards [ae_normalSlice_eq h hX hu.1.choose_spec,hs] with t he ht
  have hlin := (normalSlice_approx h u t).metric.linearFirst (fun x => u x*b x) b π 1 (-t) (hu.mul hab.1) hab.1 hab.2
  have hw : (fun x => 1*(u x*b x)+ -t*b x) = (fun x => (u x-t)*b x) := by funext x;ring
  rw [hw] at hlin
  rw [hlin,he]
  simp only [id_eq] at ht
  rw [ht]
  simp only [one_mul]
  ring

theorem ae_normalSlice_mass_level {k : ℕ} {T : Functional X (k+1)}
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    {u : X → ℝ} (hu : BoundedLip u) :
    ∀ᵐ t : ℝ, currentMassMeasure (normalSlice_approx h u t).metric {x | u x ≠ t} = 0 := by
  let W (t : ℝ) := weightedCurrent (currentMassMeasure (normalSlice_approx h u t).metric)
    (normalSlice_approx h u t).metric (fun x => u x-t)
  have hW t : IsMetricCurrent (W t) :=
    weightedCurrent_boundedLip_isMetricCurrent _ (boundedLip_sub_const hu t)
  have he : ∀ᵐ t : ℝ, W t = (0 : Functional X k) := by
    apply ae_eq_of_ae_test_eq volume (Eventually.of_forall hW) (Eventually.of_forall fun _ => isMetricCurrent_zero k)
    intro b π hab
    filter_upwards [ae_normalSlice_mul_level h hX hu hab] with t ht
    exact (weightedCurrent_boundedLip_apply _ (boundedLip_sub_const hu t) hab).trans ht
  filter_upwards [he] with t ht
  have hh : currentMassMeasure (normalSlice_approx h u t).metric {x | u x-t ≠ 0} = 0 := by
    apply massMeasure_nonzero_zero_of_mul_zero _ (boundedLip_sub_const hu t)
    intro b π hab
    rw [←weightedCurrent_boundedLip_apply (normalSlice_approx h u t).metric (boundedLip_sub_const hu t) hab]
    exact congrFun (congrFun ht b) π
  simpa only [sub_ne_zero] using hh

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma level_eval_of_carrier {T : Functional X 0} (hT : IsMetricCurrent T)
    {u : X → ℝ} (hu : BoundedLip u) (t : ℝ)
    (hz : currentMassMeasure hT {x | u x ≠ t} = 0)
    {b : X → ℝ} (hb : BoundedLip b) (σ : Fin 0 → X → ℝ) :
    T (fun x => u x*b x) σ = t*T b σ := by
  have hh := mul_action_zero_of_massMeasure_nonzero_zero hT (boundedLip_sub_const hu t)
    (by simpa only [sub_ne_zero] using hz) (show Admissible b σ from ⟨hb,fun i => Fin.elim0 i⟩)
  have hl := hT.linearFirst (fun x => u x*b x) b σ 1 (-t) (hu.mul hb) hb (fun i => Fin.elim0 i)
  have he : (fun x => 1*(u x*b x)+ -t*b x) = (fun x => (u x-t)*b x) := by funext x;ring
  rw [he,hh] at hl
  linarith

lemma ae_fullSlice_level_eval {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) (i : Fin k)
    {b : X → ℝ} (hb : BoundedLip b) (σ : Fin 0 → X → ℝ) :
    ∀ᵐ z : Euc k, fullSlice h π z (fun x => π i x*b x) σ = z i*fullSlice h π z b σ := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    let P (z : Euc (k+1)) := fullSlice h π z (fun x => π i x*b x) σ = z i*fullSlice h π z b σ
    have hm : MeasurableSet {z | P z} := measurableSet_eq_fun
      (measurable_fullSlice h π hπ _ _) (((PiLp.continuous_apply 2 _ i).measurable).mul (measurable_fullSlice h π hπ b σ))
    have hp : ∀ᵐ p : ℝ × Euc k ∂volume.prod volume, P ((Prism.split k).symm p) := by
      apply (Measure.ae_prod_iff_ae_ae (hm.preimage (Prism.split k).symm.continuous.measurable)).mpr
      dsimp only [P,mem_ofPred_eq]
      refine Fin.cases ?_ (fun j => ?_) i
      · filter_upwards [ae_normalSlice_mass_level h hX (hπ 0)] with t ht
        filter_upwards [] with z
        exact level_eval_of_carrier (fullSlice_approx (normalSlice_approx h (π 0) t) (Fin.tail π) z).metric
          (hπ 0) t
          (by simpa only [sub_ne_zero] using (massMeasure_fullSlice_nonzero_zero
            (normalSlice_approx h (π 0) t) (Fin.tail π) (fun j => (hπ j.succ).1.choose_spec.continuous)
            (boundedLip_sub_const (hπ 0) t) (by simpa only [sub_ne_zero] using ht) z)) hb σ
      · exact Eventually.of_forall fun t => ih (normalSlice_approx h (π 0) t)
          (Fin.tail π) (fun j => hπ j.succ) j
    have hh := (Prism.split_measurePreserving k).quasiMeasurePreserving.ae hp
    simpa only [Measure.volume_eq_prod,Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using hh

lemma ae_fullSlice_mass_level {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) (i : Fin k) :
    ∀ᵐ z : Euc k, currentMassMeasure (fullSlice_approx h π z).metric {x | π i x ≠ z i} = 0 := by
  let W (z : Euc k) := weightedCurrent (currentMassMeasure (fullSlice_approx h π z).metric)
    (fullSlice_approx h π z).metric (fun x => π i x-z i)
  have hW z : IsMetricCurrent (W z) :=
    weightedCurrent_boundedLip_isMetricCurrent _ (boundedLip_sub_const (hπ i) (z i))
  have he : ∀ᵐ z : Euc k, W z = (0 : Functional X 0) := by
    apply ae_eq_of_ae_test_eq volume (Eventually.of_forall hW) (Eventually.of_forall fun _ => isMetricCurrent_zero 0)
    intro b σ hab
    filter_upwards [ae_fullSlice_level_eval h hX π hπ i hab.1 σ] with z hz
    change weightedCurrent _ (fullSlice_approx h π z).metric _ b σ = 0
    rw [weightedCurrent_boundedLip_apply (fullSlice_approx h π z).metric (boundedLip_sub_const (hπ i) (z i)) hab]
    have hl := (fullSlice_approx h π z).metric.linearFirst (fun x => π i x*b x) b σ 1 (-(z i))
      ((hπ i).mul hab.1) hab.1 hab.2
    have hw : (fun x => 1*(π i x*b x)+ -(z i)*b x) = (fun x => (π i x-z i)*b x) := by funext x;ring
    rw [hw,hz] at hl
    simpa only [Pi.zero_apply] using hl.trans (by ring)
  filter_upwards [he] with z hz
  have hh : currentMassMeasure (fullSlice_approx h π z).metric {x | π i x-z i ≠ 0} = 0 := by
    apply massMeasure_nonzero_zero_of_mul_zero _ (boundedLip_sub_const (hπ i) (z i))
    intro b σ hab
    rw [←weightedCurrent_boundedLip_apply (fullSlice_approx h π z).metric (boundedLip_sub_const (hπ i) (z i)) hab]
    exact congrFun (congrFun hz b) σ
  simpa only [sub_ne_zero] using hh

lemma ae_fullSlice_mass_fiber {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i)) :
    ∀ᵐ z : Euc k, currentMassMeasure (fullSlice_approx h π z).metric {x | coordinateMap π x ≠ z} = 0 := by
  filter_upwards [ae_all_iff.mpr (fun i => ae_fullSlice_mass_level h hX π hπ i)] with z hz
  apply measure_mono_null (t := ⋃ i, {x | π i x ≠ z i}) ?_ (measure_iUnion_null fun i => hz i)
  intro x hx
  apply mem_iUnion.mpr
  by_contra hn
  push Not at hn
  exact hx (by ext i; simpa only [mem_ofPred_eq,not_not] using hn i)

lemma ae_fullSlice_weighted {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {φ : Euc k → ℝ} (hφπ : BoundedLip (φ ∘ coordinateMap π))
    {b : X → ℝ} (hb : BoundedLip b) (σ : Fin 0 → X → ℝ) :
    ∀ᵐ z : Euc k, fullSlice h π z (fun x => φ (coordinateMap π x)*b x) σ =
      φ z*fullSlice h π z b σ := by
  filter_upwards [ae_fullSlice_mass_fiber h hX π hπ] with z hz
  apply level_eval_of_carrier (fullSlice_approx h π z).metric hφπ (φ z) ?_ hb σ
  apply measure_mono_null (t := {x | coordinateMap π x ≠ z}) ?_ hz
  intro x hx he
  exact hx (congrArg φ he)

lemma fullSlice_weighted_integral {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {φ : Euc k → ℝ} (hφπ : BoundedLip (φ ∘ coordinateMap π))
    {b : X → ℝ} (hb : BoundedLip b) :
    Integrable (fun z : Euc k => φ z*fullSlice h π z b (fun j => Fin.elim0 j)) ∧
      T (fun x => φ (coordinateMap π x)*b x) π =
        ∫ z : Euc k, φ z*fullSlice h π z b (fun j => Fin.elim0 j) := by
  have he := ae_fullSlice_weighted h hX π hπ hφπ hb (fun j => Fin.elim0 j)
  refine ⟨(fullSlice_eval_integrable h hX π hπ (hφπ.mul hb) _).congr he,?_⟩
  exact (fullSlice_action_integral h hX π hπ (hφπ.mul hb)).trans (integral_congr_ae he)

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_WeakCalculus
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma linear_pi_expansion (L : (Fin k → ℝ) →L[ℝ] ℝ) (v : Fin k → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  have he : v = ∑ i, v i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]

lemma ae_fderivWithin_scalar_multi
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) :
    ∀ᵐ z ∂volume.restrict C.domain,
      fderivWithin ℝ (C.scalar (fun x => φ (fun i => π i x))) C.domain z =
        (dφ (fun i => C.scalar (π i) z)).comp
          (ContinuousLinearMap.pi (fun i => fderivWithin ℝ (C.scalar (π i)) C.domain z)) := by
  have hall : ∀ᵐ z ∂volume.restrict C.domain,
      ∀ i, DifferentiableWithinAt ℝ (C.scalar (π i)) C.domain z :=
    ae_all_iff.mpr fun i => C.ae_differentiableWithinAt_scalar (hπ i).choose_spec
  filter_upwards [ae_uniqueDiffWithinAt volume C.domain,ae_restrict_mem C.borel,hall] with z hz hzs hD
  have hPi := hasFDerivWithinAt_pi.mpr (fun i => (hD i).hasFDerivWithinAt)
  have hcomp := (hφ (fun i => C.scalar (π i) z)).comp_hasFDerivWithinAt z hPi
  have he : EqOn (C.scalar (fun x => φ (fun i => π i x)))
      (fun z => φ (fun i => C.scalar (π i) z)) C.domain := by
    intro y hy
    simp only [C.scalar_eq hy]
  exact (hcomp.congr he (he hzs)).fderivWithin hz

lemma ae_jacobian_update_multi
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) (i : Fin k) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.jacobian (Function.update π i (fun x => φ (fun j => π j x))) z =
        dφ (fun j => C.scalar (π j) z) (Pi.single i 1) * C.jacobian π z := by
  filter_upwards [C.ae_fderivWithin_scalar_multi π hπ hφ] with z hz
  rw [C.jacobian_update,hz]
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun a j =>
    fderivWithin ℝ (C.scalar (π a)) C.domain z (EuclideanSpace.single j 1)
  let a : Fin k → ℝ := fun j => dφ (fun l => C.scalar (π l) z) (Pi.single j 1)
  have he : (fun j => ((dφ (fun i => C.scalar (π i) z)).comp
      (ContinuousLinearMap.pi (fun i => fderivWithin ℝ (C.scalar (π i)) C.domain z)))
        (EuclideanSpace.single j 1)) = ∑ l, a l • M l := by
    ext j
    rw [ContinuousLinearMap.comp_apply,linear_pi_expansion]
    simp only [ContinuousLinearMap.pi_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,M,a,Matrix.of_apply]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  exact Matrix.det_updateRow_sum M i a

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.Foundations
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [BorelSpace X] [CompactSpace X] in
lemma IntegerRectifiable.apply_update_multi [BorelSpace X] [CompactSpace X]
    {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {b : X → ℝ} (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) (i : Fin k)
    (hφπ : BoundedLip (fun x => φ (fun j => π j x)))
    (hdπ : BoundedLip (fun x => dφ (fun j => π j x) (Pi.single i 1))) :
    T b (Function.update π i (fun x => φ (fun j => π j x))) =
      T (fun x => b x * dφ (fun j => π j x) (Pi.single i 1)) π := by
  classical
  obtain ⟨C,_,_,_,hrep⟩ := hT
  rw [hrep,hrep]
  apply tsum_congr
  intro q
  have had : Admissible b (Function.update π i (fun x => φ (fun j => π j x))) := by
    refine ⟨hb,?_⟩
    intro j
    by_cases he : j = i
    · simpa [he] using hφπ.1
    · simpa only [Function.update_of_ne he] using hπ j
  rw [IntegerChart.action,ite_eq_left had,IntegerChart.action,ite_eq_left ⟨hb.mul hdπ,hπ⟩]
  apply integral_congr_ae
  filter_upwards [(C q).ae_jacobian_update_multi π hπ hφ i,ae_restrict_mem (C q).borel] with z hz hzs
  rw [hz]
  simp only [(C q).scalar_eq hzs]
  ring

end CAT0Fillings.Foundations

namespace CAT0Fillings.Slicing
open Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [Nonempty X] in
lemma NormalApprox.product_rule [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
    (hT : NormalApprox (k+1) T) {b f : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    T b (Matrix.vecCons f π) + T f (Matrix.vecCons b π) =
      boundarySucc T (fun x => b x * f x) π := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hT
  have hleft := (hlim b (Matrix.vecCons f π)).add (hlim f (Matrix.vecCons b π))
  have hright := boundarySucc_weak_limit hlim (fun x => b x * f x) π
  have he j := IntegerRectifiable.product_rule (hTs j).2.1 hb hf π hπ
  simp only [he] at hleft
  exact tendsto_nhds_unique hleft hright

omit [Nonempty X] in
lemma NormalApprox.apply_update_multi [Nonempty X] {k : ℕ} {T : Functional X k}
    (hT : NormalApprox k T) {b : X → ℝ} (hb : BoundedLip b)
    (π : Fin k → X → ℝ) (hπ : ∀ j, ∃ K : ℝ≥0, LipschitzWith K (π j))
    {φ : (Fin k → ℝ) → ℝ} {dφ : (Fin k → ℝ) → (Fin k → ℝ) →L[ℝ] ℝ}
    (hφ : ∀ z, HasFDerivAt φ (dφ z) z) (i : Fin k)
    (hφπ : BoundedLip (fun x => φ (fun j => π j x)))
    (hdπ : BoundedLip (fun x => dφ (fun j => π j x) (Pi.single i 1))) :
    T b (Function.update π i (fun x => φ (fun j => π j x))) =
      T (fun x => b x * dφ (fun j => π j x) (Pi.single i 1)) π := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hT
  have hleft := hlim b (Function.update π i (fun x => φ (fun j => π j x)))
  have hright := hlim (fun x => b x * dφ (fun j => π j x) (Pi.single i 1)) π
  have hrect j : IntegerRectifiable (Ts j) := by
    cases k with
    | zero => exact (hTs j).2
    | succ k => exact (hTs j).2.1
  have he j := IntegerRectifiable.apply_update_multi (hrect j) hb π hπ hφ i hφπ hdπ
  simp only [he] at hleft
  exact tendsto_nhds_unique hleft hright

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma NormalApprox.apply_permute [BorelSpace X] [CompactSpace X] [Nonempty X]
    {k : ℕ} {T : Functional X k}
    (hT : NormalApprox k T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (hab : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    T b (π ∘ σ) = (Equiv.Perm.sign σ : ℤ)*T b π := by
  obtain ⟨C,Ts,hTs,hM,hN,hlim⟩ := hT
  have hl := hlim b (π ∘ σ)
  have hr := (hlim b π).const_mul ((Equiv.Perm.sign σ : ℤ):ℝ)
  have hrect j : IntegerRectifiable (Ts j) := by
    cases k with
    | zero => exact (hTs j).2
    | succ k => exact (hTs j).2.1
  have he j := IntegerRectifiable.apply_permute (hrect j) hab σ
  simp only [he] at hl
  exact tendsto_nhds_unique hl hr

lemma NormalApprox.abs_apply_permute {k : ℕ} {T : Functional X k}
    (hT : NormalApprox k T) {b : X → ℝ} {π : Fin k → X → ℝ}
    (hab : Admissible b π) (σ : Equiv.Perm (Fin k)) :
    |T b (π ∘ σ)| = |T b π| := by
  rw [hT.apply_permute hab σ,abs_mul,abs_unit_intCast,one_mul]

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_BV_JointPoincare
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV

lemma scalar_convolution_comm {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddLeftInvariant]
    [μ.IsNegInvariant] (f g : E → ℝ) :
    (f ⋆[lsmul ℝ ℝ, μ] g) = (g ⋆[lsmul ℝ ℝ, μ] f) := by
  have he : (lsmul ℝ ℝ).flip = lsmul ℝ ℝ := by ext; simp
  simpa only [he] using (convolution_flip (L := lsmul ℝ ℝ) (f := g) (g := f) (μ := μ))

lemma shrinkingBump_tendsto {E : Type*} [NormedAddCommGroup E] :
    Tendsto (fun j => (shrinkingBump (E := E) j).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump,mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients JointBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma coordinateMap_lipschitz {k : ℕ} (π : Fin k → X → ℝ) {K : ℝ≥0}
    (hπ : ∀ i, LipschitzWith K (π i)) : ∃ L, LipschitzWith L (coordinateMap π) := by
  have hp : LipschitzWith K (fun x i => π i x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).mpr (fun i => (hπ i).dist_le_mul x y)
  exact ⟨_,(parameterEquiv k).toContinuousLinearMap.lipschitz.comp hp⟩

end CAT0Fillings.Slicing
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Ascoli
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter Metric

namespace CAT0Fillings.JointBV
universe u
variable {ι : Type*} {α β : Type u} [PseudoMetricSpace α] [PseudoMetricSpace β]

lemma totallyBounded_range_of_control {f : ι → α} {g : ι → β}
    (hg : TotallyBounded (range g))
    (hcontrol : ∀ ε > 0, ∃ δ > 0, ∀ i j, dist (g i) (g j) < δ → dist (f i) (f j) < ε) :
    TotallyBounded (range f) := by
  classical
  apply Metric.totallyBounded_of_finite_discretization
  intro ε hε
  obtain ⟨δ,hδ,hc⟩ := hcontrol ε hε
  obtain ⟨s,hs,hfin,hcover⟩ := Metric.finite_approx_of_totallyBounded hg (δ/2) (half_pos hδ)
  have : Fintype s := hfin.fintype
  have hnear (i : ι) : ∃ y : s, dist (g i) y < δ/2 := by
    have := hcover (mem_range_self i)
    simp only [mem_iUnion,mem_ball] at this
    obtain ⟨y,hy,hiy⟩ := this
    exact ⟨⟨y,hy⟩,hiy⟩
  choose c hc' using hnear
  let pick (x : range f) : ι := x.property.choose
  have hp (x : range f) : f (pick x) = x := x.property.choose_spec
  refine ⟨s,inferInstance,fun x => c (pick x),?_⟩
  intro x y he
  change c (pick x) = c (pick y) at he
  rw [←hp x,←hp y]
  apply hc
  calc dist (g (pick x)) (g (pick y)) ≤
      dist (g (pick x)) (c (pick x)) + dist (g (pick y)) (c (pick x)) := dist_triangle_right _ _ _
    _ < δ/2+δ/2 := add_lt_add (hc' _) (by rw [he]; exact hc' _)
    _ = δ := add_halves _

lemma totallyBounded_range_of_uniform_approx {f : ι → α}
    (happrox : ∀ ε > 0, ∃ g : ι → α, TotallyBounded (range g) ∧ ∀ i, dist (f i) (g i) < ε) :
    TotallyBounded (range f) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨g,hg,hd⟩ := happrox (ε/2) (half_pos hε)
  obtain ⟨s,hfin,hs⟩ := Metric.totallyBounded_iff.mp hg (ε/2) (half_pos hε)
  refine ⟨s,hfin,?_⟩
  rintro _ ⟨i,rfl⟩
  have := hs (mem_range_self i)
  simp only [mem_iUnion,mem_ball] at this ⊢
  obtain ⟨y,hy,hiy⟩ := this
  exact ⟨y,hy,(dist_triangle (f i) (g i) y).trans_lt
    ((add_lt_add (hd i) hiy).trans_eq (add_halves ε))⟩

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

lemma dist_toL1_eq_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f g : E → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    dist (hf.toL1 f) (hg.toL1 g) = ∫ x, |f x-g x| ∂μ := by
  rw [L1.dist_eq_integral_dist]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toL1,hg.coeFn_toL1] with x hx hy
  rw [hx,hy,Real.dist_eq]

lemma totallyBounded_L1_of_compact_lipschitz_family {ι : Type*}
    (f : ι → E → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (K : ℝ≥0) (hl : ∀ i, LipschitzWith K (f i))
    (B R : ℝ) (hb : ∀ i x, |f i x| ≤ B)
    (hs : ∀ i, Function.support (f i) ⊆ closedBall (0:E) R) :
    TotallyBounded (range fun i => (hf i).toL1 (f i)) := by
  let Q := closedBall (0:E) R
  have : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedBall (0:E) R)
  let F (i : ι) : BoundedContinuousFunction Q ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun x => f i x,(hl i).continuous.comp continuous_subtype_val⟩
  have hK : ∀ g : range F, LipschitzWith K (fun x : Q => g.val x) := by
    rintro ⟨g,⟨i,rfl⟩⟩
    change LipschitzWith K (f i ∘ Subtype.val)
    simpa only [mul_one] using (hl i).comp (LipschitzWith.subtype_val Q)
  have heq : Equicontinuous (fun g : range F => fun x : Q => g.val x) :=
    (LipschitzWith.uniformEquicontinuous _ K hK).equicontinuous
  have hc : IsCompact (closure (range F)) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (-B) B) isCompact_Icc (range F)
      (by rintro _ x ⟨i,rfl⟩; exact abs_le.mp (hb i x)) heq
  apply totallyBounded_range_of_control (g := F) (hc.totallyBounded.subset subset_closure)
  intro ε hε
  let C := μ.real Q + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ε/C,div_pos hε hC,?_⟩
  intro i j hij
  rw [dist_toL1_eq_integral]
  have he : (∫ x, |f i x-f j x| ∂μ) = ∫ x in Q, |f i x-f j x| ∂μ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hi : f i x = 0 := Function.notMem_support.mp (fun h => hx (hs i h))
    have hj : f j x = 0 := Function.notMem_support.mp (fun h => hx (hs j h))
    simp only [hi,hj,sub_self,abs_zero]
  rw [he]
  have hb' : (∫ x in Q, |f i x-f j x| ∂μ) ≤ dist (F i) (F j)*μ.real Q := by
    have hic : IntegrableOn (fun _ : E => dist (F i) (F j)) Q μ :=
      integrableOn_const (by dsimp [Q]; exact measure_closedBall_lt_top.ne)
    have hm := setIntegral_mono_on ((hf i).sub (hf j)).abs.integrableOn hic
      (show MeasurableSet Q from measurableSet_closedBall) (fun x hx =>
        show |(f i-f j) x| ≤ dist (F i) (F j) from
          BoundedContinuousFunction.dist_coe_le_dist (f := F i) (g := F j) ⟨x,hx⟩)
    exact hm.trans_eq (by simp only [integral_const,smul_eq_mul,measureReal_def,mul_comm,
      Measure.restrict_apply_univ])
  apply hb'.trans_lt
  calc dist (F i) (F j)*μ.real Q ≤ dist (F i) (F j)*C := by
        apply mul_le_mul_of_nonneg_left _ dist_nonneg
        dsimp [C]; linarith
    _ < (ε/C)*C := mul_lt_mul_of_pos_right hij hC
    _ = ε := div_mul_cancel₀ _ (ne_of_gt hC)

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Chart
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators Matrix.Norms.L2Operator

namespace CAT0Fillings

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

attribute [local instance] OAI.CAT0Fillings.ChartGeometry.instMeasurableSpaceMatrixFinReal
local instance instBorelSpaceMatrixFinReal : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩

lemma aestronglyMeasurable_normSq (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : AEStronglyMeasurable (q.normSq i u)
      (volume.restrict (q.chart i).domain) := by
  have hc : Continuous (fun r : (Fin k → ℝ) × Matrix (Fin k) (Fin k) ℝ =>
      r.1 ⬝ᵥ r.2.mulVec r.1) := by fun_prop
  exact hc.comp_aestronglyMeasurable ((q.aestronglyMeasurable_covector i hu).prodMk
    (measurable_matrix_inverse _ (q.measurable_gram i)).aestronglyMeasurable)

lemma ae_duNorm_bounds (i : ℕ) {u : X → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) : ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      0 ≤ q.duNorm i u z ∧ q.duNorm i u z ≤ (K : ℝ) ∧
      q.duNorm i u z ^2 = q.normSq i u z := by
  filter_upwards [q.ae_normSq_bounds i hu] with z hz
  exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_left K.coe_nonneg).mpr hz.2, Real.sq_sqrt hz.1⟩

lemma integrable_energy (i : ℕ) {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    Integrable (fun z => q.density i z * q.normSq i u z)
      (volume.restrict (q.chart i).domain) := by
  apply ((q.density_integrable i).mul_const ((K : ℝ)^2)).mono'
    ((q.density_integrable i).aestronglyMeasurable.mul (q.aestronglyMeasurable_normSq i hu))
  filter_upwards [q.ae_normSq_bounds i hu] with z hz
  have density_nonneg : 0 ≤ q.density i z :=
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg density_nonneg hz.1)]
  exact mul_le_mul_of_nonneg_left hz.2 density_nonneg

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators MatrixOrder

namespace CAT0Fillings

lemma abs_det_le_prod_dual_norm {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) :
    |L.det| ≤ (∏ i, Real.sqrt (L i ⬝ᵥ P⁻¹.mulVec (L i))) * Real.sqrt P.det := by
  let Q := CFC.sqrt P⁻¹
  have hQsym : Q.transpose = Q :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg P⁻¹).posSemidef.isHermitian).eq
  have hQdet : Q.det = (Real.sqrt P.det)⁻¹ := by
    have hh := hP.inv.posSemidef.det_sqrt
    simpa only [Q,RCLike.sqrt_real,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,
      Real.sqrt_inv] using hh
  have hJ : 0 < Real.sqrt P.det := Real.sqrt_pos.mpr hP.det_pos
  have hrow (i : Fin n) : (L * Q) i = Q.mulVec (L i) := by
    ext j
    change (∑ t, L i t * Q t j) = ∑ t, Q j t * L i t
    apply Finset.sum_congr rfl
    intro t ht
    have hs : Q t j = Q j t := congrFun (congrFun hQsym j) t
    rw [hs,mul_comm]
  have hnorm (i : Fin n) :
      ‖(WithLp.toLp 2 ((L*Q) i) : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (L i ⬝ᵥ P⁻¹.mulVec (L i)) := by
    have hn : ‖(WithLp.toLp 2 ((L*Q) i) : EuclideanSpace ℝ (Fin n))‖^2 =
        L i ⬝ᵥ P⁻¹.mulVec (L i) := by
      rw [←real_inner_self_eq_norm_sq]
      simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,hrow]
      exact (dot_mulVec_sqrt P⁻¹ hP.inv.posSemidef (L i)).symm
    rw [←hn,Real.sqrt_sq (norm_nonneg _)]
  have heq : |L.det| = |(L*Q).det| * Real.sqrt P.det := by
    rw [Matrix.det_mul,abs_mul,hQdet,abs_of_pos (inv_pos.mpr hJ)]
    field_simp
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ hJ.le
  simpa only [hnorm] using abs_det_le_prod_row_norm (L*Q)

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_HilbertAtlas
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma weightedMeasure_le {v : ℕ → Euc k → ℝ} {c : ℝ≥0}
    (hv : ∀ i, ∀ᵐ z ∂volume.restrict (q.chart i).domain, v i z ≤ c) :
    q.weightedMeasure v ≤ c • MassMeasure.currentMassMeasure hT := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [weightedMeasure,Measure.sum_apply _ hs,Measure.smul_apply,q.measure_eq,
    Measure.sum_apply _ hs]
  change _ ≤ (c : ℝ≥0∞) * _
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  have hi := densityPush_mono_ae (q.chart i).measurable_paramExtended
    ((hv i).mono fun z hz => (mul_le_mul_of_nonneg_left hz (q.density_nonneg i z)).trans_eq
      (mul_comm _ _))
  rw [densityPush_const_mul _ _ _ _ (q.chart i).measurable_paramExtended] at hi
  exact hi s

lemma energyMeasure_le {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    q.energyMeasure u ≤ K^2 • MassMeasure.currentMassMeasure hT := by
  apply q.weightedMeasure_le
  intro i
  simpa only [NNReal.coe_pow] using (q.ae_normSq_bounds i hu).mono (fun _ hz => hz.2)

lemma energyMeasure_finite {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    IsFiniteMeasure (q.energyMeasure u) :=
  isFiniteMeasure_of_le _ (q.energyMeasure_le hu)

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma gradient_norm_sq {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ‖q.gradient hu‖^2 = (q.energyMeasure u).real univ := by
  have hi : Integrable (fun w => ‖q.gradientFunction u w‖^2) q.atlasMeasure := by
    exact (q.memLp_gradientFunction hu).integrable_norm_pow (by norm_num)
  have hleft : ‖q.gradient hu‖^2 = ∫ w, ‖q.gradientFunction u w‖^2 ∂q.atlasMeasure := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(q.memLp_gradientFunction hu).coeFn_toLp] with w hw
    rw [gradient,hw,real_inner_self_eq_norm_sq]
  have he : (q.energyMeasure u).real univ = ∑' i, ∫ z,
      q.density i z*q.normSq i u z ∂volume.restrict (q.chart i).domain := by
    let := q.energyMeasure_finite hu
    rw [show (q.energyMeasure u).real univ = ∫ _ : X, (1:ℝ) ∂q.energyMeasure u by simp]
    have hI : Integrable (fun _ : X => (1:ℝ)) (q.energyMeasure u) := integrable_const _
    rw [energyMeasure,weightedMeasure] at hI ⊢
    rw [integral_sum_measure hI]
    apply tsum_congr
    intro i
    rw [integral_densityPush _ (q.chart i).measurable_paramExtended (q.integrable_energy i hu)
      ((q.ae_normSq_bounds i hu).mono fun z hz => mul_nonneg (q.density_nonneg i z) hz.1) continuous_const]
    simp only [mul_one]
  rw [hleft,atlasMeasure,integral_sum_measure hi,he]
  apply tsum_congr
  intro i
  rw [(measurableEmbedding_prodMk_left i).integral_map]
  rw [coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [q.ae_normalizedCovector_norm_sq i u] with z hz
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i z),smul_eq_mul,gradientFunction, hz]

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Determinant
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal MatrixOrder Matrix.Norms.L2Operator

namespace CAT0Fillings

lemma sqrt_inverse_matrix_det_ne_zero {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) : (CFC.sqrt P⁻¹).det ≠ 0 := by
  have hh := hP.inv.posSemidef.det_sqrt
  rw [hh,RCLike.sqrt_real]
  exact (Real.sqrt_pos.mpr hP.inv.det_pos).ne'

lemma normalize_rawCovector {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) (v : Euc n) :
    (CFC.sqrt P⁻¹).mulVec (rawCovector P v) = WithLp.ofLp v := by
  rw [rawCovector,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (sqrt_inverse_matrix_det_ne_zero P hP)),Matrix.one_mulVec]

lemma raw_normalizedCovector {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) (a : Fin n → ℝ) :
    rawCovector P (WithLp.toLp 2 ((CFC.sqrt P⁻¹).mulVec a)) = a := by
  rw [rawCovector,WithLp.ofLp_toLp,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (sqrt_inverse_matrix_det_ne_zero P hP)),Matrix.one_mulVec]

lemma rawCovector_norm {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosDef) (v : Euc n) :
    Real.sqrt (rawCovector P v ⬝ᵥ P⁻¹.mulVec (rawCovector P v)) = ‖v‖ := by
  rw [dot_mulVec_sqrt P⁻¹ hP.inv.posSemidef,normalize_rawCovector P hP]
  have he : (WithLp.ofLp v) ⬝ᵥ (WithLp.ofLp v) = ‖v‖^2 := by
    rw [←real_inner_self_eq_norm_sq]
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  rw [he,Real.sqrt_sq (norm_nonneg _)]

lemma normalizedDet_bound_prod {n : ℕ} (P : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hP : P.PosDef) (R : Fin n → Fin (n+1) → ℝ) (K : Fin n → ℝ≥0)
    (hR : ∀ i, Real.sqrt (R i ⬝ᵥ P⁻¹.mulVec (R i)) ≤ K i) (v : Euc (n+1)) :
    |normalizedDet P R v| ≤ ‖v‖ * ∏ i, (K i : ℝ) := by
  have h := abs_det_le_prod_dual_norm (Matrix.vecCons (rawCovector P v) R) P hP
  rw [Fin.prod_univ_succ] at h
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ] at h
  rw [rawCovector_norm P hP] at h
  have hprod := Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => Real.sqrt_nonneg
    (R i ⬝ᵥ P⁻¹.mulVec (R i))) (fun i _ => hR i)
  have hh := h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hprod (norm_nonneg v)) (Real.sqrt_nonneg _))
  rw [normalizedDet,abs_div,abs_of_pos (Real.sqrt_pos.mpr hP.det_pos)]
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hP.det_pos)).mpr hh

attribute [local instance] OAI.CAT0Fillings.instMeasurableSpaceMatrixFinReal_solutions_2
local instance instBorelSpaceMatrixFinReal_solutions_2 {n : ℕ} : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := ⟨rfl⟩

lemma aestronglyMeasurable_normalizedDet {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {n : ℕ} {P : α → Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    {R : α → Fin n → Fin (n+1) → ℝ} {v : α → Euc (n+1)}
    (hP : Measurable P) (hR : AEStronglyMeasurable R μ) (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable (fun x => normalizedDet (P x) (R x) (v x)) μ := by
  have hQ := measurable_matrix_inverse _
    (measurable_matrix_sqrt.comp (measurable_matrix_inverse _ hP))
  have hc : Continuous (fun w : Matrix (Fin (n+1)) (Fin (n+1)) ℝ ×
      (Fin n → Fin (n+1) → ℝ) × Euc (n+1) =>
      Matrix.det (Matrix.vecCons (w.1.mulVec (WithLp.ofLp w.2.2)) w.2.1)) := by
    fun_prop
  have hh := hc.comp_aestronglyMeasurable (hQ.aestronglyMeasurable.prodMk (hR.prodMk hv))
  have hJ : Measurable (fun x => Real.sqrt (P x).det) := by fun_prop
  exact (hh.aemeasurable.div hJ.aemeasurable).aestronglyMeasurable

lemma orientation_bound (a : ℝ) : abs (a/abs a) ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [abs_div,abs_abs,div_self (abs_ne_zero.mpr ha)]

lemma orientation_density (a : ℝ) : abs a*(a/abs a) = a := by
  by_cases ha : a = 0
  · simp [ha]
  · field_simp

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_Pairing
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators MatrixOrder

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma aestronglyMeasurable_testWeight (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {L : ℕ × Euc (k+1) → Euc (k+1)}
    (hL : AEStronglyMeasurable L q.atlasMeasure) :
    AEStronglyMeasurable (q.testWeight π L) q.atlasMeasure := by
  apply aestronglyMeasurable_sum_measure_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).aestronglyMeasurable_map_iff.mpr
  have hLi := (measurableEmbedding_prodMk_left i).aestronglyMeasurable_map_iff.mp
    (aestronglyMeasurable_sum_measure_iff.mp hL i)
  have ha := (q.chart i).integrable.aestronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous (volume.restrict (q.chart i).domain)
      (fun z => ENNReal.ofReal (q.density i z)))
  have hR : AEStronglyMeasurable (fun z j => q.covector i (π j) z) (q.coordinateMeasure i) := by
    apply AEMeasurable.aestronglyMeasurable
    exact AEMeasurable.of_eval (fun j =>
      ((q.aestronglyMeasurable_covector i (hπ j)).mono_ac
        (withDensity_absolutelyContinuous _ _)).aemeasurable)
  exact ((ha.aemeasurable.div ha.aemeasurable.abs).aestronglyMeasurable).mul
    (aestronglyMeasurable_normalizedDet _ (q.measurable_gram i) hR hLi)

lemma ae_testWeight_bound (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) (L : ℕ × Euc (k+1) → Euc (k+1)) :
    ∀ᵐ w ∂q.atlasMeasure, |q.testWeight π L w| ≤ ‖L w‖ * ∏ j, (K j : ℝ) := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  have hR : ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      ∀ j, q.duNorm i (π j) z ≤ K j := by
    rw [eventually_all]
    intro j
    exact (q.ae_duNorm_bounds i (hπ j)).mono (fun z hz => hz.2.1)
  filter_upwards [q.differential i,hR] with z hz hRz
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  change abs ((_ / abs _) * normalizedDet _ _ _) ≤ _
  rw [abs_mul]
  have hh := normalizedDet_bound_prod (q.gram i z) hG
    (fun j => q.covector i (π j) z) K hRz (L (i,z))
  exact (mul_le_mul_of_nonneg_right (orientation_bound _) (abs_nonneg _)).trans
    (by simpa only [one_mul] using hh)

lemma memLp_testWeight (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {L : ℕ × Euc (k+1) → Euc (k+1)}
    (hL : MemLp L 2 q.atlasMeasure) : MemLp (q.testWeight π L) 2 q.atlasMeasure := by
  apply (hL.norm.mul_const (∏ j, (K j : ℝ))).mono'
    (q.aestronglyMeasurable_testWeight π K hπ hL.aestronglyMeasurable)
  simpa only [Real.norm_eq_abs] using q.ae_testWeight_bound π K hπ L

lemma integrable_testWeight_mul (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {L : ℕ × Euc (k+1) → Euc (k+1)}
    (hL : MemLp L 2 q.atlasMeasure) {b : X → ℝ} (hb : BoundedLip b) :
    Integrable (fun w => q.testWeight π L w*b (q.atlasParam w)) q.atlasMeasure := by
  obtain ⟨Kb,hbK⟩ := hb.1
  obtain ⟨M,hM⟩ := hb.2
  have hm : MemLp (fun w => b (q.atlasParam w)) 2 q.atlasMeasure :=
    MemLp.of_bound (hbK.continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable M
      (Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hM (q.atlasParam w))
  exact (q.memLp_testWeight π K hπ hL).integrable_mul hm

lemma testWeight_gradient (π : Fin k → X → ℝ) (K : Fin k → ℝ≥0)
    (hπ : ∀ j, LipschitzWith (K j) (π j)) {u b : X → ℝ} {Ku : ℝ≥0}
    (hu : LipschitzWith Ku u) (hb : BoundedLip b) :
    (∫ w, q.testWeight π (q.gradientFunction u) w*b (q.atlasParam w) ∂q.atlasMeasure) =
      T b (Fin.cons u π) := by
  have hi := q.integrable_testWeight_mul π K hπ (q.memLp_gradientFunction hu) hb
  rw [atlasMeasure,integral_sum_measure hi,q.action]
  apply tsum_congr
  intro i
  rw [(measurableEmbedding_prodMk_left i).integral_map]
  rw [coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have ha : Admissible b (Fin.cons u π) := Foundations.admissible_vecCons hb
    ⟨Ku,hu⟩ (fun j => ⟨K j,hπ j⟩)
  rw [IntegerChart.action,ite_eq_left ha]
  apply integral_congr_ae
  filter_upwards [q.differential i,ae_restrict_mem (q.chart i).borel] with z hz hzi
  have hG : (q.gram i z).PosDef := polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i z),smul_eq_mul,
    testWeight,gradientFunction,normalizedDet,normalizedCovector,raw_normalizedCovector _ hG]
  have hd : Matrix.det (Matrix.vecCons (q.covector i u z) (fun j => q.covector i (π j) z)) =
      (q.chart i).jacobian (Fin.cons u π) z := by
    congr 1
    ext a j
    refine Fin.cases ?_ (fun a => ?_) a <;> rfl
  rw [hd]
  have hbz : b (q.atlasParam (i,z)) = (q.chart i).scalar b z := by
    simp only [atlasParam,IntegerChart.paramExtended,IntegerChart.scalar,dite_eq_left hzi]
  rw [hbz]
  unfold density
  have ho := orientation_density ((q.chart i).multiplicity z : ℝ)
  have hJ : Real.sqrt (q.gram i z).det ≠ 0 := (Real.sqrt_pos.mpr hG.det_pos).ne'
  calc
    _ = (abs ((q.chart i).multiplicity z : ℝ)*
        (((q.chart i).multiplicity z : ℝ)/abs ((q.chart i).multiplicity z : ℝ)))*
        (q.chart i).jacobian (Fin.cons u π) z*(q.chart i).scalar b z := by field_simp [hJ]
    _ = _ := by rw [ho]; ring

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings

lemma integral_norm_le_lpNorm_two {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → E} (hf : MemLp f 2 μ) :
    (∫ x, ‖f x‖ ∂μ) ≤ lpNorm f 2 μ * Real.sqrt (μ.real univ) := by
  have hp : (2:ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_norm_le_Lp_mul_Lq hp (by simpa using hf.norm)
    (show MemLp (fun _ : α => (1:ℝ)) (ENNReal.ofReal 2) μ from memLp_const 1)
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  simpa only [norm_one,mul_one,Real.one_rpow,integral_const,smul_eq_mul,
    mul_one,ENNReal.toReal_ofNat,one_div,Real.sqrt_eq_rpow,norm_norm] using hh

lemma lpNorm_Lp {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} (f : Lp E p μ) : lpNorm f p μ = ‖f‖ := by
  rw [Lp.norm_def,toReal_eLpNorm (Lp.aestronglyMeasurable f)]

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_IntrinsicBV
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma ae_fullSlice_borel_weighted {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {b : X → ℝ} (hb : Measurable b) {B : ℝ} (hB : ∀ x, |b x| ≤ B)
    (φ : Euc k → ℝ) :
    ∀ᵐ z : Euc k, currentBorelAction (fullSlice h π z)
      (fun x => φ (coordinateMap π x)*b x) (fun j => Fin.elim0 j) =
      φ z*currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j) := by
  filter_upwards [ae_fullSlice_mass_fiber h hX π hπ] with z hz
  have he : (fun x => φ (coordinateMap π x)*b x) =ᵐ[currentMassMeasure (fullSlice_approx h π z).metric]
      (φ z • b) := by
    have hh : ∀ᵐ x ∂currentMassMeasure (fullSlice_approx h π z).metric, coordinateMap π x = z := by
      simpa only [ae_iff,not_not] using hz
    filter_upwards [hh] with x hx
    simp only [hx,Pi.smul_apply,smul_eq_mul]
  rw [currentBorelAction_eq (fullSlice_approx h π z).metric]
  rw [borelAction_congr_ae _ (fullSlice_approx h π z).metric he]
  rw [borelAction_smul _ (fullSlice_approx h π z).metric
    (integrable_bounded_measurable _ hb hB) _ (φ z) (fun j => Fin.elim0 j)]
  rw [currentBorelAction_eq (fullSlice_approx h π z).metric]

lemma fullSlice_borel_weighted_integral {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : Measurable b) (B : ℝ≥0) (hB : ∀ x, |b x| ≤ B)
    {φ : Euc k → ℝ} (hφ : Measurable φ) (C : ℝ≥0) (hC : ∀ z, |φ z| ≤ C) :
    Integrable (fun z => φ z*currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)) ∧
    currentBorelAction T (fun x => φ (coordinateMap π x)*b x) π =
      ∫ z, φ z*currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j) := by
  obtain ⟨L,hL⟩ := coordinateMap_lipschitz π hπ
  have hf : Measurable (fun x => φ (coordinateMap π x)*b x) :=
    (hφ.comp hL.continuous.measurable).mul hb
  have hfB (x) : |φ (coordinateMap π x)*b x| ≤ (C*B : ℝ≥0) := by
    rw [abs_mul]
    exact mul_le_mul (hC _) (hB _) (abs_nonneg _) C.coe_nonneg
  have hi := fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hf (C*B) hfB
  have he := ae_fullSlice_borel_weighted h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb hB φ
  exact ⟨hi.1.congr he,hi.2.trans (integral_congr_ae he)⟩

lemma fullSlice_borel_L1_bound {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : Measurable b) (B : ℝ≥0) (hB : ∀ x, |b x| ≤ B) :
    (∫ z, |currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)|) ≤
      (K:ℝ)^k * ∫ x, |b x| ∂currentMassMeasure h.metric := by
  let f (z : Euc k) := currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)
  have hi := (fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb B hB).1
  let g := hi.aestronglyMeasurable.mk f
  have hg : Measurable g := hi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[volume] g := hi.aestronglyMeasurable.ae_eq_mk
  let φ (z : Euc k) : ℝ := if 0 ≤ g z then 1 else -1
  have hφ : Measurable φ := Measurable.ite (measurableSet_le measurable_const hg) measurable_const measurable_const
  have hφ1 (z) : |φ z| ≤ (1:ℝ≥0) := by dsimp [φ]; split <;> norm_num
  have hw := fullSlice_borel_weighted_integral h hX π hπ hb B hB hφ 1 hφ1
  have he : (∫ z, |f z|) = ∫ z, φ z*f z := by
    apply integral_congr_ae
    filter_upwards [hfg] with z hz
    dsimp only [φ]
    rw [hz]
    split_ifs with hg0
    · simp [abs_of_nonneg hg0]
    · simp [abs_of_neg (lt_of_not_ge hg0)]
  rw [he,←hw.2]
  apply (le_abs_self _).trans
  rw [currentBorelAction_eq h.metric]
  obtain ⟨L,hL⟩ := coordinateMap_lipschitz π hπ
  have hf : Measurable (fun x => φ (coordinateMap π x)*b x) :=
    (hφ.comp hL.continuous.measurable).mul hb
  have hfb (x) : |φ (coordinateMap π x)*b x| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hφ1 _) (abs_nonneg _)).trans (by simpa using hB x)
  have hh := borelAction_bound _ h.metric (currentMassMeasure_controls h.metric)
    (integrable_bounded_measurable _ hf hfb) π (fun _ => K) hπ
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left ?_ (pow_nonneg K.coe_nonneg _)
  apply integral_mono (integrable_bounded_measurable _ hf hfb).abs
    (integrable_bounded_measurable _ hb hB).abs
  intro x
  change |φ (coordinateMap π x)*b x| ≤ |b x|
  rw [abs_mul]
  simpa using mul_le_mul_of_nonneg_right (hφ1 (coordinateMap π x)) (abs_nonneg (b x))

lemma ae_fullSlice_borel_support {k : ℕ} {T : Functional X k}
    (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) (hπ : ∀ i, BoundedLip (π i))
    {b : X → ℝ} (hb : Measurable b) (B : ℝ≥0) (hB : ∀ x, |b x| ≤ B) :
    ∀ᵐ z : Euc k, z ∉ range (coordinateMap π) →
      currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j) = 0 := by
  filter_upwards [ae_fullSlice_mass_fiber h hX π hπ] with z hz
  intro hn
  have hzero : currentMassMeasure (fullSlice_approx h π z).metric univ = 0 := by
    apply measure_mono_null (t := {x | coordinateMap π x ≠ z}) ?_ hz
    intro x _ hx
    exact hn ⟨x,hx⟩
  have hm : mass (fullSlice h π z) = 0 := by
    rw [←currentMassMeasure_total (fullSlice_approx h π z).metric,measureReal_def,hzero,ENNReal.toReal_zero]
  have hh := currentBorelAction_bound (fullSlice_approx h π z).metric hb hB
    (fun j => Fin.elim0 j) (fun _ => (1:ℝ≥0)) (fun j => Fin.elim0 j)
  simp only [hm,mul_zero] at hh
  exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Foundations MassMeasure Slicing JointBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma abs_head_intrinsic_bound {u b : X → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) (hb : BoundedLip b)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ j, LipschitzWith K (π j)) :
    |T b (Fin.cons u π)| ≤ (K:ℝ)^k*
      ∫ w, |b (q.atlasParam w)| * ‖q.gradientFunction u w‖ ∂q.atlasMeasure := by
  rw [←q.testWeight_gradient π (fun _ => K) hπ hu hb]
  obtain ⟨B,hB⟩ := hb.2
  have hbi : MemLp (fun w => b (q.atlasParam w)) 2 q.atlasMeasure :=
    MemLp.of_bound (hb.1.choose_spec.continuous.measurable.comp q.measurable_atlasParam).aestronglyMeasurable B
      (Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs] using hB _)
  have hi : Integrable (fun w => (K:ℝ)^k*(|b (q.atlasParam w)| * ‖q.gradientFunction u w‖)) q.atlasMeasure :=
    (hbi.norm.integrable_mul (q.memLp_gradientFunction hu).norm).const_mul _
  have hh := norm_integral_le_of_norm_le hi (by
    filter_upwards [q.ae_testWeight_bound π (fun _ => K) hπ (q.gradientFunction u)] with w hw
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hw
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_right hw (abs_nonneg _)).trans_eq (by ring))
  rw [integral_const_mul] at hh
  exact hh

lemma abs_cycle_head_intrinsic_bound (h : NormalApprox (k+1) T) (hz : boundarySucc T = 0)
    {u b : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (hb : BoundedLip b)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ j, LipschitzWith K (π j)) :
    |T u (Fin.cons b π)| ≤ (K:ℝ)^k*
      ∫ w, |b (q.atlasParam w)| * ‖q.gradientFunction u w‖ ∂q.atlasMeasure := by
  have hh := h.product_rule (boundedLip_of_lipschitz hu) hb π (fun j => ⟨K,hπ j⟩)
  rw [hz] at hh
  change T u (Fin.cons b π)+T b (Fin.cons u π) = 0 at hh
  have he : T u (Fin.cons b π) = -T b (Fin.cons u π) := by linarith
  rw [he,abs_neg]
  exact q.abs_head_intrinsic_bound hu hb π hπ

lemma abs_cycle_coordinate_intrinsic_bound (h : NormalApprox (k+1) T) (hz : boundarySucc T = 0)
    {u b : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (hb : BoundedLip b)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ j, LipschitzWith K (π j)) (i : Fin (k+1)) :
    |T u (Function.update π i b)| ≤ (K:ℝ)^k*
      ∫ w, |b (q.atlasParam w)| * ‖q.gradientFunction u w‖ ∂q.atlasMeasure := by
  classical
  let σ : Equiv.Perm (Fin (k+1)) := Equiv.swap 0 i
  let ρ : Fin k → X → ℝ := fun j => π (σ j.succ)
  have hne (j : Fin k) : σ j.succ ≠ i := by
    intro he
    have hh := congrArg σ he
    simp [σ] at hh
  have he : (Function.update π i b) ∘ σ = Fin.cons b ρ := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [σ]
    · simp only [Function.comp_apply,Function.update_of_ne (hne j),Fin.cons_succ,ρ]
  have ha : Admissible u (Function.update π i b) := by
    refine ⟨boundedLip_of_lipschitz hu,?_⟩
    intro j
    by_cases hj : j = i
    · simpa [hj] using hb.1
    · simpa only [Function.update_of_ne hj] using (show ∃ M, LipschitzWith M (π j) from ⟨K,hπ j⟩)
  rw [←h.abs_apply_permute ha σ,he]
  exact q.abs_cycle_head_intrinsic_bound h hz hu hb ρ (fun j => hπ (σ j.succ))

lemma intrinsicSliceControl_finite (π : Fin (k+1) → X → ℝ) (K : ℝ≥0)
    {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) :
    IsFiniteMeasure (q.intrinsicSliceControl π K u) := by
  have := isFiniteMeasure_withDensity_ofReal
    ((q.memLp_gradientFunction hu).integrable (by norm_num)).norm.hasFiniteIntegral
  unfold intrinsicSliceControl
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma intrinsicSliceControl_integral (π : Fin (k+1) → X → ℝ) {K : ℝ≥0}
    (hπ : ∀ i, LipschitzWith K (π i)) {u : X → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) {φ : Euc (k+1) → ℝ} (hφ : Continuous φ) :
    (∫ z, |φ z| ∂q.intrinsicSliceControl π K u) =
      (K:ℝ)^k * ∫ w, |φ (coordinateMap π (q.atlasParam w))| *
        ‖q.gradientFunction u w‖ ∂q.atlasMeasure := by
  obtain ⟨M,hM⟩ := coordinateMap_lipschitz π hπ
  rw [intrinsicSliceControl,integral_smul_nnreal_measure,
    integral_map (show Measurable (fun w => coordinateMap π (q.atlasParam w)) from
      hM.continuous.measurable.comp q.measurable_atlasParam).aemeasurable
      hφ.abs.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul₀
      (q.aestronglyMeasurable_gradientFunction hu).norm.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (norm_nonneg _),NNReal.smul_def,smul_eq_mul,
    NNReal.coe_pow]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun w => mul_comm _ _

lemma fullSlice_intrinsic_directional_variation (h : NormalApprox (k+1) T)
    (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (i : Fin (k+1)) :
    DirectionalVariation (fun z => fullSlice h π z u (fun j => Fin.elim0 j))
      (EuclideanSpace.basisFun (Fin (k+1)) ℝ i) volume
      (q.intrinsicSliceControl π K u) := by
  intro φ hφ hc
  let A := parameterEquiv (k+1)
  let v := EuclideanSpace.basisFun (Fin (k+1)) ℝ i
  let ψ : (Fin (k+1) → ℝ) → ℝ := fun z => φ (A z)
  let dψ (z : Fin (k+1) → ℝ) := (fderiv ℝ φ (A z)).comp A.toContinuousLinearMap
  have hψ (z) : HasFDerivAt ψ (dψ z) z :=
    ((hφ.differentiable (by simp)) (A z)).hasFDerivAt.comp z A.hasFDerivAt
  have he (z : Fin (k+1) → ℝ) : dψ z (Pi.single i 1) = fderiv ℝ φ (A z) v := by
    simp only [dψ,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    congr 1
    simp only [v,EuclideanSpace.basisFun_apply]
    rfl
  obtain ⟨M,hM⟩ := coordinateMap_lipschitz π hπ
  obtain ⟨N,hN⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hφ (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hbφ : BoundedLip (fun x => φ (coordinateMap π x)) := boundedLip_of_lipschitz (hN.comp hM)
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
  have hdc : HasCompactSupport (fun z => fderiv ℝ φ z v) := by
    exact (hc.fderiv ℝ).comp_left (g := fun L => L v) rfl
  obtain ⟨N',hN'⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hdc hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hbd : BoundedLip (fun x => dψ (fun j => π j x) (Pi.single i 1)) := by
    simp only [he]
    exact boundedLip_of_lipschitz (hN'.comp hM)
  have huB := boundedLip_of_lipschitz hu
  have hint := (fullSlice_weighted_integral h hX π
    (fun j => boundedLip_of_lipschitz (hπ j))
    (φ := fun z => dψ (WithLp.ofLp z) (Pi.single i 1)) hbd huB).2
  have hchain := h.apply_update_multi huB π (fun j => ⟨K,hπ j⟩) hψ i hbφ hbd
  have hbound := q.abs_cycle_coordinate_intrinsic_bound h hz hu hbφ π hπ i
  have hw : (fun x => dψ (fun j => π j x) (Pi.single i 1)*u x) =
      (fun x => u x*dψ (fun j => π j x) (Pi.single i 1)) := by funext x; ring
  have hA (z : Euc (k+1)) : A (WithLp.ofLp z) = z := rfl
  change |∫ z, (fderiv ℝ φ z) v * fullSlice h π z u (fun j => Fin.elim0 j)| ≤ _
  rw [q.intrinsicSliceControl_integral π hπ hu hφ.continuous]
  have ht : |∫ z, (fderiv ℝ φ z) v * fullSlice h π z u (fun j => Fin.elim0 j)| =
      |T (fun x => dψ (fun j => π j x) (Pi.single i 1)*u x) π| := by
    rw [hint]
    simp only [he,hA]
  rw [ht]
  rw [hw,←hchain]
  exact hbound

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_ChartDensity
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Foundations MassMeasure Slicing BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma exists_exact_inverse_coordinates (i : ℕ) :
    ∃ (F : Fin n → X → ℝ) (K : ℝ≥0), (∀ a, LipschitzWith K (F a)) ∧
      (∀ z ∈ (q.chart i).domain, coordinateMap F ((q.chart i).paramExtended z) = z) ∧
      ∀ᵐ z ∂volume.restrict (q.chart i).domain, (q.chart i).jacobian F z = 1 := by
  obtain ⟨K₁,K₂,hK₁,hK₂⟩ := (q.chart i).bilipschitz
  have hrow : ∀ a y (hy : y ∈ (q.chart i).domain) z (hz : z ∈ (q.chart i).domain),
      |EuclideanSpace.proj a y-EuclideanSpace.proj a z| ≤
        (K₂:ℝ)*dist ((q.chart i).param ⟨y,hy⟩) ((q.chart i).param ⟨z,hz⟩) := by
    intro a y hy z hz
    have hh := PiLp.norm_apply_le (p := (2:ℝ≥0∞)) (y-z) a
    have he : |EuclideanSpace.proj a y-EuclideanSpace.proj a z| ≤ dist y z := by
      change |y.ofLp a-z.ofLp a| ≤ ‖y-z‖
      simpa only [Real.norm_eq_abs,PiLp.sub_apply] using hh
    exact he.trans (hK₂.le_mul_dist ⟨y,hy⟩ ⟨z,hz⟩)
  obtain ⟨F,hF,hFeq,hjac⟩ := (q.chart i).exists_inverse_coordinate_tests
    (q.chart i).borel subset_rfl (fun a => EuclideanSpace.proj a) K₂ hrow
  refine ⟨F,K₂,hF,?_,?_⟩
  · intro z hz
    ext a
    have hh := hFeq a z hz
    change F a ((q.chart i).paramExtended z) = (EuclideanSpace.proj a) z
    simpa only [IntegerChart.scalar,IntegerChart.paramExtended,dite_eq_left hz] using hh
  · have he : (Matrix.of fun i j : Fin n => EuclideanSpace.proj i (EuclideanSpace.single j (1:ℝ))) = 1 := by
      ext i j
      simp [Matrix.one_apply]
    simpa only [he,Matrix.det_one] using hjac

lemma chart_isolated_action (i : ℕ) {b : X → ℝ} (hb : BoundedLip b)
    (F : Fin n → X → ℝ) (hF : ∀ a, ∃ K : ℝ≥0, LipschitzWith K (F a)) :
    currentBorelAction T ((q.chart i).image.indicator b) F = (q.chart i).action b F := by
  rw [currentBorelAction_eq hT,←restrictCurrent_apply hT (q.chart i).image ⟨hb,hF⟩]
  rw [chartFamily_restrict_eq hT q.chart q.disjoint q.current q.summable q.action i]

lemma ae_isolated_projected_density (h : NormalApprox n T) (hX : IsCAT0 X)
    (i : ℕ) (F : Fin n → X → ℝ) {K : ℝ≥0} (hF : ∀ a, LipschitzWith K (F a))
    (hFinv : ∀ z ∈ (q.chart i).domain, coordinateMap F ((q.chart i).paramExtended z) = z)
    (hjac : ∀ᵐ z ∂volume.restrict (q.chart i).domain, (q.chart i).jacobian F z = 1)
    {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) :
    (fun z => currentBorelAction (fullSlice h F z) ((q.chart i).image.indicator u) (fun j => Fin.elim0 j)) =ᵐ[volume]
      (q.chart i).domain.indicator (fun z => ((q.chart i).multiplicity z:ℝ)*u ((q.chart i).paramExtended z)) := by
  let C := q.chart i
  obtain ⟨U,hU⟩ := (boundedLip_of_lipschitz hu).2
  let B : ℝ≥0 := ⟨max U 0,le_max_right _ _⟩
  have huB x : |u x| ≤ B := (hU x).trans (le_max_left _ _)
  have hbu : Measurable (C.image.indicator u) := hu.continuous.measurable.indicator C.measurableSet_image
  have hbb x : |C.image.indicator u x| ≤ B := by
    by_cases hx : x ∈ C.image
    · simpa only [indicator_of_mem hx] using huB x
    · simpa only [indicator_of_notMem hx,abs_zero] using B.coe_nonneg
  have hi := (fullSlice_borel_integral h hX F (fun a => boundedLip_of_lipschitz (hF a)) hbu B hbb).1
  have hden := integrable_weighted_comp (volume.restrict C.domain) C.measurable_paramExtended
    C.integrable hu.continuous.measurable ⟨B,huB⟩
  have hden' : Integrable (C.domain.indicator (fun z => (C.multiplicity z:ℝ)*u (C.paramExtended z))) :=
    (integrable_indicator_iff C.borel).mpr hden
  apply ae_eq_of_integral_contDiff_smul_eq hi.locallyIntegrable hden'.locallyIntegrable
  intro φ hφ hφs
  obtain ⟨J,hJ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφs hφ (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨M,hM⟩ := coordinateMap_lipschitz F hF
  have hφb : BoundedLip φ := by
    obtain ⟨V,hV⟩ := hφ.continuous.bounded_above_of_compact_support hφs
    exact ⟨⟨J,hJ⟩,V,fun x => by simpa only [Real.norm_eq_abs] using hV x⟩
  obtain ⟨V,hV⟩ := hφb.2
  let D : ℝ≥0 := ⟨max V 0,le_max_right _ _⟩
  have hφD x : |φ x| ≤ D := (hV x).trans (le_max_left _ _)
  have hw := fullSlice_borel_weighted_integral h hX F hF hbu B hbb hφ.continuous.measurable D hφD
  have he : (fun x => φ (coordinateMap F x)*C.image.indicator u x) =
      C.image.indicator (fun x => φ (coordinateMap F x)*u x) := by
    ext x; by_cases hx : x ∈ C.image <;> simp [hx]
  simp only [smul_eq_mul]
  have hbφ : BoundedLip (fun x => φ (coordinateMap F x)) := boundedLip_of_lipschitz (hJ.comp hM)
  have hprod := hbφ.mul (boundedLip_of_lipschitz hu)
  rw [←hw.2,he,q.chart_isolated_action i hprod F (fun a => ⟨K,hF a⟩)]
  rw [IntegerChart.action,ite_eq_left ⟨hprod,fun a => ⟨K,hF a⟩⟩]
  have hei : (fun z => φ z*C.domain.indicator (fun z => (C.multiplicity z:ℝ)*u (C.paramExtended z)) z) =
      C.domain.indicator (fun z => φ z*((C.multiplicity z:ℝ)*u (C.paramExtended z))) := by
    ext z; by_cases hz : z ∈ C.domain <;> simp [hz]
  rw [hei,integral_indicator C.borel]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem C.borel,hjac] with z hz hjz
  have hh := hFinv z hz
  simp only [IntegerChart.scalar,IntegerChart.paramExtended,dite_eq_left hz] at hh ⊢
  change (C.multiplicity z:ℝ)*(_)*C.jacobian F z = _
  rw [hjz,hh]
  have hzC : z ∈ C.domain := hz
  simp only [dite_eq_left hzC]
  ring

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_chart_jacobian_le (i : ℕ) {K : ℝ≥0}
    (hK : LipschitzWith K (q.chart i).param) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      Real.sqrt (q.gram i z).det ≤ (K:ℝ)^n := by
  filter_upwards [q.differential i,ae_restrict_mem (q.chart i).borel,
    Besicovitch.ae_tendsto_measure_inter_div volume (q.chart i).domain] with z hz hzi hzd
  have hb : ∀ v, q.field i z v ≤ (K:ℝ)*‖v‖ := by
    apply (hz.1 hzi).seminorm_le_on_piece volume subset_rfl hzd (q := normSeminorm ℝ (Euc n))
    intro y hy
    change dist ((q.chart i).param ⟨y,hy⟩) ((q.chart i).param ⟨z,hzi⟩) ≤ (K:ℝ)*‖y-z‖
    simpa only [Subtype.dist_eq,dist_eq_norm] using hK.dist_le_mul ⟨y,hy⟩ ⟨z,hzi⟩
  apply sqrt_det_le_pow_of_quadratic_bound _
    (polarizationMatrix_posDef _ _ hz.2.2 hz.2.1).posSemidef K.coe_nonneg
  intro v
  let w : Euc n := WithLp.toLp 2 v
  have hrepr : (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.repr w = v := by ext j; simp [w]
  have he : v ⬝ᵥ (q.gram i z).mulVec v = (q.field i z w)^2 := by
    simpa only [gram,hrepr] using polarizationMatrix_quadratic
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (q.field i z) hz.2.2 hz.2.1 w
  change Real.sqrt (v ⬝ᵥ (q.gram i z).mulVec v) ≤ _
  rw [he,Real.sqrt_sq (apply_nonneg _ _)]
  exact hb w

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
lemma integral_abs_mul_le_lpNorm_two {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, |f x| * |g x| ∂μ) ≤ lpNorm f 2 μ*lpNorm g 2 μ := by
  have hp : (2:ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_norm_le_Lp_mul_Lq hp (by simpa using hf) (by simpa using hg)
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable]
  simpa only [Real.norm_eq_abs,ENNReal.toReal_ofNat,one_div] using hh

namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma lipToL2_dense : DenseRange (lipToL2 μ) := by
  apply (ContinuousMap.toLp_denseRange ℝ μ ℝ (by simp : (2:ℝ≥0∞) ≠ ∞)).comp
    lipAlgebra_dense (ContinuousMap.toLp 2 μ ℝ).continuous

lemma exists_lipschitz_L2_approximation {b : X → ℝ} (hb : MemLp b 2 μ) :
    ∃ f : ℕ → lipAlgebra (X := X),
      Tendsto (fun j => lpNorm (fun x => (f j).val x-b x) 2 μ) atTop (𝓝 0) := by
  obtain ⟨u,hu,hulim⟩ := mem_closure_iff_seq_limit.mp ((lipToL2_dense μ) (hb.toLp b))
  choose f hf using hu
  have hfun : (fun j => lipToL2 μ (f j)) = u := funext hf
  have hnorm := (tendsto_iff_norm_sub_tendsto_zero).mp (hfun ▸ hulim)
  refine ⟨f,?_⟩
  convert hnorm using 1
  all_goals try with_reducible_and_instances rfl
  funext j
  rw [←lpNorm_Lp]
  rw [←toReal_eLpNorm (Lp.aestronglyMeasurable _),
    ←toReal_eLpNorm (show AEStronglyMeasurable (fun x => (f j).val x-b x) μ from
      (f j).val.continuous.aestronglyMeasurable.sub hb.aestronglyMeasurable)]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (lipToL2 μ (f j)) (hb.toLp b),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (f j).val,hb.coeFn_toLp] with x hx hfx hbx
  change (f j).val x-b x = (lipToL2 μ (f j)-hb.toLp b) x
  rw [hx]
  change _ = (ContinuousMap.toLp 2 μ ℝ (f j).val) x-(hb.toLp b) x
  rw [hfx,hbx]

end BorelCoefficients
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Coordinates
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.Slicing
open Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X k}

lemma fullSlice_borel_sub (h : NormalApprox k T) (π : Fin k → X → ℝ) (z : Euc k)
    {b c : X → ℝ} (hb : Measurable b) (hc : Measurable c)
    {B C : ℝ} (hB : ∀ x, |b x| ≤ B) (hC : ∀ x, |c x| ≤ C) :
    currentBorelAction (fullSlice h π z) (fun x => b x-c x) (fun j => Fin.elim0 j) =
      currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)-
      currentBorelAction (fullSlice h π z) c (fun j => Fin.elim0 j) := by
  simp only [currentBorelAction_eq (fullSlice_approx h π z).metric]
  exact borelAction_sub _ (fullSlice_approx h π z).metric
    (integrable_bounded_measurable _ hb hB) (integrable_bounded_measurable _ hc hC) _
    (fun j => Fin.elim0 j)

lemma fullSlice_borel_difference_bound (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b c : X → ℝ} (hb : Measurable b) (hc : Measurable c)
    {B C : ℝ≥0} (hB : ∀ x, |b x| ≤ B) (hC : ∀ x, |c x| ≤ C) :
    (∫ z, |currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)-
      currentBorelAction (fullSlice h π z) c (fun j => Fin.elim0 j)|) ≤
        (K:ℝ)^k*∫ x, |b x-c x| ∂currentMassMeasure h.metric := by
  have hd x : |b x-c x| ≤ (B+C:ℝ≥0) :=
    (abs_sub _ _).trans (add_le_add (hB x) (hC x))
  have hh := fullSlice_borel_L1_bound h hX π hπ (hb.sub hc) (B+C) hd
  change (∫ z, |currentBorelAction (fullSlice h π z) (fun x => b x-c x) (fun j => Fin.elim0 j)|) ≤
    (K:ℝ)^k*∫ x, |b x-c x| ∂currentMassMeasure h.metric at hh
  simp only [fullSlice_borel_sub h π _ hb hc hB hC] at hh
  exact hh

lemma fullSlice_cutoff_difference_bound (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b c u : X → ℝ} (hb : Measurable b) (hc : Measurable c) (hu : Measurable u)
    {B C U : ℝ≥0} (hB : ∀ x, |b x| ≤ B) (hC : ∀ x, |c x| ≤ C) (hU : ∀ x, |u x| ≤ U) :
    (∫ z, |currentBorelAction (fullSlice h π z) (fun x => b x*u x) (fun j => Fin.elim0 j)-
      currentBorelAction (fullSlice h π z) (fun x => c x*u x) (fun j => Fin.elim0 j)|) ≤
        (K:ℝ)^k*lpNorm (fun x => b x-c x) 2 (currentMassMeasure h.metric)*
          lpNorm u 2 (currentMassMeasure h.metric) := by
  have hbu x : |b x*u x| ≤ (B*U:ℝ≥0) := by
    rw [abs_mul]; exact mul_le_mul (hB x) (hU x) (abs_nonneg _) B.coe_nonneg
  have hcu x : |c x*u x| ≤ (C*U:ℝ≥0) := by
    rw [abs_mul]; exact mul_le_mul (hC x) (hU x) (abs_nonneg _) C.coe_nonneg
  apply (fullSlice_borel_difference_bound h hX π hπ (hb.mul hu) (hc.mul hu) hbu hcu).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg K.coe_nonneg _)
  have hb2 : MemLp b 2 (currentMassMeasure h.metric) :=
    MemLp.of_bound hb.aestronglyMeasurable B (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB x))
  have hc2 : MemLp c 2 (currentMassMeasure h.metric) :=
    MemLp.of_bound hc.aestronglyMeasurable C (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x))
  have hu2 : MemLp u 2 (currentMassMeasure h.metric) :=
    MemLp.of_bound hu.aestronglyMeasurable U (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hU x))
  have he : (fun x => |b x*u x-c x*u x|) = (fun x => |(b-c) x| * |u x|) := by
    funext x
    rw [←sub_mul,abs_mul]
    rfl
  change (∫ x, |b x*u x-c x*u x| ∂currentMassMeasure h.metric) ≤ _
  rw [he]
  exact integral_abs_mul_le_lpNorm_two (hb2.sub hc2) hu2

lemma dist_projectedL1 (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b c : X → ℝ} (hb : Measurable b) (hc : Measurable c)
    {B C : ℝ≥0} (hB : ∀ x, |b x| ≤ B) (hC : ∀ x, |c x| ≤ C) :
    dist (projectedL1 h hX π hπ hb B hB) (projectedL1 h hX π hπ hc C hC) =
      ∫ z, |currentBorelAction (fullSlice h π z) b (fun j => Fin.elim0 j)-
        currentBorelAction (fullSlice h π z) c (fun j => Fin.elim0 j)| := by
  rw [dist_eq_norm,L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (projectedL1 h hX π hπ hb B hB) (projectedL1 h hX π hπ hc C hC),
    (fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb B hB).1.coeFn_toL1,
    (fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hc C hC).1.coeFn_toL1]
    with z hz hzb hzc
  rw [hz]
  change ‖((fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb B hB).1.toL1 _) z-
    ((fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hc C hC).1.toL1 _) z‖ = _
  rw [hzb,hzc,Real.norm_eq_abs]

lemma projectedL1_lipschitz (h : NormalApprox k T) (hX : IsCAT0 X)
    (π : Fin k → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    {b : X → ℝ} (hb : BoundedLip b) {B : ℝ≥0} (hB : ∀ x, |b x| ≤ B) :
    projectedL1 h hX π hπ hb.continuous.measurable B hB =
      (fullSlice_eval_integrable h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb
        (fun j => Fin.elim0 j)).toL1 (fun z => fullSlice h π z b (fun j => Fin.elim0 j)) := by
  apply Lp.ext
  filter_upwards [(fullSlice_borel_integral h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb.continuous.measurable B hB).1.coeFn_toL1,
    (fullSlice_eval_integrable h hX π (fun i => boundedLip_of_lipschitz (hπ i)) hb (fun j => Fin.elim0 j)).coeFn_toL1]
    with z hz hz'
  exact hz.trans ((currentBorelAction_eq_action (fullSlice_approx h π z).metric ⟨hb,fun j => Fin.elim0 j⟩).trans hz'.symm)

end CAT0Fillings.Slicing
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Slicing Foundations MassMeasure BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma dist_coordinateL1 (i : ℕ) {u v : X → ℝ} (hu : Measurable u) (hv : Measurable v)
    (U V : ℝ≥0) (hU : ∀ x, |u x| ≤ U) (hV : ∀ x, |v x| ≤ V) :
    dist (q.coordinateL1 i hu U hU) (q.coordinateL1 i hv V hV) =
      ∫ z, q.density i z*|u ((q.chart i).paramExtended z)-v ((q.chart i).paramExtended z)|
        ∂volume.restrict (q.chart i).domain := by
  rw [dist_eq_norm,L1.norm_eq_integral_norm]
  have he : (∫ z, ‖(q.coordinateL1 i hu U hU-q.coordinateL1 i hv V hV) z‖ ∂q.coordinateMeasure i) =
      ∫ z, |u ((q.chart i).paramExtended z)-v ((q.chart i).paramExtended z)| ∂q.coordinateMeasure i := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (q.coordinateL1 i hu U hU) (q.coordinateL1 i hv V hV),
      (q.coordinate_memLp i hu U hU 1).coeFn_toLp,(q.coordinate_memLp i hv V hV 1).coeFn_toLp] with z hz huz hvz
    rw [hz]
    change ‖((q.coordinate_memLp i hu U hU 1).toLp _) z-((q.coordinate_memLp i hv V hV 1).toLp _) z‖ = _
    rw [huz,hvz,Real.norm_eq_abs]
  rw [he,coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i _),smul_eq_mul]

lemma dist_isolatedL1 (h : NormalApprox n T) (hX : IsCAT0 X) (i : ℕ)
    (F : Fin n → X → ℝ) {K : ℝ≥0} (hF : ∀ a, LipschitzWith K (F a))
    (hFinv : ∀ z ∈ (q.chart i).domain, coordinateMap F ((q.chart i).paramExtended z) = z)
    (hjac : ∀ᵐ z ∂volume.restrict (q.chart i).domain, (q.chart i).jacobian F z = 1)
    {u v : X → ℝ} {L J : ℝ≥0} (hu : LipschitzWith L u) (hv : LipschitzWith J v)
    (U V : ℝ≥0) (hU : ∀ x, |u x| ≤ U) (hV : ∀ x, |v x| ≤ V) :
    dist (q.isolatedL1 h hX i F hF hu.continuous.measurable U hU)
      (q.isolatedL1 h hX i F hF hv.continuous.measurable V hV) =
      ∫ z, |((q.chart i).multiplicity z:ℝ)| * |u ((q.chart i).paramExtended z)-v ((q.chart i).paramExtended z)|
        ∂volume.restrict (q.chart i).domain := by
  rw [isolatedL1,isolatedL1,dist_projectedL1]
  rw [←integral_indicator (q.chart i).borel]
  apply integral_congr_ae
  filter_upwards [q.ae_isolated_projected_density h hX i F hF hFinv hjac hu,
    q.ae_isolated_projected_density h hX i F hF hFinv hjac hv] with z huz hvz
  rw [huz,hvz]
  by_cases hz : z ∈ (q.chart i).domain
  · simp only [indicator_of_mem hz,←mul_sub,abs_mul]
  · simp only [indicator_of_notMem hz,sub_self,abs_zero]

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Convolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution Pointwise

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

lemma convolution_scalar_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f ρ : E → ℝ} (hf : Integrable f μ) {C M : ℝ}
    (hC : 0 ≤ C) (hρ : ∀ x, |ρ x| ≤ C) (hM : (∫ x, |f x| ∂μ) ≤ M) (x : E) :
    |(f ⋆[lsmul ℝ ℝ, μ] ρ) x| ≤ C*M := by
  rw [convolution_def]
  have hb := norm_integral_le_of_norm_le (hf.abs.mul_const C)
    (ae_of_all μ fun y => show ‖(lsmul ℝ ℝ (f y)) (ρ (x-y))‖ ≤ |f y| *C by
      simpa only [lsmul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul] using
        mul_le_mul_of_nonneg_left (hρ (x-y)) (abs_nonneg (f y)))
  rw [integral_mul_const] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_right hM hC).trans_eq (mul_comm _ _))

lemma convolution_scalar_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f ρ : E → ℝ} (hf : Integrable f μ)
    (hρc : HasCompactSupport ρ) {K M : ℝ≥0} (hρ : LipschitzWith K ρ)
    (hM : (∫ x, |f x| ∂μ) ≤ M) :
    LipschitzWith (K*M) (f ⋆[lsmul ℝ ℝ, μ] ρ) := by
  have hi (x : E) : Integrable (fun y => f y*ρ (x-y)) μ :=
    hρc.convolutionExists_right (lsmul ℝ ℝ) hf.locallyIntegrable hρ.continuous x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,convolution_def,lsmul_apply,smul_eq_mul]
  rw [←integral_sub (hi x) (hi y)]
  have hh := norm_integral_le_of_norm_le (hf.abs.mul_const ((K:ℝ)*dist x y))
    (ae_of_all μ fun z => show ‖f z*ρ (x-z)-f z*ρ (y-z)‖ ≤ |f z| *((K:ℝ)*dist x y) by
      rw [←mul_sub,Real.norm_eq_abs,abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.dist_eq,dist_sub_right] using hρ.dist_le_mul (x-z) (y-z))
  rw [integral_mul_const] at hh
  apply hh.trans
  calc (∫ z, |f z| ∂μ)*((K:ℝ)*dist x y) ≤ (M:ℝ)*((K:ℝ)*dist x y) :=
      mul_le_mul_of_nonneg_right hM (mul_nonneg K.coe_nonneg dist_nonneg)
    _ = ((K*M:ℝ≥0):ℝ)*dist x y := by push_cast; ring

lemma convolution_scalar_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f ρ : E → ℝ} {R ε : ℝ}
    (hf : Function.support f ⊆ closedBall (0:E) R)
    (hρ : Function.support ρ ⊆ closedBall (0:E) ε) :
    Function.support (f ⋆[lsmul ℝ ℝ, μ] ρ) ⊆ closedBall (0:E) (R+ε) := by
  intro x hx
  obtain ⟨y,hy,z,hz,rfl⟩ := support_convolution_subset_swap (lsmul ℝ ℝ) hx
  have hy' : ‖y‖ ≤ ε := by simpa only [mem_closedBall,dist_zero_right] using hρ hy
  have hz' : ‖z‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hf hz
  simp only [mem_closedBall,dist_zero_right]
  exact (norm_add_le y z).trans ((add_le_add hy' hz').trans_eq (add_comm _ _))

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology ENNReal NNReal Convolution

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

lemma mollifier_error_of_translation {f : E → ℝ} (hf : Integrable f μ)
    {C : ℝ} (hC : 0 ≤ C)
    (ht : ∀ w, (∫ x, |f (x+w)-f x| ∂μ) ≤ C*‖w‖) (η : ContDiffBump (0:E)) :
    (∫ x, |f x-(η.normed μ ⋆[lsmul ℝ ℝ, μ] f) x| ∂μ) ≤ C*η.rOut := by
  let ρ := η.normed μ
  have hρ : Integrable ρ μ := η.continuous_normed.integrable_of_hasCompactSupport η.hasCompactSupport_normed
  have hρ0 : ∀ x, 0 ≤ ρ x := η.nonneg_normed
  have hfi : Integrable (ρ ⋆[lsmul ℝ ℝ, μ] f) μ := hρ.integrable_convolution (lsmul ℝ ℝ) hf
  have hconv (x : E) : Integrable (fun y => ρ y*f (x-y)) μ := by
    exact (η.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ)
      η.continuous_normed hf.locallyIntegrable x)
  have hp : Integrable (fun p : E × E => ρ p.2*(f p.1-f (p.1-p.2))) (μ.prod μ) := by
    have h1 := (hf.mul_prod hρ)
    have h2 := hρ.convolution_integrand (lsmul ℝ ℝ) hf
    convert h1.sub h2 using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp only [Pi.sub_apply,lsmul_apply,smul_eq_mul]
    ring
  have hpoint (x : E) : |f x-(ρ ⋆[lsmul ℝ ℝ, μ] f) x| ≤
      ∫ y, ρ y*|f x-f (x-y)| ∂μ := by
    have he : f x-(ρ ⋆[lsmul ℝ ℝ, μ] f) x = ∫ y, ρ y*(f x-f (x-y)) ∂μ := by
      simp only [mul_sub]
      rw [integral_sub (hρ.mul_const _) (hconv x),integral_mul_const]
      simp only [ρ,η.integral_normed,one_mul,convolution_def,lsmul_apply,smul_eq_mul]
    rw [he]
    have hn := norm_integral_le_integral_norm (f := fun y => ρ y*(f x-f (x-y))) (μ := μ)
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hρ0 _)] using hn
  have hpn : Integrable (fun p : E × E => ρ p.2*|f p.1-f (p.1-p.2)|) (μ.prod μ) := by
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hρ0 _)] using hp.abs
  have hh := integral_mono (hf.sub hfi).abs hpn.integral_prod_left hpoint
  rw [integral_integral_swap hpn] at hh
  have hb (y : E) : (∫ x, ρ y*|f x-f (x-y)| ∂μ) ≤ ρ y*(C*η.rOut) := by
    rw [integral_const_mul]
    by_cases hy : y ∈ Function.support ρ
    · have hyn : ‖y‖ ≤ η.rOut := by
        have hys : Function.support ρ ⊆ closedBall 0 η.rOut := by
          dsimp [ρ]
          rw [η.support_normed_eq]
          exact ball_subset_closedBall
        simpa only [mem_closedBall,dist_zero_right] using hys hy
      have ht' : (∫ x, |f x-f (x-y)| ∂μ) ≤ C*‖y‖ := by
        simpa only [←sub_eq_add_neg,norm_neg,abs_sub_comm] using ht (-y)
      exact mul_le_mul_of_nonneg_left (ht'.trans (mul_le_mul_of_nonneg_left hyn hC)) (hρ0 y)
    · have hz : ρ y = 0 := Function.notMem_support.mp hy
      simp only [hz,zero_mul,le_refl]
  have hm := integral_mono hpn.integral_prod_right (hρ.mul_const (C*η.rOut)) hb
  rw [integral_mul_const] at hm
  have hr : (∫ y, ρ y ∂μ) = 1 := η.integral_normed
  rw [hr,one_mul] at hm
  exact hh.trans hm

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Translation
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem totallyBounded_L1_of_translation {ι : Type*}
    (f : ι → E → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (M : ℝ≥0) (hM : ∀ i, (∫ x, |f i x| ∂μ) ≤ M)
    (R : ℝ) (hs : ∀ i, Function.support (f i) ⊆ closedBall (0:E) R)
    {C : ℝ} (hC : 0 ≤ C)
    (ht : ∀ i w, (∫ x, |f i (x+w)-f i x| ∂μ) ≤ C*‖w‖) :
    TotallyBounded (range fun i => (hf i).toL1 (f i)) := by
  apply totallyBounded_range_of_uniform_approx
  intro ε hε
  let δ := ε/(C+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  let η : ContDiffBump (0:E) := ⟨δ/2,δ,half_pos hδ,by linarith⟩
  let ρ := η.normed μ
  let g (i) := f i ⋆[lsmul ℝ ℝ, μ] ρ
  have hρc : HasCompactSupport ρ := η.hasCompactSupport_normed
  have hρ : Continuous ρ := η.continuous_normed
  have hρi : Integrable ρ μ := hρ.integrable_of_hasCompactSupport hρc
  have hg (i) : Integrable (g i) μ := (hf i).integrable_convolution (lsmul ℝ ℝ) hρi
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hρc (η.contDiff_normed (n := (⊤ : ℕ∞))) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨B,hB⟩ := hρ.bounded_above_of_compact_support hρc
  have hB0 : 0 ≤ B := (norm_nonneg (ρ 0)).trans (hB 0)
  have hgs (i) : Function.support (g i) ⊆ closedBall (0:E) (R+δ) := by
    apply convolution_scalar_support (hs i)
    dsimp [ρ]
    rw [η.support_normed_eq]
    exact ball_subset_closedBall
  have hgb (i) (x) : |g i x| ≤ B*M :=
    convolution_scalar_bound (hf i) hB0 (fun y => hB y) (hM i) x
  have hgl (i) : LipschitzWith (K*M) (g i) :=
    convolution_scalar_lipschitz (hf i) hρc hK (hM i)
  refine ⟨fun i => (hg i).toL1 (g i),
    totallyBounded_L1_of_compact_lipschitz_family g hg (K*M) hgl (B*M) (R+δ) hgb hgs,?_⟩
  intro i
  rw [dist_toL1_eq_integral]
  have he := mollifier_error_of_translation (hf i) hC (ht i) η
  have hcomm : (ρ ⋆[lsmul ℝ ℝ, μ] f i) = g i := by
    have hflip : (lsmul ℝ ℝ).flip = lsmul ℝ ℝ := by ext; simp
    simpa only [hflip,g] using (convolution_flip (L := lsmul ℝ ℝ) (f := f i) (g := ρ) (μ := μ))
  rw [hcomm] at he
  apply he.trans_lt
  change C*δ < ε
  dsimp [δ]
  rw [←mul_div_assoc]
  apply (div_lt_iff₀ (by linarith : 0 < C+1)).mpr
  nlinarith

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.JointBV
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

lemma integral_le_of_closedBall_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {f : E → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hb : ∀ r : ℝ, (∫ x in closedBall (0:E) r, f x ∂μ) ≤ C) :
    (∫ x, f x ∂μ) ≤ C := by
  have hi : IntegrableOn f (⋃ n : ℕ, closedBall (0:E) n) μ := by
    simpa only [iUnion_closedBall_nat,integrableOn_univ] using hf
  have hl := tendsto_setIntegral_of_monotone (fun n : ℕ => measurableSet_closedBall)
    (fun i j hij => closedBall_subset_closedBall (Nat.cast_le.mpr hij)) hi
  simp only [iUnion_closedBall_nat,Measure.restrict_univ] at hl
  exact le_of_tendsto hl (Eventually.of_forall fun n : ℕ => hb n)

lemma full_segment_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : Continuous f') (x w : E) :
    |f (x+w)-f x| ≤ ‖w‖*∫ t in Icc (0:ℝ) 1, ‖f' (x+t • w)‖ := by
  let p (t : ℝ) := x+t • w
  have hp (t : ℝ) : HasDerivAt p w t := by
    simpa only [p,one_smul,id_eq] using ((hasDerivAt_id t).smul_const w).const_add x
  have hd (t : ℝ) := (hf (p t)).comp_hasDerivAt t (hp t)
  have hc : Continuous (fun t => f' (p t) w) := by dsimp [p]; fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (fun t _ => hd t) (hc.intervalIntegrable _ _)
  change (∫ t in (0:ℝ)..1, f' (p t) w) = f (p 1)-f (p 0) at hi
  simp only [p,zero_smul,one_smul,add_zero] at hi
  rw [←hi]
  apply (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans
  have hh := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
    (hc.abs.intervalIntegrable _ _)
    ((show Continuous (fun t : ℝ => ‖w‖*‖f' (p t)‖) by dsimp [p]; fun_prop).intervalIntegrable _ _)
    (fun t _ => by simpa only [Real.norm_eq_abs,mul_comm] using (f' (p t)).le_opNorm w)
  apply hh.trans_eq
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le zero_le_one,
    ←integral_Icc_eq_integral_Ioc]

lemma smooth_translation_integral_bound {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hf : ∀ x, HasFDerivAt f (f' x) x) (hf' : Continuous f')
    (hfi : Integrable f μ) (hgi : Integrable (fun x => ‖f' x‖) μ) (w : E) :
    (∫ x, |f (x+w)-f x| ∂μ) ≤ ‖w‖*∫ x, ‖f' x‖ ∂μ := by
  let m : Measure ℝ := volume.restrict (Icc 0 1)
  have : IsFiniteMeasure m := by dsimp [m]; infer_instance
  have he (t : ℝ) : (∫ x, ‖f' (x+t • w)‖ ∂μ) = ∫ x, ‖f' x‖ ∂μ :=
    integral_add_right_eq_self (fun x => ‖f' x‖) (t • w)
  have hp : Integrable (fun p : E × ℝ => ‖f' (p.1+p.2 • w)‖) (μ.prod m) := by
    apply (integrable_prod_iff' (show AEStronglyMeasurable
      (fun p : E × ℝ => ‖f' (p.1+p.2 • w)‖) (μ.prod m) from
        (show Continuous (fun p : E × ℝ => ‖f' (p.1+p.2 • w)‖) by fun_prop).aestronglyMeasurable)).mpr
    refine ⟨Eventually.of_forall fun t => hgi.comp_add_right (t • w),?_⟩
    simp only [norm_norm,he]
    exact integrable_const (μ := m) _
  have hh := integral_mono ((hfi.comp_add_right w).sub hfi).abs
    (hp.integral_prod_left.const_mul ‖w‖) (fun x => full_segment_bound hf hf' x w)
  rw [integral_const_mul,integral_integral_swap hp] at hh
  simp only [he,integral_const,smul_eq_mul] at hh
  have hm : m.real univ = 1 := by simp [m,measureReal_def,Real.volume_Icc]
  simpa only [←measureReal_def,hm,one_mul,Pi.sub_apply] using hh

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_BV
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology NNReal ENNReal Convolution

namespace CAT0Fillings.JointBV
lemma scalar_precompR {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (lsmul ℝ ℝ).precompR E = (lsmul ℝ ℝ : ℝ →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) := by
  ext scalar linearMap
  simp only [precompR,coe_comp,Function.comp_apply,compL_apply,lsmul_apply,_root_.smul_apply]

lemma convolution_bump_deriv_norm_integrable {k : ℕ}
    {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin k))} [μ.IsAddHaarMeasure]
    (hf : Integrable f μ) (η : ContDiffBump (0:EuclideanSpace ℝ (Fin k))) :
    Integrable (fun x => ‖(f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), μ]
      fderiv ℝ (η.normed μ)) x‖) μ := by
  have hc := η.hasCompactSupport_normed (μ := μ)
  have hd := (η.contDiff_normed (μ := μ) (n := (⊤ : ℕ∞))).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [scalar_precompR]
  exact (hf.integrable_convolution (lsmul ℝ ℝ : ℝ →L[ℝ] (EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ))
    (hd.integrable_of_hasCompactSupport (hc.fderiv ℝ))).norm
end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric ContinuousLinearMap
open scoped Topology ENNReal NNReal Convolution

namespace CAT0Fillings.JointBV

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

lemma convolution_bump_hasFDerivAt {f : E → ℝ} (hf : Integrable f μ)
    (η : ContDiffBump (0:E)) (x : E) :
    HasFDerivAt (f ⋆[lsmul ℝ ℝ, μ] η.normed μ)
      ((f ⋆[(lsmul ℝ ℝ).precompR E, μ] fderiv ℝ (η.normed μ)) x) x :=
  η.hasCompactSupport_normed.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hf.locallyIntegrable η.contDiff_normed x

lemma convolution_bump_deriv_continuous {f : E → ℝ} (hf : Integrable f μ)
    (η : ContDiffBump (0:E)) :
    Continuous (f ⋆[(lsmul ℝ ℝ).precompR E, μ] fderiv ℝ (η.normed μ)) :=
  (η.hasCompactSupport_normed.fderiv ℝ).continuous_convolution_right
    ((lsmul ℝ ℝ).precompR E) hf.locallyIntegrable
    ((η.contDiff_normed (n := (⊤ : ℕ∞))).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))

lemma convolution_bump_integrable {f : E → ℝ} (hf : Integrable f μ)
    (η : ContDiffBump (0:E)) : Integrable (f ⋆[lsmul ℝ ℝ, μ] η.normed μ) μ :=
  hf.integrable_convolution (lsmul ℝ ℝ)
    (η.continuous_normed.integrable_of_hasCompactSupport η.hasCompactSupport_normed)

lemma mollified_gradient_total_bound {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin k))} [μ.IsAddHaarMeasure]
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ν]
    (hf : Integrable f μ)
    (hv : ∀ i, DirectionalVariation f (EuclideanSpace.basisFun (Fin k) ℝ i) μ ν)
    (η : ContDiffBump (0 : EuclideanSpace ℝ (Fin k))) :
    (∫ z, ‖(f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), μ]
      fderiv ℝ (η.normed μ)) z‖ ∂μ) ≤ k*ν.real univ := by
  apply integral_le_of_closedBall_bound
    (convolution_bump_deriv_norm_integrable hf η)
  intro r
  exact (mollified_gradient_integral_bound hf.locallyIntegrable hv η 0 r).trans
    (mul_le_mul_of_nonneg_left (measureReal_mono (subset_univ _)) (Nat.cast_nonneg k))

theorem translation_integral_bound {k : ℕ} {f : EuclideanSpace ℝ (Fin k) → ℝ}
    {μ : Measure (EuclideanSpace ℝ (Fin k))} [μ.IsAddHaarMeasure]
    {ν : Measure (EuclideanSpace ℝ (Fin k))} [IsFiniteMeasure ν]
    (hf : Integrable f μ)
    (hv : ∀ i, DirectionalVariation f (EuclideanSpace.basisFun (Fin k) ℝ i) μ ν)
    (w : EuclideanSpace ℝ (Fin k)) :
    (∫ x, |f (x+w)-f x| ∂μ) ≤ ‖w‖*(k*ν.real univ) := by
  let η (j : ℕ) := shrinkingBump (E := EuclideanSpace ℝ (Fin k)) j
  let F (j : ℕ) := f ⋆[lsmul ℝ ℝ, μ] (η j).normed μ
  let F' (j : ℕ) := f ⋆[(lsmul ℝ ℝ).precompR (EuclideanSpace ℝ (Fin k)), μ]
    fderiv ℝ ((η j).normed μ)
  have hF (j : ℕ) (x : EuclideanSpace ℝ (Fin k)) : HasFDerivAt (F j) (F' j x) x :=
    convolution_bump_hasFDerivAt hf (η j) x
  have hF' (j : ℕ) : Continuous (F' j) := convolution_bump_deriv_continuous hf (η j)
  have hFi (j : ℕ) : Integrable (F j) μ := convolution_bump_integrable hf (η j)
  have hGi (j : ℕ) : Integrable (fun x => ‖F' j x‖) μ :=
    convolution_bump_deriv_norm_integrable hf (η j)
  have hl : ∀ᵐ x ∂μ, Tendsto (fun j => F j x) atTop (𝓝 (f x)) := by
    have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := η) shrinkingBump_tendsto (K := 2) (Eventually.of_forall (fun j => le_rfl)) hf.locallyIntegrable
    filter_upwards [hh] with x hx
    simpa only [F,scalar_convolution_comm f] using hx
  have hlw := (measurePreserving_add_right μ w).quasiMeasurePreserving.ae hl
  apply integral_abs_le_of_ae_tendsto ((hf.comp_add_right w).sub hf)
    (fun j => ((hFi j).comp_add_right w).sub (hFi j)) ?_ (by positivity)
  · exact Eventually.of_forall fun j =>
      (smooth_translation_integral_bound (hF j) (hF' j) (hFi j) (hGi j) w).trans
        (mul_le_mul_of_nonneg_left (mollified_gradient_total_bound hf hv (η j)) (norm_nonneg w))
  · filter_upwards [hlw,hl] with x hx hw
    exact hx.sub hw

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.JointBV

lemma DirectionalVariation.congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] {μ ν : Measure E} {f g : E → ℝ} {v : E}
    (h : DirectionalVariation f v μ ν) (he : f =ᵐ[μ] g) :
    DirectionalVariation g v μ ν := by
  intro φ hφ hc
  have hh := h φ hφ hc
  convert hh using 2
  all_goals try with_reducible_and_instances rfl
  apply integral_congr_ae
  filter_upwards [he] with x hx
  rw [hx]

theorem totallyBounded_L1_of_directional_variation {k : ℕ} {ι : Type*}
    (f : ι → EuclideanSpace ℝ (Fin k) → ℝ) (hf : ∀ i, Integrable (f i))
    (ν : ι → Measure (EuclideanSpace ℝ (Fin k))) [∀ i, IsFiniteMeasure (ν i)]
    (hv : ∀ i l, DirectionalVariation (f i) (EuclideanSpace.basisFun (Fin k) ℝ l) volume (ν i))
    (B : ℝ≥0) (hB : ∀ i, (∫ x, |f i x|) ≤ B)
    (M : ℝ≥0) (hM : ∀ i, (ν i).real univ ≤ M)
    (R : ℝ) (hs : ∀ i, ∀ᵐ x, x ∉ closedBall 0 R → f i x = 0) :
    TotallyBounded (range fun i => (hf i).toL1 (f i)) := by
  let g (i) := (closedBall 0 R).indicator (f i)
  have he (i) : f i =ᵐ[volume] g i := by
    filter_upwards [hs i] with x hx
    by_cases hxR : x ∈ closedBall 0 R
    · simp only [g,indicator_of_mem hxR]
    · simp only [g,indicator_of_notMem hxR,hx hxR]
  have hg (i) : Integrable (g i) := (hf i).congr (he i)
  have hge (i) : (hf i).toL1 (f i) = (hg i).toL1 (g i) :=
    (Integrable.toL1_eq_toL1_iff _ _ _ _).mpr (he i)
  simp only [hge]
  apply totallyBounded_L1_of_translation g hg B ?_ R ?_ (C := k*(M:ℝ)) (by positivity)
  · intro i w
    have hh := translation_integral_bound (hg i) (fun l => (hv i l).congr (he i)) w
    apply hh.trans
    calc ‖w‖*((k:ℝ)*(ν i).real univ) ≤ ‖w‖*((k:ℝ)*M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hM i) (Nat.cast_nonneg k)) (norm_nonneg w)
      _ = _ := mul_comm _ _
  · intro i
    have hi : (∫ x, |g i x|) = ∫ x, |f i x| := integral_congr_ae ((he i).symm.fun_comp abs)
    rw [hi]
    exact hB i
  · intro i x hx
    by_contra hn
    exact hx (indicator_of_notMem hn _)

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Gradient_ClosedLinear
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma norm_value {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
    {hT : IsMetricCurrent T} {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ‖value (hT := hT) hu‖ = lpNorm u 2 (MassMeasure.currentMassMeasure hT) := by
  rw [value,Lp.norm_toLp,toReal_eLpNorm hu.continuous.aestronglyMeasurable]

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Projected
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma gradientFunction_mul {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    q.gradientFunction (fun x => u x*v x) =ᵐ[q.atlasMeasure]
      fun w => u (q.atlasParam w) • q.gradientFunction v w+
        v (q.atlasParam w) • q.gradientFunction u w := by
  apply Measure.ae_sum_iff.mpr
  intro i
  apply (measurableEmbedding_prodMk_left i).ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [(q.chart i).ae_fderivWithin_scalar_mul hu hv,
    ae_restrict_mem (q.chart i).borel] with z hz hzi
  change q.normalizedCovector i (fun x => u x*v x) z = _
  unfold normalizedCovector covector
  rw [hz]
  have hr (L M : Euc (k+1) →L[ℝ] ℝ) (a b : ℝ) :
      differentialRow (a • L+b • M) = a • differentialRow L+b • differentialRow M := rfl
  rw [hr,Matrix.mulVec_add,Matrix.mulVec_smul,Matrix.mulVec_smul,WithLp.toLp_add,
    WithLp.toLp_smul,WithLp.toLp_smul]
  simp only [gradientFunction,normalizedCovector,covector,atlasParam,
    IntegerChart.paramExtended,IntegerChart.scalar,dite_eq_left hzi]

lemma integral_gradientFunction_norm {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    (∫ w, ‖q.gradientFunction u w‖ ∂q.atlasMeasure) ≤
      ‖q.gradient hu‖*Real.sqrt (q.atlasMeasure.real univ) := by
  have hh := integral_norm_le_lpNorm_two (q.memLp_gradientFunction hu)
  have hn : lpNorm (q.gradientFunction u) 2 q.atlasMeasure = ‖q.gradient hu‖ := by
    rw [gradient,Lp.norm_toLp,toReal_eLpNorm (q.memLp_gradientFunction hu).aestronglyMeasurable]
  rwa [hn] at hh

lemma integral_gradient_mul_bound {u χ : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hχ : LipschitzWith J χ) {B : ℝ}
    (hB : 0 ≤ B) (hχB : ∀ x, |χ x| ≤ B) :
    (∫ w, ‖q.gradientFunction (fun x => χ x*u x) w‖ ∂q.atlasMeasure) ≤
      B*‖q.gradient hu‖*Real.sqrt (q.atlasMeasure.real univ)+
        J*‖value (hT := hT) hu‖*Real.sqrt ((MassMeasure.currentMassMeasure hT).real univ) := by
  let μ := MassMeasure.currentMassMeasure hT
  have hχb := Foundations.boundedLip_of_lipschitz hχ
  have hub := Foundations.boundedLip_of_lipschitz hu
  obtain ⟨M,hm⟩ := (hχb.mul hub).1
  have hia := ((q.memLp_gradientFunction hu).integrable (by norm_num)).norm.const_mul B
  have hiu : Integrable (fun w => |u (q.atlasParam w)|) q.atlasMeasure := by
    have hh : Integrable (fun x => |u x|) (q.atlasMeasure.map q.atlasParam) := by
      rw [q.map_atlasMeasure]
      exact ((hub.memLp 2).integrable (by norm_num)).abs
    exact (integrable_map_measure (hu.continuous.abs.aestronglyMeasurable)
      q.measurable_atlasParam.aemeasurable).mp hh
  have hib := hiu.const_mul (J:ℝ)
  have hpoint : ∀ᵐ w ∂q.atlasMeasure,
      ‖q.gradientFunction (fun x => χ x*u x) w‖ ≤
        B*‖q.gradientFunction u w‖+J*|u (q.atlasParam w)| := by
    filter_upwards [q.gradientFunction_mul hχ hu,q.ae_gradientFunction_bound hχ] with w hw hwb
    rw [hw]
    calc _ ≤ ‖χ (q.atlasParam w) • q.gradientFunction u w‖+
          ‖u (q.atlasParam w) • q.gradientFunction χ w‖ := norm_add_le _ _
      _ ≤ B*‖q.gradientFunction u w‖+J*|u (q.atlasParam w)| := by
        simp only [norm_smul,Real.norm_eq_abs]
        exact add_le_add (mul_le_mul_of_nonneg_right (hχB _) (norm_nonneg _))
          ((mul_le_mul_of_nonneg_left hwb (abs_nonneg _)).trans_eq (mul_comm _ _))
  have hh := integral_mono_ae ((q.memLp_gradientFunction hm).integrable (by norm_num)).norm
    (hia.add hib) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add hia hib,integral_const_mul,integral_const_mul] at hh
  have he : (∫ w, |u (q.atlasParam w)| ∂q.atlasMeasure) = ∫ x, |u x| ∂μ := by
    dsimp only [μ]
    rw [←q.map_atlasMeasure,integral_map q.measurable_atlasParam.aemeasurable
      hu.continuous.abs.aestronglyMeasurable]
  rw [he] at hh
  have huL := integral_norm_le_lpNorm_two (hub.memLp (μ := μ) 2)
  rw [←norm_value (hT := hT) hu] at huL
  simp only [Real.norm_eq_abs] at huL
  exact hh.trans (by
    have h1 := mul_le_mul_of_nonneg_left (q.integral_gradientFunction_norm hu) hB
    have h2 := mul_le_mul_of_nonneg_left huL J.coe_nonneg
    nlinarith)

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Foundations MassMeasure Slicing JointBV BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma intrinsicSliceControl_total (π : Fin (k+1) → X → ℝ) {K : ℝ≥0}
    (hπ : ∀ i, LipschitzWith K (π i)) {u : X → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) :
    (q.intrinsicSliceControl π K u).real univ =
      (K:ℝ)^k*∫ w, ‖q.gradientFunction u w‖ ∂q.atlasMeasure := by
  simpa using q.intrinsicSliceControl_integral π hπ hu (φ := fun _ => (1:ℝ)) continuous_const

lemma fullSlice_L1_bound {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    (h : NormalApprox (k+1) T) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i)) :
    (∫ z, |fullSlice h π z u (fun j => Fin.elim0 j)|) ≤
      (K:ℝ)^(k+1)*∫ x, |u x| ∂currentMassMeasure hT := by
  obtain ⟨B,hB⟩ := (boundedLip_of_lipschitz hu).2
  let B' : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  have hh := fullSlice_borel_L1_bound h hX π hπ hu.continuous.measurable B'
    (fun x => (hB x).trans (le_max_left _ _))
  simpa only [currentBorelAction_eq_action (fullSlice_approx h π _).metric
    ⟨boundedLip_of_lipschitz hu,fun j => Fin.elim0 j⟩] using hh

theorem totallyBounded_whole_projected {ι : Type*}
    (h : NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    (u : ι → X → ℝ) (L : ι → ℝ≥0) (hu : ∀ i, LipschitzWith (L i) (u i))
    {χ : X → ℝ} {J : ℝ≥0} (hχ : LipschitzWith J χ)
    (M : ℝ≥0) (hMv : ∀ i, ‖value (hT := hT) (hu i)‖ ≤ M)
    (hMg : ∀ i, ‖q.gradient (hu i)‖ ≤ M) :
    TotallyBounded (range fun i =>
      (fullSlice_eval_integrable h hX π (fun a => boundedLip_of_lipschitz (hπ a))
        ((boundedLip_of_lipschitz hχ).mul (boundedLip_of_lipschitz (hu i)))
          (fun j => Fin.elim0 j)).toL1
      (fun z => fullSlice h π z (fun x => χ x*u i x) (fun j => Fin.elim0 j))) := by
  obtain ⟨B₀,hB₀⟩ := (boundedLip_of_lipschitz hχ).2
  let B : ℝ≥0 := ⟨max B₀ 0,le_max_right _ _⟩
  have hB x : |χ x| ≤ B := (hB₀ x).trans (le_max_left _ _)
  let v i := fun x => χ x*u i x
  have hvb i : BoundedLip (v i) := (boundedLip_of_lipschitz hχ).mul (boundedLip_of_lipschitz (hu i))
  choose N hv using fun i => (hvb i).1
  let f i := fun z => fullSlice h π z (v i) (fun j => Fin.elim0 j)
  have hfi i : Integrable (f i) := fullSlice_eval_integrable h hX π
    (fun a => boundedLip_of_lipschitz (hπ a)) (hvb i) _
  let ν i := q.intrinsicSliceControl π K (v i)
  have : ∀ index, IsFiniteMeasure (ν index) :=
    fun index => q.intrinsicSliceControl_finite π K (hv index)
  let m := Real.sqrt ((currentMassMeasure hT).real univ)
  let a := Real.sqrt (q.atlasMeasure.real univ)
  let C : ℝ≥0 := ⟨(K:ℝ)^k*(B*M*a+J*M*m),by dsimp [a,m]; positivity⟩
  let D : ℝ≥0 := ⟨(K:ℝ)^(k+1)*B*M*m,by dsimp [m]; positivity⟩
  obtain ⟨K',hK'⟩ := coordinateMap_lipschitz π hπ
  obtain ⟨R,hR⟩ := (isCompact_range hK'.continuous).isBounded.subset_closedBall (0:Euc (k+1))
  apply totallyBounded_L1_of_directional_variation f hfi ν
    (fun i l => q.fullSlice_intrinsic_directional_variation h hz hX π hπ (hv i) l) D ?_ C ?_ R ?_
  · intro i
    apply (fullSlice_L1_bound (hv i) h hX π hπ).trans
    have hint : (∫ x, |v i x| ∂currentMassMeasure hT) ≤
        B*∫ x, |u i x| ∂currentMassMeasure hT := by
      rw [←integral_const_mul]
      apply integral_mono (integrable_boundedLip _ (hvb i)).abs
        ((integrable_boundedLip _ (boundedLip_of_lipschitz (hu i))).abs.const_mul B)
      intro x
      exact (abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _))
    have hil := integral_norm_le_lpNorm_two ((boundedLip_of_lipschitz (hu i)).memLp (μ := currentMassMeasure hT) 2)
    rw [←norm_value (hT := hT) (hu i)] at hil
    simp only [Real.norm_eq_abs] at hil
    have him : (∫ x, |u i x| ∂currentMassMeasure hT) ≤ M*m :=
      hil.trans (mul_le_mul_of_nonneg_right (hMv i) (Real.sqrt_nonneg _))
    change _ ≤ (K:ℝ)^(k+1)*B*M*m
    nlinarith [pow_nonneg K.coe_nonneg (k+1),mul_le_mul_of_nonneg_left hint (pow_nonneg K.coe_nonneg (k+1)),
      mul_le_mul_of_nonneg_left him (mul_nonneg (pow_nonneg K.coe_nonneg (k+1)) B.coe_nonneg)]
  · intro i
    rw [intrinsicSliceControl_total q π hπ (hv i)]
    apply (mul_le_mul_of_nonneg_left (q.integral_gradient_mul_bound (hu i) hχ B.coe_nonneg hB)
      (pow_nonneg K.coe_nonneg k)).trans
    change _ ≤ (K:ℝ)^k*(B*M*a+J*M*m)
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg K.coe_nonneg k)
    exact add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hMg i) B.coe_nonneg) (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hMv i) J.coe_nonneg) (Real.sqrt_nonneg _))
  · intro i
    obtain ⟨B',hB'⟩ := (hvb i).2
    let B'' : ℝ≥0 := ⟨max B' 0,le_max_right _ _⟩
    have hs := ae_fullSlice_borel_support h hX π (fun a => boundedLip_of_lipschitz (hπ a))
      (hv i).continuous.measurable B'' (fun x => (hB' x).trans (le_max_left _ _))
    filter_upwards [hs] with z hz
    intro hnot
    have hh := hz (fun hh => hnot (hR hh))
    simpa only [currentBorelAction_eq_action (fullSlice_approx h π z).metric
      ⟨hvb i,fun j => Fin.elim0 j⟩] using hh

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Borel
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Foundations MassMeasure Slicing JointBV BorelCoefficients

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

theorem totallyBounded_borel_projected {ι : Type*}
    (h : NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (π : Fin (k+1) → X → ℝ) {K : ℝ≥0} (hπ : ∀ i, LipschitzWith K (π i))
    (u : ι → X → ℝ) (L U : ι → ℝ≥0) (hu : ∀ i, LipschitzWith (L i) (u i))
    (hU : ∀ i x, |u i x| ≤ U i)
    {χ : X → ℝ} (hχ : Measurable χ) (B : ℝ≥0) (hB : ∀ x, |χ x| ≤ B)
    (M : ℝ≥0) (hMv : ∀ i, ‖value (hT := hT) (hu i)‖ ≤ M)
    (hMg : ∀ i, ‖q.gradient (hu i)‖ ≤ M) :
    TotallyBounded (range fun i => projectedL1 h hX π hπ (hχ.mul (hu i).continuous.measurable)
      (B*U i) (mul_bounded hB (hU i))) := by
  have hχ2 : MemLp χ 2 (currentMassMeasure hT) := MemLp.of_bound hχ.aestronglyMeasurable B
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  obtain ⟨b,hb⟩ := exists_lipschitz_L2_approximation (currentMassMeasure hT) hχ2
  apply totallyBounded_range_of_uniform_approx
  intro ε hε
  have hlim : Tendsto (fun j => (K:ℝ)^(k+1)*lpNorm (fun x => (b j).val x-χ x) 2 (currentMassMeasure hT)*M)
      atTop (𝓝 0) := by simpa using (hb.const_mul ((K:ℝ)^(k+1))).mul_const (M:ℝ)
  obtain ⟨j,hj⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  obtain ⟨C₀,hC₀⟩ := (b j).property.2
  let C : ℝ≥0 := ⟨max C₀ 0,le_max_right _ _⟩
  have hC x : |(b j).val x| ≤ C := (hC₀ x).trans (le_max_left _ _)
  obtain ⟨J,hJ⟩ := (b j).property.1
  let g i := projectedL1 h hX π hπ ((b j).val.continuous.measurable.mul (hu i).continuous.measurable)
    (C*U i) (mul_bounded hC (hU i))
  refine ⟨g,?_,?_⟩
  · have he : g = fun i =>
        (fullSlice_eval_integrable h hX π (fun a => boundedLip_of_lipschitz (hπ a))
          ((boundedLip_of_lipschitz hJ).mul (boundedLip_of_lipschitz (hu i))) (fun j => Fin.elim0 j)).toL1
            (fun z => fullSlice h π z (fun x => (b j).val x*u i x) (fun j => Fin.elim0 j)) := by
      funext i
      exact projectedL1_lipschitz h hX π hπ ((b j).property.mul (boundedLip_of_lipschitz (hu i))) _
    rw [he]
    exact q.totallyBounded_whole_projected h hz hX π hπ u L hu hJ M hMv hMg
  · intro i
    rw [dist_comm]
    change dist (projectedL1 h hX π hπ _ _ _) (projectedL1 h hX π hπ _ _ _) < ε
    rw [dist_projectedL1]
    apply (fullSlice_cutoff_difference_bound h hX π hπ (b j).val.continuous.measurable hχ
      (hu i).continuous.measurable hC hB (hU i)).trans_lt
    apply lt_of_le_of_lt _ hj
    rw [←norm_value (hT := hT) (hu i)]
    exact mul_le_mul_of_nonneg_left (hMv i) (mul_nonneg (pow_nonneg K.coe_nonneg _) lpNorm_nonneg)

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Slicing Foundations MassMeasure BorelCoefficients JointBV

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma coordinate_distance_le (h : NormalApprox (k+1) T) (hX : IsCAT0 X) (i : ℕ)
    (F : Fin (k+1) → X → ℝ) {K J : ℝ≥0} (hF : ∀ a, LipschitzWith K (F a))
    (hJ : LipschitzWith J (q.chart i).param)
    (hFinv : ∀ z ∈ (q.chart i).domain, coordinateMap F ((q.chart i).paramExtended z) = z)
    (hjac : ∀ᵐ z ∂volume.restrict (q.chart i).domain, (q.chart i).jacobian F z = 1)
    {u v : X → ℝ} {L P : ℝ≥0} (hu : LipschitzWith L u) (hv : LipschitzWith P v)
    (U V : ℝ≥0) (hU : ∀ x, |u x| ≤ U) (hV : ∀ x, |v x| ≤ V) :
    dist (q.coordinateL1 i hu.continuous.measurable U hU) (q.coordinateL1 i hv.continuous.measurable V hV) ≤
      (J:ℝ)^(k+1)*dist (q.isolatedL1 h hX i F hF hu.continuous.measurable U hU)
        (q.isolatedL1 h hX i F hF hv.continuous.measurable V hV) := by
  rw [q.dist_coordinateL1,q.dist_isolatedL1 h hX i F hF hFinv hjac hu hv,←integral_const_mul]
  have hb x : abs |u x-v x| ≤ (U+V:ℝ≥0) := by
    rw [abs_abs]; exact (abs_sub _ _).trans (add_le_add (hU x) (hV x))
  have hm := (hu.continuous.measurable.sub hv.continuous.measurable).norm
  have hleft := integrable_weighted_comp (volume.restrict (q.chart i).domain)
    (q.chart i).measurable_paramExtended (q.density_integrable i) hm ⟨(U+V:ℝ≥0),hb⟩
  have hright := integrable_weighted_comp (volume.restrict (q.chart i).domain)
    (q.chart i).measurable_paramExtended (q.chart i).integrable.norm hm ⟨(U+V:ℝ≥0),hb⟩
  apply integral_mono_ae (by simpa only [Real.norm_eq_abs,Pi.sub_apply] using hleft)
    (by simpa only [Real.norm_eq_abs,Pi.sub_apply] using hright.const_mul ((J:ℝ)^(k+1)))
  filter_upwards [q.ae_chart_jacobian_le i hJ] with z hz
  dsimp only [density]
  calc _ ≤ |((q.chart i).multiplicity z:ℝ)| * ((J:ℝ)^(k+1))*|u ((q.chart i).paramExtended z)-v ((q.chart i).paramExtended z)| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz (abs_nonneg _)) (abs_nonneg _)
    _ = _ := by ring

theorem totallyBounded_coordinate {ι : Type*}
    (h : NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (u : ι → X → ℝ) (L U : ι → ℝ≥0) (hu : ∀ j, LipschitzWith (L j) (u j))
    (hU : ∀ j x, |u j x| ≤ U j)
    (M : ℝ≥0) (hMv : ∀ j, ‖value (hT := hT) (hu j)‖ ≤ M)
    (hMg : ∀ j, ‖q.gradient (hu j)‖ ≤ M) (i : ℕ) :
    TotallyBounded (range fun j => q.coordinateL1 i (hu j).continuous.measurable (U j) (hU j)) := by
  obtain ⟨F,K,hF,hFinv,hjac⟩ := q.exists_exact_inverse_coordinates i
  obtain ⟨J,J',hJ,hJ'⟩ := (q.chart i).bilipschitz
  have hib : ∀ x, |(q.chart i).image.indicator (fun _ => (1:ℝ)) x| ≤ (1:ℝ≥0) := by
    intro x; by_cases hx : x ∈ (q.chart i).image <;> simp [hx]
  have ht := q.totallyBounded_borel_projected h hz hX F hF u L U hu hU
    (measurable_const.indicator (q.chart i).measurableSet_image) 1 hib M hMv hMg
  have he : (fun j => projectedL1 h hX F hF ((measurable_const.indicator (q.chart i).measurableSet_image).mul (hu j).continuous.measurable) (1*U j) (mul_bounded hib (hU j))) =
      (fun j => q.isolatedL1 h hX i F hF (hu j).continuous.measurable (U j) (hU j)) := by
    funext j
    apply Lp.ext
    filter_upwards [(fullSlice_borel_integral h hX F (fun a => boundedLip_of_lipschitz (hF a))
      ((measurable_const.indicator (q.chart i).measurableSet_image).mul (hu j).continuous.measurable)
      (1*U j) (mul_bounded hib (hU j))).1.coeFn_toL1,
      (fullSlice_borel_integral h hX F (fun a => boundedLip_of_lipschitz (hF a))
      ((hu j).continuous.measurable.indicator (q.chart i).measurableSet_image)
      (U j) (q.indicator_bound i (hU j))).1.coeFn_toL1] with z hz hz'
    change _ = _ at hz hz'
    dsimp only [projectedL1,isolatedL1]
    rw [hz,hz']
    congr 2
    ext x
    by_cases hx : x ∈ (q.chart i).image <;> simp [hx]
  rw [he] at ht
  apply totallyBounded_range_of_control ht
  intro ε hε
  refine ⟨ε/((J:ℝ)^(k+1)+1),div_pos hε (by positivity),?_⟩
  intro a b hab
  apply (q.coordinate_distance_le h hX i F hF hJ hFinv hjac (hu a) (hu b) (U a) (U b) (hU a) (hU b)).trans_lt
  have hc := (lt_div_iff₀ (show 0 < (J:ℝ)^(k+1)+1 by positivity)).mp hab
  have hd : 0 ≤ dist (q.isolatedL1 h hX i F hF (hu a).continuous.measurable (U a) (hU a))
    (q.isolatedL1 h hX i F hF (hu b).continuous.measurable (U b) (hU b)) := dist_nonneg
  nlinarith [pow_nonneg J.coe_nonneg (k+1)]

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Tails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter Metric

namespace CAT0Fillings.JointBV
universe u v
lemma totallyBounded_range_of_finite_coordinate_control {ι : Type*} {α : Type u}
    [PseudoMetricSpace α] {β : ℕ → Type v} [∀ i, PseudoMetricSpace (β i)]
    [∀ i, CompleteSpace (β i)] {f : ι → α} {g : ∀ i, ι → β i}
    (hg : ∀ i, TotallyBounded (range (g i)))
    (hcontrol : ∀ ε > 0, ∃ N : ℕ, ∃ δ > 0,
      ∀ a b, (∀ i : Fin N, dist (g i a) (g i b) < δ) → dist (f a) (f b) < ε) :
    TotallyBounded (range f) := by
  classical
  apply Metric.totallyBounded_of_finite_discretization
  intro ε hε
  obtain ⟨N,δ,hδ,hc⟩ := hcontrol ε hε
  let G (a : ι) (i : Fin N) := g i a
  have hG : TotallyBounded (range G) := by
    apply (isCompact_pi_infinite (fun i : Fin N => ((hg i).closure.isCompact_of_isClosed isClosed_closure))).totallyBounded.subset
    rintro _ ⟨a,rfl⟩ i
    exact subset_closure (mem_range_self a)
  obtain ⟨s,hs,hfin,hcover⟩ := Metric.finite_approx_of_totallyBounded hG (δ/2) (half_pos hδ)
  have : Fintype s := hfin.fintype
  have hnear (a : ι) : ∃ y : s, dist (G a) y < δ/2 := by
    have := hcover (mem_range_self a)
    simp only [mem_iUnion,mem_ball] at this
    obtain ⟨y,hy,hay⟩ := this
    exact ⟨⟨y,hy⟩,hay⟩
  choose c hc' using hnear
  let pick (x : range f) : ι := x.property.choose
  have hp (x : range f) : f (pick x) = x := x.property.choose_spec
  refine ⟨ULift.{u} (Fin (Fintype.card s)),inferInstance,fun x => ULift.up ((Fintype.equivFin s) (c (pick x))),?_⟩
  intro x y he
  have he : c (pick x) = c (pick y) := (Fintype.equivFin s).injective (congrArg ULift.down he)
  rw [←hp x,←hp y]
  apply hc
  intro i
  apply (dist_le_pi_dist (G (pick x)) (G (pick y)) i).trans_lt
  calc dist (G (pick x)) (G (pick y)) ≤
      dist (G (pick x)) (c (pick x)) + dist (G (pick y)) (c (pick x)) := dist_triangle_right _ _ _
    _ < δ/2+δ/2 := add_lt_add (hc' _) (by rw [he]; exact hc' _)
    _ = δ := add_halves _

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.JointBV
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
  (ρ : α → ℕ) (hρ : Measurable ρ)

include hρ
lemma measurable_indexTail (N : ℕ) : Measurable (indexTail ρ N) :=
  measurable_const.ite (measurableSet_le measurable_const hρ) measurable_const

omit hρ in
lemma indexTail_bound {α : Type*} [MeasurableSpace α] (ρ : α → ℕ)
    (N : ℕ) (x : α) : |indexTail ρ N x| ≤ 1 := by
  unfold indexTail; split_ifs <;> norm_num

lemma memLp_indexTail (N : ℕ) : MemLp (indexTail ρ N) 2 μ :=
  MemLp.of_bound (measurable_indexTail ρ hρ N).aestronglyMeasurable 1
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using indexTail_bound ρ N x)

omit hρ in
lemma lpNorm_indexTail {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (ρ : α → ℕ) (hρ : Measurable ρ) (N : ℕ) :
    lpNorm (indexTail ρ N) 2 μ = (μ.real {x | N ≤ ρ x}) ^ (1/(2:ℝ)) := by
  have he : indexTail ρ N = {x | N ≤ ρ x}.indicator (fun _ => (1:ℝ)) := by
    ext x; simp only [indexTail,Set.indicator_apply,mem_ofPred_eq]
  rw [he, ←toReal_eLpNorm (aestronglyMeasurable_const.indicator (measurableSet_le measurable_const hρ)), eLpNorm_indicator_const₀ (s := {x | N ≤ ρ x})
    (measurableSet_le measurable_const hρ).nullMeasurableSet (by norm_num) (by norm_num)]
  simp [ENNReal.toReal_rpow,measureReal_def]

lemma tendsto_lpNorm_indexTail : Tendsto (fun N => lpNorm (indexTail ρ N) 2 μ) atTop (𝓝 0) := by
  have hsets : (⋂ N : ℕ, {x | N ≤ ρ x}) = ∅ := by
    ext x
    simp only [mem_iInter,mem_ofPred_eq,mem_empty_iff_false,iff_false]
    intro hx
    exact Nat.not_succ_le_self (ρ x) (hx (ρ x+1))
  have hm : Tendsto (fun N => μ {x | N ≤ ρ x}) atTop (𝓝 0) := by
    simpa only [Function.comp_def,hsets,measure_empty] using
      tendsto_measure_iInter_atTop (μ := μ) (fun N => (measurableSet_le measurable_const hρ).nullMeasurableSet)
        (show Antitone (fun N : ℕ => {x | N ≤ ρ x}) by intro N M hNM x hx; exact hNM.trans hx)
        ⟨0,measure_ne_top _ _⟩
  have hr : Tendsto (fun N => μ.real {x | N ≤ ρ x}) atTop (𝓝 0) := by
    simpa only [measureReal_def,ENNReal.toReal_zero,Function.comp_def] using (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞) ≠ ∞)).tendsto.comp hm
  simpa only [lpNorm_indexTail μ ρ hρ,Real.zero_rpow (by norm_num : (1/(2:ℝ)) ≠ 0)] using
    (hr.rpow_const (by norm_num : (0:ℝ) ≠ 0 ∨ 0 ≤ 1/(2:ℝ)))

end CAT0Fillings.JointBV
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Atlas
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

namespace CAT0Fillings.JointBV
variable {β : Type*} [MeasurableSpace β] (σ : ℕ → Measure β)
  (μ : Measure (ℕ × β)) [IsFiniteMeasure μ]
  (hμ : μ = Measure.sum (fun i => (σ i).map (Prod.mk i)))

include hμ
omit [IsFiniteMeasure μ] in
lemma integral_prefix [IsFiniteMeasure μ] {f : ℕ × β → ℝ} (hf : Integrable f μ) (N : ℕ) :
    (∫ w, (if w.1 < N then f w else 0) ∂μ) =
      ∑ i ∈ Finset.range N, ∫ z, f (i,z) ∂σ i := by
  have hs : MeasurableSet {w : ℕ × β | w.1 < N} := measurableSet_lt measurable_fst measurable_const
  have hi : Integrable (fun w : ℕ × β => if w.1 < N then f w else 0) μ := by
    apply (hf.indicator hs).congr
    filter_upwards [] with w
    by_cases hw : w.1 < N <;> simp [hw]
  rw [hμ] at hi ⊢
  rw [integral_sum_measure hi]
  have he (i : ℕ) : (∫ w : ℕ × β, (if w.1 < N then f w else 0) ∂(σ i).map (Prod.mk i)) =
      if i < N then ∫ z, f (i,z) ∂σ i else 0 := by
    rw [(measurableEmbedding_prodMk_left i).integral_map]
    by_cases hi : i < N <;> simp [hi]
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range N)]
  · apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [ite_eq_left hi]
  · intro i hi
    simp only [Finset.mem_range] at hi
    rw [ite_eq_right hi]

lemma integral_abs_le_finite_parts_add_tail {f : ℕ × β → ℝ}
    (hf : MemLp f 2 μ) (N : ℕ) :
    (∫ w, |f w| ∂μ) ≤ (∑ i ∈ Finset.range N, ∫ z, |f (i,z)| ∂σ i) +
      lpNorm f 2 μ*lpNorm (indexTail Prod.fst N) 2 μ := by
  have hi := (hf.integrable (by norm_num)).abs
  have hs : MeasurableSet {w : ℕ × β | w.1 < N} := measurableSet_lt measurable_fst measurable_const
  have hp : Integrable (fun w : ℕ × β => if w.1 < N then |f w| else 0) μ := by
    apply (hi.indicator hs).congr
    filter_upwards [] with w
    by_cases hw : w.1 < N <;> simp [hw]
  have ht : Integrable (fun w : ℕ × β => |f w| *|indexTail Prod.fst N w|) μ := by
    apply hi.mul_bdd (c := 1) (measurable_indexTail Prod.fst measurable_fst N).abs.aestronglyMeasurable
    exact Eventually.of_forall fun w => by
      simpa only [Real.norm_eq_abs,abs_abs] using indexTail_bound Prod.fst N w
  have he : (fun w => |f w|) = fun w => (if w.1 < N then |f w| else 0)+|f w| *|indexTail Prod.fst N w| := by
    ext w
    by_cases hw : w.1 < N
    · simp [indexTail,hw,Nat.not_le.mpr hw]
    · simp [indexTail,hw,Nat.le_of_not_gt hw]
  calc
    _ = (∫ w, (if w.1 < N then |f w| else 0) ∂μ)+(∫ w, |f w| *|indexTail Prod.fst N w| ∂μ) := by
      rw [←integral_add hp ht,←he]
    _ ≤ (∑ i ∈ Finset.range N, ∫ z, |f (i,z)| ∂σ i) +lpNorm f 2 μ*lpNorm (indexTail Prod.fst N) 2 μ := by
      rw [integral_prefix σ μ hμ hi N]
      exact add_le_add le_rfl (integral_abs_mul_le_lpNorm_two hf (memLp_indexTail μ Prod.fst measurable_fst N))

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BigOperators

namespace CAT0Fillings.ChartGeometry
open JointBV Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

omit [Nonempty X] in
lemma dist_value1 [Nonempty X] {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    dist (value1 (hT := hT) hu) (value1 hv) =
      ∫ x, |u x-v x| ∂MassMeasure.currentMassMeasure hT := by
  rw [dist_eq_norm,L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (value1 (hT := hT) hu) (value1 hv),
    ((boundedLip_of_lipschitz hu).memLp (μ := MassMeasure.currentMassMeasure hT) 1).coeFn_toLp,
    ((boundedLip_of_lipschitz hv).memLp (μ := MassMeasure.currentMassMeasure hT) 1).coeFn_toLp] with x hx hux hvx
  rw [hx]
  change ‖(((boundedLip_of_lipschitz hu).memLp 1).toLp u) x-
    (((boundedLip_of_lipschitz hv).memLp 1).toLp v) x‖ = _
  rw [hux,hvx,Real.norm_eq_abs]

lemma dist_coordinateL1_eq (i : ℕ) {u v : X → ℝ} (hu : Measurable u) (hv : Measurable v)
    (U V : ℝ≥0) (hU : ∀ x, |u x| ≤ U) (hV : ∀ x, |v x| ≤ V) :
    dist (q.coordinateL1 i hu U hU) (q.coordinateL1 i hv V hV) =
      ∫ z, |u ((q.chart i).paramExtended z)-v ((q.chart i).paramExtended z)| ∂q.coordinateMeasure i := by
  rw [q.dist_coordinateL1,coordinateMeasure,integral_withDensity_eq_integral_toReal_smul₀
    (q.density_integrable i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (q.density_nonneg i _),smul_eq_mul]

lemma dist_value1_le_prefix {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v)
    (U V : ℝ≥0) (hU : ∀ x, |u x| ≤ U) (hV : ∀ x, |v x| ≤ V) (N : ℕ) :
    dist (value1 (hT := hT) hu) (value1 hv) ≤
      (∑ i ∈ Finset.range N, dist (q.coordinateL1 i hu.continuous.measurable U hU)
        (q.coordinateL1 i hv.continuous.measurable V hV)) +
      (‖value (hT := hT) hu‖+‖value (hT := hT) hv‖)*lpNorm (indexTail Prod.fst N) 2 q.atlasMeasure := by
  let μ := MassMeasure.currentMassMeasure hT
  have hmp : MeasurePreserving q.atlasParam q.atlasMeasure μ := ⟨q.measurable_atlasParam,q.map_atlasMeasure⟩
  have hmem : MemLp (fun x => u x-v x) 2 μ := ((boundedLip_of_lipschitz hu).memLp 2).sub ((boundedLip_of_lipschitz hv).memLp 2)
  have hma := hmem.comp_measurePreserving hmp
  have hh := integral_abs_le_finite_parts_add_tail q.coordinateMeasure q.atlasMeasure rfl hma N
  have hleft : (∫ w, |u (q.atlasParam w)-v (q.atlasParam w)| ∂q.atlasMeasure) =
      dist (value1 (hT := hT) hu) (value1 hv) := by
    rw [dist_value1,←q.map_atlasMeasure]
    symm
    simpa only [Pi.sub_apply] using integral_map q.measurable_atlasParam.aemeasurable
      (hu.continuous.sub hv.continuous).abs.aestronglyMeasurable
  change (∫ w, |u (q.atlasParam w)-v (q.atlasParam w)| ∂q.atlasMeasure) ≤ _ at hh
  rw [hleft] at hh
  have hnorm : lpNorm ((fun x => u x-v x) ∘ q.atlasParam) 2 q.atlasMeasure ≤
      ‖value (hT := hT) hu‖+‖value (hT := hT) hv‖ := by
    rw [←toReal_eLpNorm hma.aestronglyMeasurable,eLpNorm_comp_measurePreserving hmem.aestronglyMeasurable hmp]
    have he : hmem.toLp _ = value (hT := hT) hu-value hv :=
      MemLp.toLp_sub ((boundedLip_of_lipschitz hu).memLp 2) ((boundedLip_of_lipschitz hv).memLp 2)
    rw [←Lp.norm_toLp (fun x => u x-v x) hmem,he]
    exact norm_sub_le _ _
  apply hh.trans
  apply add_le_add
  · apply Finset.sum_le_sum
    intro index _
    rw [q.dist_coordinateL1_eq]
    rfl
  · exact mul_le_mul_of_nonneg_right hnorm lpNorm_nonneg

theorem totallyBounded_value1 {ι : Type*}
    (h : Slicing.NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (u : ι → X → ℝ) (L U : ι → ℝ≥0) (hu : ∀ j, LipschitzWith (L j) (u j))
    (hU : ∀ j x, |u j x| ≤ U j)
    (M : ℝ≥0) (hMv : ∀ j, ‖value (hT := hT) (hu j)‖ ≤ M)
    (hMg : ∀ j, ‖q.gradient (hu j)‖ ≤ M) :
    TotallyBounded (range fun j => value1 (hT := hT) (hu j)) := by
  apply totallyBounded_range_of_finite_coordinate_control
    (q.totallyBounded_coordinate h hz hX u L U hu hU M hMv hMg)
  intro ε hε
  have ht := (tendsto_lpNorm_indexTail q.atlasMeasure Prod.fst measurable_fst).const_mul (2*(M:ℝ))
  rw [mul_zero] at ht
  obtain ⟨N,hN⟩ := ((tendsto_order.1 ht).2 (ε/2) (half_pos hε)).exists
  refine ⟨N,ε/(2*((N:ℝ)+1)),div_pos hε (by positivity),?_⟩
  intro a b hab
  have hh := q.dist_value1_le_prefix (hu a) (hu b) (U a) (U b) (hU a) (hU b) N
  have hs : (∑ i ∈ Finset.range N, dist (q.coordinateL1 i (hu a).continuous.measurable (U a) (hU a))
      (q.coordinateL1 i (hu b).continuous.measurable (U b) (hU b))) ≤ (N:ℝ)*(ε/(2*((N:ℝ)+1))) := by
    calc _ ≤ ∑ _i ∈ Finset.range N, ε/(2*((N:ℝ)+1)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact (hab ⟨i,Finset.mem_range.mp hi⟩).le
      _ = _ := by simp
  have hp := mul_le_mul_of_nonneg_right (add_le_add (hMv a) (hMv b))
    (show 0 ≤ lpNorm (indexTail Prod.fst N) 2 q.atlasMeasure from lpNorm_nonneg)
  have hd : (N:ℝ)*(ε/(2*((N:ℝ)+1))) < ε/2 := by
    have he : (N:ℝ)*(ε/(2*((N:ℝ)+1))) = (ε/2)*((N:ℝ)/((N:ℝ)+1)) := by field_simp
    rw [he]
    apply mul_lt_of_lt_one_right (half_pos hε)
    exact (div_lt_one (by positivity)).2 (by linarith)
  have : (M:ℝ)+(M:ℝ) = 2*(M:ℝ) := by ring
  rw [this] at hp
  linarith

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Compactness_Interpolation
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.JointBV
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}

lemma lintegral_enorm_rpow_eq (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖f x‖ₑ^p ∂μ) = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hp.le,←ENNReal.rpow_mul]
  simp [hp.ne']

lemma eLpNorm_two_interpolation (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 2 < p) :
    eLpNorm f 2 μ ^ (2:ℝ) ≤ eLpNorm f 1 μ ^ ((p-2)/(p-1)) *
      eLpNorm f (ENNReal.ofReal p) μ ^ (p/(p-1)) := by
  have hp1 : 0 < p-1 := by linarith
  let a := (p-2)/(p-1)
  let b := 1/(p-1)
  have ha : 0 ≤ a := div_nonneg (by linarith) hp1.le
  have hb : 0 ≤ b := div_nonneg zero_le_one hp1.le
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have hsum : a+p*b=2 := by dsimp [a,b]; field_simp; ring
  have hh := ENNReal.lintegral_mul_norm_pow_le hf.aemeasurable.enorm
    (hf.aemeasurable.enorm.pow_const p) ha hb hab
  have he : (fun x => ‖f x‖ₑ^a*(‖f x‖ₑ^p)^b) = fun x => ‖f x‖ₑ^(2:ℝ) := by
    ext x
    rw [←ENNReal.rpow_mul,←ENNReal.rpow_add_of_nonneg a (p*b) ha (mul_nonneg (by linarith) hb),hsum]
  rw [he,lintegral_enorm_rpow_eq hf (by norm_num : (0:ℝ)<2),
    lintegral_enorm_rpow_eq hf (by linarith : 0<p),←eLpNorm_one_eq_lintegral_enorm,
    ←ENNReal.rpow_mul] at hh
  simpa only [ENNReal.ofReal_ofNat,a,b,mul_one_div] using hh

lemma lpNorm_two_sq_interpolation (h1 : MemLp f 1 μ) {p : ℝ} (hp : 2 < p)
    (hpMem : MemLp f (ENNReal.ofReal p) μ) :
    lpNorm f 2 μ ^ 2 ≤ lpNorm f 1 μ ^ ((p-2)/(p-1)) *
      lpNorm f (ENNReal.ofReal p) μ ^ (p/(p-1)) := by
  have hh := eLpNorm_two_interpolation h1.aestronglyMeasurable hp
  have hp1 : 0 < p-1 := by linarith
  have hp2 : 0 < p-2 := by linarith
  have hp0 : 0 < p := by linarith
  have hr : eLpNorm f 1 μ ^ ((p-2)/(p-1)) * eLpNorm f (ENNReal.ofReal p) μ ^ (p/(p-1)) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg (by positivity) h1.eLpNorm_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg (by positivity) hpMem.eLpNorm_ne_top
  have hh' := ENNReal.toReal_mono hr hh
  simpa only [ENNReal.toReal_mul,←ENNReal.toReal_rpow,toReal_eLpNorm h1.aestronglyMeasurable,
    Real.rpow_two] using hh'

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open JointBV Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

omit [Nonempty X] in
lemma dist_value [Nonempty X] {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    dist (value (hT := hT) hu) (value hv) =
      lpNorm (fun x => u x-v x) 2 (MassMeasure.currentMassMeasure hT) := by
  rw [dist_eq_norm,value,value,←MemLp.toLp_sub ((boundedLip_of_lipschitz hu).memLp 2)
    ((boundedLip_of_lipschitz hv).memLp 2),Lp.norm_toLp,toReal_eLpNorm (hu.continuous.sub hv.continuous).aestronglyMeasurable]
  rfl

lemma totallyBounded_value_of_lpBound {ι : Type*} {p : ℝ} (hp : 2 < p)
    (u : ι → X → ℝ) (L : ι → ℝ≥0) (hu : ∀ j, LipschitzWith (L j) (u j))
    (h1 : TotallyBounded (range fun j => value1 (hT := hT) (hu j)))
    (C : ℝ≥0) (hC : ∀ j, lpNorm (u j) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) ≤ C) :
    TotallyBounded (range fun j => value (hT := hT) (hu j)) := by
  let μ := MassMeasure.currentMassMeasure hT
  let a := (p-2)/(p-1)
  let b := p/(p-1)
  have ha : 0 < a := div_pos (by linarith) (by linarith)
  have hb : 0 ≤ b := div_nonneg (by linarith) (by linarith)
  have hp' : 1 ≤ ENNReal.ofReal p := by rw [←ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  apply totallyBounded_range_of_control h1
  intro ε hε
  have ht : Tendsto (fun t : ℝ => t^a*(2*(C:ℝ))^b) (𝓝 0) (𝓝 0) := by
    simpa only [id_eq,Real.zero_rpow ha.ne',zero_mul] using
      ((continuous_id.tendsto (0:ℝ)).rpow_const (Or.inr ha.le)).mul_const ((2*(C:ℝ))^b)
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp (ht (Iio_mem_nhds (sq_pos_of_pos hε)))
  refine ⟨δ,hδ,?_⟩
  intro i j hij
  have hmem1 : MemLp (fun x => u i x-u j x) 1 μ :=
    ((boundedLip_of_lipschitz (hu i)).memLp 1).sub ((boundedLip_of_lipschitz (hu j)).memLp 1)
  have hmemp : MemLp (fun x => u i x-u j x) (ENNReal.ofReal p) μ :=
    ((boundedLip_of_lipschitz (hu i)).memLp _).sub ((boundedLip_of_lipschitz (hu j)).memLp _)
  have hh := lpNorm_two_sq_interpolation hmem1 hp hmemp
  have he1 : lpNorm (fun x => u i x-u j x) 1 μ = dist (value1 (hT := hT) (hu i)) (value1 (hu j)) := by
    rw [dist_value1,lpNorm_one_eq_integral_norm hmem1.aestronglyMeasurable]
    rfl
  have hep : lpNorm (fun x => u i x-u j x) (ENNReal.ofReal p) μ ≤ 2*(C:ℝ) := by
    have hh := lpNorm_sub_le (g := u j) ((boundedLip_of_lipschitz (hu i)).memLp (μ := μ) (ENNReal.ofReal p)) hp'
    change lpNorm (u i-u j) (ENNReal.ofReal p) μ ≤ 2*(C:ℝ)
    exact hh.trans ((add_le_add (hC i) (hC j)).trans_eq (by ring))
  have hmono := Real.rpow_le_rpow lpNorm_nonneg hep hb
  have hsmall : (dist (value1 (hT := hT) (hu i)) (value1 (hu j)))^a*(2*(C:ℝ))^b < ε^2 := by
    apply hd
    simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg] using hij
  rw [he1] at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg dist_nonneg a))
  have hd2 := (hh'.trans_lt hsmall)
  rw [←dist_value (hT := hT) (hu i) (hu j)] at hd2
  nlinarith [dist_nonneg (x := value (hT := hT) (hu i)) (y := value (hT := hT) (hu j))]

theorem totallyBounded_value {ι : Type*}
    (h : Slicing.NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (u : ι → X → ℝ) (L U : ι → ℝ≥0) (hu : ∀ j, LipschitzWith (L j) (u j))
    (hU : ∀ j x, |u j x| ≤ U j)
    (M : ℝ≥0) (hMv : ∀ j, ‖value (hT := hT) (hu j)‖ ≤ M)
    (hMg : ∀ j, ‖q.gradient (hu j)‖ ≤ M)
    {p : ℝ} (hp : 2 < p) (C : ℝ≥0)
    (hC : ∀ j, lpNorm (u j) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) ≤ C) :
    TotallyBounded (range fun j => value (hT := hT) (hu j)) :=
  totallyBounded_value_of_lpBound (hT := hT) hp u L hu
    (q.totallyBounded_value1 h hz hX u L U hu hU M hMv hMg) C hC

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_Completion
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma graph_norm_sq (P : q.GraphAmbient) :
    ‖P‖^2 = ‖q.valueProjection P‖^2+‖q.gradientProjection P‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 P

end CAT0Fillings.ChartGeometry
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Sobolev_Compact
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open JointBV Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma norm_valueProjection_le (P : q.GraphAmbient) : ‖q.valueProjection P‖ ≤ ‖P‖ := by
  have := q.graph_norm_sq P
  nlinarith [norm_nonneg P,sq_nonneg ‖q.gradientProjection P‖]
lemma norm_gradientProjection_le (P : q.GraphAmbient) : ‖q.gradientProjection P‖ ≤ ‖P‖ := by
  have := q.graph_norm_sq P
  nlinarith [norm_nonneg P,sq_nonneg ‖q.valueProjection P‖]

lemma totallyBounded_inclusion {ι : Type*}
    (h : Slicing.NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    {p A B C : ℝ} (hp : 2 < p) (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
      A*lpNorm u (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT)^2 ≤
        B*(q.energyMeasure u).real univ+C*lpNorm u 2 (MassMeasure.currentMassMeasure hT)^2)
    (P : ι → q.Sobolev) (M : ℝ≥0) (hM : ∀ i, ‖P i‖ ≤ M) :
    TotallyBounded (range fun i => q.inclusion (P i)) := by
  classical
  apply totallyBounded_range_of_uniform_approx
  intro ε hε
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  have ha (i : ι) : ∃ (u : X → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u),
      dist (P i : q.GraphAmbient) (q.graphPoint hu) < δ := by
    have hm : (P i : q.GraphAmbient) ∈ closure (q.lipschitzGraph : Set q.GraphAmbient) := (P i).property
    obtain ⟨b,hb,hnear⟩ := Metric.mem_closure_iff.mp hm δ hδ
    obtain ⟨u,K,hu,rfl⟩ := hb
    exact ⟨u,K,hu,hnear⟩
  choose u K hu hd using ha
  have hn (i : ι) : ‖q.graphPoint (hu i)‖ ≤ (M:ℝ)+1 := by
    have hh := norm_add_le (q.graphPoint (hu i)-(P i : q.GraphAmbient)) (P i : q.GraphAmbient)
    rw [sub_add_cancel,←dist_eq_norm,dist_comm] at hh
    have hb : dist (P i : q.GraphAmbient) (q.graphPoint (hu i)) < 1 := (hd i).trans_le (min_le_right _ _)
    have hMi : ‖(P i : q.GraphAmbient)‖ ≤ M := hM i
    linarith
  have hv (i : ι) : ‖value (hT := hT) (hu i)‖ ≤ (M:ℝ)+1 :=
    (q.norm_valueProjection_le (q.graphPoint (hu i))).trans (hn i)
  have hg (i : ι) : ‖q.gradient (hu i)‖ ≤ (M:ℝ)+1 :=
    (q.norm_gradientProjection_le (q.graphPoint (hu i))).trans (hn i)
  have hUi (i : ι) : ∃ U : ℝ≥0, ∀ x, |u i x| ≤ U := by
    obtain ⟨R,hR⟩ := (boundedLip_of_lipschitz (hu i)).2
    exact ⟨⟨max R 0,le_max_right _ _⟩,fun x => (hR x).trans (le_max_left _ _)⟩
  choose U hU using hUi
  let D := Real.sqrt (((B+C)*((M:ℝ)+1)^2)/A)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have huv (i : ι) : lpNorm (u i) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) ≤ D := by
    apply (Real.le_sqrt lpNorm_nonneg (div_nonneg (mul_nonneg (add_nonneg hB hC) (sq_nonneg _)) hA.le)).mpr
    apply (le_div_iff₀ hA).mpr
    have hh := hb (u i) (K i) (hu i)
    rw [←q.gradient_norm_sq (hu i),←norm_value (hu i)] at hh
    have hv2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (M:ℝ)+1)).mpr (hv i)
    have hg2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (M:ℝ)+1)).mpr (hg i)
    nlinarith [mul_le_mul_of_nonneg_left hv2 hC,mul_le_mul_of_nonneg_left hg2 hB]
  refine ⟨fun i => value (hT := hT) (hu i),
    q.totallyBounded_value h hz hX u K U hu hU (M+1) hv hg hp ⟨D,hD⟩ huv,?_⟩
  intro i
  have hh := q.norm_valueProjection_le ((P i : q.GraphAmbient)-q.graphPoint (hu i))
  rw [map_sub] at hh
  have hh' : dist (q.inclusion (P i)) (value (hT := hT) (hu i)) ≤
      dist (P i : q.GraphAmbient) (q.graphPoint (hu i)) := by
        simpa [dist_eq_norm,inclusion] using hh
  exact hh'.trans_lt ((hd i).trans_le (min_le_left _ _))

theorem inclusion_compact_oai
    (h : Slicing.NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    {p A B C : ℝ} (hp : 2 < p) (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
      A*lpNorm u (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT)^2 ≤
        B*(q.energyMeasure u).real univ+C*lpNorm u 2 (MassMeasure.currentMassMeasure hT)^2) :
    IsCompactOperator q.inclusion := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall q.inclusion.toLinearMap zero_lt_one).mpr
  have ht := q.totallyBounded_inclusion h hz hX hp hA hB hC hb
    (fun P : closedBall (0 : q.Sobolev) 1 => (P : q.Sobolev)) 1
    (fun P => by simpa only [mem_closedBall,dist_zero_right,NNReal.coe_one] using P.property)
  have he : (range fun P : closedBall (0 : q.Sobolev) 1 => q.inclusion (P : q.Sobolev)) =
      q.inclusion '' closedBall 0 1 := by ext u; simp
  rw [he] at ht
  exact isCompact_iff_totallyBounded_isComplete.mpr ⟨ht.closure,isClosed_closure.isComplete⟩

end CAT0Fillings.ChartGeometry
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.ChartGeometry.inclusion_compact_oai.{u_1} := @OAI.CAT0Fillings.ChartGeometry.inclusion_compact_oai.{u_1}
