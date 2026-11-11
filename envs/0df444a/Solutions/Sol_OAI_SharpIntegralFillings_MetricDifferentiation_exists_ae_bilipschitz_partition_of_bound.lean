-- Prove2me | solution 1 for OAI.SharpIntegralFillings.MetricDifferentiation.exists_ae_bilipschitz_partition_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:36:12.685318+00:00
-- url     : https://prove2.me/submissions/1267ad09-d450-45d2-a5c9-61eb269d327a

import Mathlib
import Definitions.Def_OAIQ219IF000

section
-- module Solutions.OAIQ219_IF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_CurveSpeed
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiationDense
variable {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X] {f : ℝ → X} {K : ℝ≥0}

lemma coordinate_lipschitz (hf : LipschitzWith K f) (q : ℕ) :
    LipschitzWith K (distanceCoordinate f q) := by
  change LipschitzWith K (fun t : ℝ => dist (f t) (denseSeq X q))
  simpa only [Function.comp_def, one_mul] using (LipschitzWith.dist_left (denseSeq X q)).comp hf

lemma coordinate_deriv_bound (hf : LipschitzWith K f) (q : ℕ) (t : ℝ) :
    |deriv (distanceCoordinate f q) t| ≤ K := by
  simpa [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (coordinate_lipschitz hf q)

lemma coordinate_deriv_le_speed (hf : LipschitzWith K f) (q : ℕ) (t : ℝ) :
    |deriv (distanceCoordinate f q) t| ≤ metricSpeed f t :=
  le_ciSup ⟨(K : ℝ), by rintro v ⟨r, rfl⟩; exact coordinate_deriv_bound hf r t⟩ q

lemma metricSpeed_nonneg (hf : LipschitzWith K f) (t : ℝ) : 0 ≤ metricSpeed f t :=
  (abs_nonneg _).trans (coordinate_deriv_le_speed hf 0 t)

lemma metricSpeed_le (hf : LipschitzWith K f) (t : ℝ) : metricSpeed f t ≤ K :=
  ciSup_le (fun q => coordinate_deriv_bound hf q t)

lemma measurable_metricSpeed (f : ℝ → X) : Measurable (metricSpeed f) :=
  Measurable.iSup (fun q => (measurable_deriv (distanceCoordinate f q)).abs)

lemma locallyIntegrable_metricSpeed (hf : LipschitzWith K f) :
    LocallyIntegrable (metricSpeed f) volume := by
  apply (memLp_top_of_bound (measurable_metricSpeed f).aestronglyMeasurable (K : ℝ) ?_).locallyIntegrable le_top
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (metricSpeed_nonneg hf t)]
    exact metricSpeed_le hf t

lemma intervalIntegrable_metricSpeed (hf : LipschitzWith K f) (s t : ℝ) :
    IntervalIntegrable (metricSpeed f) volume s t :=
  intervalIntegrable_iff.mpr
    (((locallyIntegrable_metricSpeed hf).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

lemma coordinate_difference_bound (hf : LipschitzWith K f) (q : ℕ) {s t : ℝ} (hst : s ≤ t) :
    |distanceCoordinate f q t - distanceCoordinate f q s| ≤ ∫ x in s..t, metricSpeed f x := by
  have hac := (coordinate_lipschitz hf q).lipschitzOnWith.absolutelyContinuousOnInterval (a := s) (b := t)
  rw [← hac.integral_deriv_eq_sub, ← Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_integral_norm hst).trans
  apply intervalIntegral.integral_mono_on hst hac.intervalIntegrable_deriv.norm
    (intervalIntegrable_metricSpeed hf s t)
  intro x hx
  exact coordinate_deriv_le_speed hf q x

lemma distance_le_integral_speed (hf : LipschitzWith K f) {s t : ℝ} (hst : s ≤ t) :
    dist (f t) (f s) ≤ ∫ x in s..t, metricSpeed f x := by
  have hc : Continuous (fun y : X => |dist (f t) y - dist (f s) y|) :=
    ((continuous_const.dist continuous_id).sub (continuous_const.dist continuous_id)).abs
  have h := (denseRange_denseSeq X).induction_on
    (p := fun y : X => |dist (f t) y - dist (f s) y| ≤
      ∫ x in s..t, metricSpeed f x) (f s) (isClosed_le hc continuous_const)
      (fun q => coordinate_difference_bound hf q hst)
  simpa using h

lemma distance_le_integratedSpeed (hf : LipschitzWith K f) (s t : ℝ) :
    dist (f t) (f s) ≤ |integratedSpeed f t - integratedSpeed f s| := by
  have hi (a b : ℝ) := intervalIntegrable_metricSpeed hf a b
  have hd (a b : ℝ) : integratedSpeed f b - integratedSpeed f a =
      ∫ x in a..b, metricSpeed f x := by
    exact intervalIntegral.integral_interval_sub_left (hi 0 b) (hi 0 a)
  rcases le_total s t with hst | hts
  · rw [hd s t, abs_of_nonneg (intervalIntegral.integral_nonneg hst
      (fun x hx => metricSpeed_nonneg hf x))]
    exact distance_le_integral_speed hf hst
  · rw [abs_sub_comm, hd t s, abs_of_nonneg (intervalIntegral.integral_nonneg hts
      (fun x hx => metricSpeed_nonneg hf x)), dist_comm]
    exact distance_le_integral_speed hf hts

lemma abs_slope_tendsto {g : ℝ → ℝ} {d x : ℝ} (hd : HasDerivAt g d x) :
    Tendsto (fun t => |g t-g x|/|t-x|) (𝓝[≠] x) (𝓝 |d|) := by
  simpa only [slope, norm_smul, norm_inv, Real.norm_eq_abs, vsub_eq_sub, div_eq_mul_inv, mul_comm]
    using hd.tendsto_slope.norm

theorem ae_hasMetricDerivAt (hf : LipschitzWith K f) :
    ∀ᵐ x, HasMetricDerivAt f (metricSpeed f x) x := by
  have hcoords : ∀ᵐ x, ∀ q : ℕ, DifferentiableAt ℝ (distanceCoordinate f q) x := by
    rw [ae_all_iff]
    intro q
    exact (coordinate_lipschitz hf q).ae_differentiableAt_real
  have hint := LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_metricSpeed hf)
  filter_upwards [hcoords, hint] with x hx hI
  have hg := abs_slope_tendsto (hI 0)
  rw [abs_of_nonneg (metricSpeed_nonneg hf x)] at hg
  change Tendsto (fun t => |integratedSpeed f t-integratedSpeed f x|/|t-x|)
    (𝓝[≠] x) (𝓝 (metricSpeed f x)) at hg
  apply tendsto_order.mpr
  constructor
  · intro c hc
    have hb : BddAbove (range (fun q : ℕ => |deriv (distanceCoordinate f q) x|)) :=
      ⟨(K : ℝ), by rintro v ⟨q, rfl⟩; exact coordinate_deriv_bound hf q x⟩
    obtain ⟨q, hq⟩ := (lt_ciSup_iff hb).mp hc
    have hd := abs_slope_tendsto (hx q).hasDerivAt
    filter_upwards [hd.eventually (eventually_gt_nhds hq)] with t ht
    exact ht.trans_le (div_le_div_of_nonneg_right
      (abs_dist_sub_le (f t) (f x) (denseSeq X q)) (abs_nonneg _))
  · intro c hc
    filter_upwards [hg.eventually (eventually_lt_nhds hc)] with t ht
    exact (div_le_div_of_nonneg_right (distance_le_integratedSpeed hf x t) (abs_nonneg _)).trans_lt ht

end SharpIntegralFillings.MetricDifferentiationDense

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Directional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
variable {X : Type*} [MetricSpace X]

lemma signedDistance_zero (c : ℝ → X) : signedDistance c 0 = 0 := by
  simp [signedDistance]

lemma signedDistance_div (c : ℝ → X) (t : ℝ) :
    signedDistance c t / t = dist (c t) (c 0) / |t| := by
  rcases le_total 0 t with ht | ht
  · simp [signedDistance, ht, abs_of_nonneg ht]
  · by_cases h0 : t = 0
    · simp [h0]
    · simp [signedDistance, not_le.mpr (lt_of_le_of_ne ht h0), abs_of_nonpos ht, neg_div, div_neg]

lemma hasDerivAt_signedDistance_iff (c : ℝ → X) (d : ℝ) :
    HasDerivAt (signedDistance c) d 0 ↔
      Tendsto (fun t => dist (c t) (c 0) / |t|) (𝓝[≠] 0) (𝓝 d) := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  simp only [zero_add, signedDistance_zero, sub_zero, smul_eq_mul, ← div_eq_inv_mul,
    signedDistance_div]

lemma continuous_signedDistance {A : Type*} [TopologicalSpace A] {c : A → ℝ → X}
    (hc : Continuous c.uncurry) : Continuous (fun p : A × ℝ => signedDistance (c p.1) p.2) := by
  have hd : Continuous (fun p : A × ℝ => dist (c p.1 p.2) (c p.1 0)) :=
    hc.dist (hc.comp (continuous_fst.prodMk continuous_const))
  exact hd.if_le hd.neg continuous_const continuous_snd (by
    rintro ⟨x,t⟩ (h : 0 = t)
    simp [← h])

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] [NormedSpace ℝ E] in
lemma scalarCoordinate_lipschitz (hf : LipschitzWith K f) (q : ℕ) :
    LipschitzWith K (scalarCoordinate f q) := by
  change LipschitzWith K (fun x : E => dist (f x) (denseSeq X q))
  simpa only [Function.comp_def, one_mul] using
    (LipschitzWith.dist_left (denseSeq X q)).comp hf

lemma measurable_lineSpeed (hf : Continuous f) (v : E) : Measurable (lineSpeed f v) := by
  apply Measurable.iSup
  intro q
  exact (measurable_lineDeriv (hf.dist continuous_const)).abs

omit [MeasurableSpace E] [BorelSpace E] in
lemma deriv_coordinate_line (p v : E) (s : ℝ) (q : ℕ) :
    deriv (MetricDifferentiationDense.distanceCoordinate (fun t => f (p+t • v)) q) s =
      lineDeriv ℝ (scalarCoordinate f q) (p+s • v) v := by
  rw [lineDeriv]
  have he : (fun t : ℝ => scalarCoordinate f q (p+s • v+t • v)) =
      (fun t : ℝ => MetricDifferentiationDense.distanceCoordinate (fun t => f (p+t • v)) q (s+t)) := by
    ext t
    simp [scalarCoordinate, MetricDifferentiationDense.distanceCoordinate, add_smul, add_assoc]
  rw [he]
  simpa using (deriv_comp_const_add (f := MetricDifferentiationDense.distanceCoordinate
    (fun t => f (p+t • v)) q) s 0).symm

omit [MeasurableSpace E] [BorelSpace E] in
lemma lineSpeed_eq_curveSpeed (p v : E) (s : ℝ) :
    lineSpeed f v (p+s • v) = MetricDifferentiationDense.metricSpeed (fun t => f (p+t • v)) s := by
  simp only [lineSpeed, MetricDifferentiationDense.metricSpeed, deriv_coordinate_line]

lemma measurableSet_hasMetricDirectionalDeriv (hf : Continuous f) (v : E) :
    MeasurableSet {x | Tendsto (fun t : ℝ => dist (f (x+t • v)) (f x) / |t|)
      (𝓝[≠] 0) (𝓝 (lineSpeed f v x))} := by
  let c : E → ℝ → X := fun x t => f (x + t • v)
  have hc : Continuous c.uncurry := hf.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hD := measurableSet_of_differentiableAt_with_param ℝ
    (f := fun x t => signedDistance (c x) t) (continuous_signedDistance hc)
  have hder := measurable_deriv_with_param (f := fun x t => signedDistance (c x) t)
    (continuous_signedDistance hc)
  have hm := (measurable_prodMk_right (y := (0 : ℝ)) hD).inter
    (measurableSet_eq_fun (hder.comp (measurable_prodMk_right (y := (0 : ℝ)))) (measurable_lineSpeed hf v))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff]
  constructor
  · intro ht
    have hd := (hasDerivAt_signedDistance_iff (c x) (lineSpeed f v x)).mpr (by simpa [c] using ht)
    exact ⟨hd.differentiableAt, hd.deriv⟩
  · rintro ⟨hd, he⟩
    rw [← he]
    simpa [c] using (hasDerivAt_signedDistance_iff (c x) _).mp hd.hasDerivAt

lemma tendsto_add_zero_punctured (s : ℝ) :
    Tendsto (fun t : ℝ => s+t) (𝓝[≠] 0) (𝓝[≠] s) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => s) (𝓝 0) (𝓝 s)).add tendsto_id).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    simpa using ht

theorem ae_hasMetricDirectionalDeriv [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f) (v : E) :
    ∀ᵐ x ∂μ, Tendsto (fun t : ℝ => dist (f (x+t • v)) (f x) / |t|)
      (𝓝[≠] 0) (𝓝 (lineSpeed f v x)) := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  apply ae_mem_of_ae_add_linearMap_mem L.toLinearMap volume μ
    (measurableSet_hasMetricDirectionalDeriv hf.continuous v)
  intro p
  have hcurve := hf.comp ((LipschitzWith.const p).add L.lipschitz)
  filter_upwards [MetricDifferentiationDense.ae_hasMetricDerivAt hcurve] with s hs
  change Tendsto (fun t : ℝ => dist (f (p+s • v+t • v)) (f (p+s • v)) / |t|)
    (𝓝[≠] 0) (𝓝 (lineSpeed f v (p+s • v)))
  rw [lineSpeed_eq_curveSpeed]
  have hh := hs.comp (tendsto_add_zero_punctured s)
  simpa only [Function.comp_def, L, MetricDifferentiationDense.HasMetricDerivAt,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, smul_eq_mul,
    add_smul, add_assoc, add_sub_cancel_left] using hh

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Seminorm
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

lemma coordinateSeminorm_le (hf : LipschitzWith K f) (x : E) (q : ℕ) :
    coordinateSeminorm f x q ≤ K • normSeminorm ℝ E := by
  intro v
  change ‖fderiv ℝ (scalarCoordinate f q) x v‖ ≤ (K : ℝ) * ‖v‖
  exact (ContinuousLinearMap.le_opNorm _ v).trans (mul_le_mul_of_nonneg_right
    (norm_fderiv_le_of_lipschitz ℝ (scalarCoordinate_lipschitz hf q)) (norm_nonneg _))

lemma bddAbove_coordinateSeminorm (hf : LipschitzWith K f) (x : E) :
    BddAbove (range (coordinateSeminorm f x)) :=
  ⟨K • normSeminorm ℝ E, by rintro p ⟨q,rfl⟩; exact coordinateSeminorm_le hf x q⟩

lemma metricSeminorm_apply (hf : LipschitzWith K f) (x v : E) :
    metricSeminorm f x v = ⨆ q : ℕ, |fderiv ℝ (scalarCoordinate f q) x v| := by
  rw [metricSeminorm, Seminorm.iSup_apply (bddAbove_coordinateSeminorm hf x)]
  rfl

lemma metricSeminorm_le (hf : LipschitzWith K f) (x v : E) :
    metricSeminorm f x v ≤ (K : ℝ) * ‖v‖ :=
  (ciSup_le (fun q => coordinateSeminorm_le hf x q) :
    metricSeminorm f x ≤ K • normSeminorm ℝ E) v

lemma metricSeminorm_lipschitz (hf : LipschitzWith K f) (x : E) :
    LipschitzWith K (metricSeminorm f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  rw [Real.dist_eq, ← Real.norm_eq_abs, dist_eq_norm]
  exact ((metricSeminorm f x).norm_sub_map_le_sub v w).trans (metricSeminorm_le hf x (v-w))

lemma lineSpeed_eq_metricSeminorm (hf : LipschitzWith K f) {x : E}
    (hx : ∀ q : ℕ, DifferentiableAt ℝ (scalarCoordinate f q) x) (v : E) :
    lineSpeed f v x = metricSeminorm f x v := by
  rw [metricSeminorm_apply hf]
  simp only [lineSpeed, (hx _).lineDeriv_eq_fderiv]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem ae_dense_directionalSeminorm (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, ∀ j : ℕ,
      Tendsto (fun t : ℝ => dist (f (x+t • denseSeq E j)) (f x) / |t|)
        (𝓝[≠] 0) (𝓝 (metricSeminorm f x (denseSeq E j))) := by
  have hcoord : ∀ᵐ x ∂μ, ∀ q : ℕ, DifferentiableAt ℝ (scalarCoordinate f q) x := by
    rw [ae_all_iff]
    exact fun q => (scalarCoordinate_lipschitz hf q).ae_differentiableAt
  have hdir : ∀ᵐ x ∂μ, ∀ j : ℕ,
      Tendsto (fun t : ℝ => dist (f (x+t • denseSeq E j)) (f x) / |t|)
        (𝓝[≠] 0) (𝓝 (lineSpeed f (denseSeq E j) x)) := by
    rw [ae_all_iff]
    exact fun j => ae_hasMetricDirectionalDeriv μ hf _
  filter_upwards [hcoord, hdir] with x hx hd j
  simpa only [lineSpeed_eq_metricSeminorm hf hx] using hd j

end SharpIntegralFillings.MetricDifferentiation

open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings
open Metric

lemma uniformly_tendsto_of_lipschitz {A : Type*} [PseudoMetricSpace A]
    {ι : Type*} {l : Filter ι} {f : ι → A → ℝ} {g : A → ℝ}
    {K : ℝ≥0} (hf : ∀ j, LipschitzWith K (f j)) (hg : LipschitzWith K g)
    {s : Set A} (hs : IsCompact s)
    (hlim : ∀ x ∈ s, Tendsto (fun j => f j x) l (𝓝 (g x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in l, ∀ x ∈ s, dist (f j x) (g x) < ε := by
  let δ : ℝ := ε / (4 * ((K : ℝ) + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨t, hts, ht, hcov⟩ := hs.finite_cover_balls hδ
  have hev : ∀ᶠ j in l, ∀ y ∈ t, dist (f j y) (g y) < ε/2 := by
    rw [ht.eventually_all]
    exact fun y hy => (Metric.tendsto_nhds.mp (hlim y (hts hy))) (ε/2) (half_pos hε)
  filter_upwards [hev] with j hj x hx
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ t, dist x y < δ := by
    rcases mem_iUnion.mp (hcov hx) with ⟨y, hy⟩
    rcases mem_iUnion.mp hy with ⟨hyt, hball⟩
    exact ⟨y, hyt, hball⟩
  have hdr : (K : ℝ) * dist x y < ε/4 := by
    have hm := mul_lt_mul_of_pos_left hxy (show 0 < (K : ℝ)+1 by positivity)
    have heq : ((K : ℝ)+1)*δ = ε/4 := by dsimp [δ]; field_simp
    rw [heq] at hm
    exact lt_of_le_of_lt (by nlinarith [dist_nonneg (x := x) (y := y)]) hm
  calc dist (f j x) (g x) ≤
      dist (f j x) (f j y) + dist (f j y) (g y) + dist (g y) (g x) :=
        (dist_triangle _ (g y) _).trans (add_le_add (dist_triangle _ (f j y) _) le_rfl)
    _ < ε/4 + ε/2 + ε/4 := by
      apply add_lt_add
      · exact add_lt_add (((hf j).dist_le_mul x y).trans_lt hdr) (hj y hy)
      · rw [dist_comm]
        exact (hg.dist_le_mul x y).trans_lt hdr
    _ = ε := by ring
end SharpIntegralFillings

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Centered
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {X : Type*} [MetricSpace X] {f : E → X} {K : ℝ≥0}

lemma metricQuotient_lipschitz (hf : LipschitzWith K f) (x : E) (t : ℝ) :
    LipschitzWith K (metricQuotient f x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  by_cases ht : t = 0
  · simp only [metricQuotient, ht, abs_zero, div_zero, dist_self]
    positivity
  have ht' : 0 < |t| := abs_pos.mpr ht
  simp only [metricQuotient, Real.dist_eq, ← sub_div, abs_div, abs_abs]
  calc |dist (f (x+t • v)) (f x) - dist (f (x+t • w)) (f x)|/|t| ≤
        dist (f (x+t • v)) (f (x+t • w)) / |t| :=
      div_le_div_of_nonneg_right (abs_dist_sub_le _ _ _) ht'.le
    _ ≤ ((K : ℝ) * dist (x+t • v) (x+t • w)) / |t| :=
      div_le_div_of_nonneg_right (hf.dist_le_mul _ _) ht'.le
    _ = (K : ℝ) * dist v w := by
      rw [dist_add_left, dist_eq_norm, ← smul_sub, norm_smul,
        Real.norm_eq_abs, dist_eq_norm]
      field_simp

lemma hasCenteredMetricDifferential_of_dense_directions [FiniteDimensional ℝ E]
    (hf : LipschitzWith K f) (x : E) (p : Seminorm ℝ E)
    (hp : LipschitzWith K p) {ι : Type*} {D : ι → E} (hD : DenseRange D)
    (hdir : ∀ j, Tendsto (fun t => metricQuotient f x t (D j)) (𝓝[≠] 0) (𝓝 (p (D j)))) :
    HasCenteredMetricDifferential f p x := by
  have hall (v : E) : Tendsto (fun t => metricQuotient f x t v) (𝓝[≠] 0) (𝓝 (p v)) :=
    tendsto_of_lipschitz_dense (metricQuotient_lipschitz hf x) hp hD hdir v
  apply IsLittleO.of_bound
  intro ε hε
  have hU := uniformly_tendsto_of_lipschitz (metricQuotient_lipschitz hf x) hp
    (isCompact_sphere (0 : E) 1) (fun v _ => hall v) hε
  obtain ⟨δ, hδ, hUδ⟩ := Metric.mem_nhdsWithin_iff.mp hU
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  by_cases hyx : y = x
  · simp [hyx]
  let r : ℝ := ‖y-x‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  let v : E := r⁻¹ • (y-x)
  have hv : v ∈ sphere (0 : E) 1 := by
    rw [mem_sphere, dist_zero_right]
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_cancel₀ hr.ne']
  have hrv : r • v = y-x := by dsimp [v]; exact smul_inv_smul₀ hr.ne' _
  have hry : x+r • v = y := by rw [hrv]; abel
  have hrδ : r ∈ ball (0 : ℝ) δ ∩ ({0} : Set ℝ)ᶜ := by
    constructor
    · change |r-0| < δ
      rw [sub_zero, abs_of_pos hr]
      simpa only [mem_ball, dist_eq_norm, r] using hy
    · exact hr.ne'
  have hh := hUδ hrδ v hv
  change dist (dist (f (x+r • v)) (f x)/|r|) (p v) < ε at hh
  rw [hry, abs_of_pos hr, Real.dist_eq] at hh
  have hpv : p (y-x) = r * p v := by
    rw [← hrv, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hr]
  rw [hpv, Real.norm_eq_abs]
  change |dist (f y) (f x)-r*p v| ≤ ε*r
  have heq : dist (f y) (f x)-r*p v = r*(dist (f y) (f x)/r-p v) := by field_simp
  rw [heq, abs_mul, abs_of_pos hr]
  exact (mul_lt_mul_of_pos_left hh hr).le.trans_eq (mul_comm r ε)

variable [SeparableSpace X] [Nonempty X] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

theorem ae_hasCenteredMetricDifferential (μ : Measure E) [μ.IsAddHaarMeasure]
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, HasCenteredMetricDifferential f (metricSeminorm f x) x := by
  filter_upwards [ae_dense_directionalSeminorm μ hf] with x hx
  exact hasCenteredMetricDifferential_of_dense_directions hf x _ (metricSeminorm_lipschitz hf x)
    (denseRange_denseSeq E) hx

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_ErrorModulus
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
omit [FiniteDimensional ℝ E] in
lemma measurable_metricSeminorm_apply (hf : LipschitzWith K f) (v : E) :
    Measurable (fun x => metricSeminorm f x v) := by
  simp only [metricSeminorm_apply hf]
  exact Measurable.iSup (fun q => (measurable_fderiv_apply_const ℝ (scalarCoordinate f q) v).abs)

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorTerm_nonneg (r : ℝ) (q : ℕ) (x : E) :
    0 ≤ metricErrorTerm f r q x := by
  dsimp [metricErrorTerm]
  split_ifs
  · positivity
  · rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorTerm_le (hf : LipschitzWith K f) (r : ℝ) (q : ℕ) (x : E) :
    metricErrorTerm f r q x ≤ 2*(K : ℝ) := by
  dsimp [metricErrorTerm]
  split_ifs with h
  · apply (div_le_iff₀ h.1).mpr
    have hd : dist (f (x+denseSeq E q)) (f x) ≤ (K : ℝ)*‖denseSeq E q‖ := by
      simpa only [dist_eq_norm, add_sub_cancel_left] using hf.dist_le_mul (x+denseSeq E q) x
    have hp := metricSeminorm_le hf x (denseSeq E q)
    have hp0 := apply_nonneg (metricSeminorm f x) (denseSeq E q)
    have hd0 := dist_nonneg (x := f (x+denseSeq E q)) (y := f x)
    rw [abs_le]
    constructor <;> nlinarith
  · positivity

omit [MeasurableSpace E] [BorelSpace E] in
lemma bddAbove_metricErrorTerm (hf : LipschitzWith K f) (r : ℝ) (x : E) :
    BddAbove (range (fun q => metricErrorTerm f r q x)) :=
  ⟨2*(K : ℝ), by rintro _ ⟨q,rfl⟩; exact metricErrorTerm_le hf r q x⟩

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_nonneg (hf : LipschitzWith K f) (r : ℝ) (x : E) :
    0 ≤ metricErrorModulus f r x :=
  (metricErrorTerm_nonneg r 0 x).trans (le_ciSup (bddAbove_metricErrorTerm hf r x) 0)

lemma measurable_metricErrorModulus (hf : LipschitzWith K f) (r : ℝ) :
    Measurable (metricErrorModulus f r) := by
  change Measurable (fun x => ⨆ q : ℕ, metricErrorTerm f r q x)
  apply Measurable.iSup
  intro q
  change Measurable (fun x => metricErrorTerm f r q x)
  unfold metricErrorTerm
  split_ifs
  · exact (((hf.continuous.comp (continuous_id.add continuous_const)).dist hf.continuous).measurable.sub
      (measurable_metricSeminorm_apply hf _)).abs.div_const _
  · exact measurable_const

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_le_of_bound (_hf : LipschitzWith K f) {r ε : ℝ} {x : E}
    (hε : 0 ≤ ε)
    (H : ∀ v : E, ‖v‖ ≤ r → |dist (f (x+v)) (f x)-metricSeminorm f x v| ≤ ε*‖v‖) :
    metricErrorModulus f r x ≤ ε := by
  apply ciSup_le
  intro q
  dsimp [metricErrorTerm]
  split_ifs with h
  · exact (div_le_iff₀ h.1).mpr (H _ h.2)
  · exact hε

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_tendsto_zero (hf : LipschitzWith K f) {x : E}
    (hx : HasCenteredMetricDifferential f (metricSeminorm f x) x)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le (metricErrorModulus_nonneg hf _ _))
  · intro ε hε
    have hxε := hx.bound (half_pos hε)
    obtain ⟨δ,hδ,hδx⟩ := Metric.mem_nhds_iff.mp hxε
    have hδr := (tendsto_order.1 hr).2 δ hδ
    filter_upwards [hδr] with n hn
    apply lt_of_le_of_lt (metricErrorModulus_le_of_bound hf (half_pos hε).le ?_)
      (half_lt_self hε)
    intro v hv
    have hvδ : x+v ∈ ball x δ := by
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hv.trans_lt hn
    simpa only [mem_ofPred_eq, add_sub_cancel_left, Real.norm_eq_abs] using hδx hvδ

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

omit [MeasurableSpace E] [BorelSpace E] in
lemma metricErrorModulus_bound (hf : LipschitzWith K f) {r : ℝ} (x v : E)
    (hv : ‖v‖ < r) :
    |dist (f (x+v)) (f x)-metricSeminorm f x v| ≤ metricErrorModulus f r x * ‖v‖ := by
  let A : Set E := {w | |dist (f (x+w)) (f x)-metricSeminorm f x w| ≤
    metricErrorModulus f r x * ‖w‖}
  have hA : IsClosed A := isClosed_le
    (((hf.continuous.comp (continuous_const.add continuous_id)).dist continuous_const).sub
      (metricSeminorm_lipschitz hf x).continuous).abs
    (continuous_const.mul continuous_norm)
  have hsub : ball (0 : E) r ∩ range (denseSeq E) ⊆ A := by
    rintro w ⟨hq,⟨q,rfl⟩⟩
    by_cases hw : denseSeq E q = 0
    · simp [A,hw]
    have hqw : 0 < ‖denseSeq E q‖ := norm_pos_iff.mpr hw
    have hqr : ‖denseSeq E q‖ ≤ r := (by simpa only [mem_ball, dist_zero_right] using hq :
      ‖denseSeq E q‖ < r).le
    have hle := le_ciSup (bddAbove_metricErrorTerm hf r x) q
    rw [metricErrorTerm, ite_eq_left ⟨hqw,hqr⟩] at hle
    exact (div_le_iff₀ hqw).mp hle
  have hvcl := (denseRange_denseSeq E).open_subset_closure_inter isOpen_ball
    (by simpa only [mem_ball, dist_zero_right] using hv : v ∈ ball (0 : E) r)
  exact hA.closure_subset_iff.mpr hsub hvcl

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_TwoPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory TopologicalSpace
open Filter Set
open scoped Topology NNReal

namespace SharpIntegralFillings
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma seminorm_sub_bound_of_sphere {p q : Seminorm ℝ E} {ε : ℝ} (_hε : 0 ≤ ε)
    (H : ∀ v : E, ‖v‖ = 1 → |p v-q v| ≤ ε) (v : E) :
    |p v-q v| ≤ ε*‖v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,hv0.ne']
  have he : ‖v‖ • u = v := by simp [u,hv0.ne']
  have hpv : p v = ‖v‖ * p u := by
    calc p v = p (‖v‖ • u) := congrArg p he.symm
      _ = ‖v‖ * p u := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg v)]
  have hqv : q v = ‖v‖ * q u := by
    calc q v = q (‖v‖ • u) := congrArg q he.symm
      _ = ‖v‖ * q u := by rw [map_smul_eq_mul, Real.norm_of_nonneg (norm_nonneg v)]
  calc |p v-q v| = ‖v‖ * |p u-q u| := by
        rw [hpv,hqv,←mul_sub,abs_mul,abs_of_pos hv0]
    _ ≤ ‖v‖*ε := mul_le_mul_of_nonneg_left (H u hu) hv0.le
    _ = ε*‖v‖ := mul_comm _ _

variable [FiniteDimensional ℝ E]
lemma eventually_seminorm_bound_of_dense
    {ι κ : Type*} {l : Filter ι} {p : ι → Seminorm ℝ E} {q : Seminorm ℝ E}
    {K : ℝ≥0} (hp : ∀ i, LipschitzWith K (p i)) (hq : LipschitzWith K q)
    {D : κ → E} (hD : DenseRange D)
    (hc : ∀ j, Tendsto (fun i => p i (D j)) l (𝓝 (q (D j))))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ v : E, |p i v-q v| ≤ ε*‖v‖ := by
  have hlim := tendsto_of_lipschitz_dense hp hq hD hc
  have h := uniformly_tendsto_of_lipschitz hp hq (isCompact_sphere (0 : E) 1)
    (fun v _ => hlim v) hε
  filter_upwards [h] with i hi v
  apply seminorm_sub_bound_of_sphere hε.le _ v
  intro w hw
  exact (hi w (by simpa only [mem_sphere,dist_zero_right] using hw)).le

end SharpIntegralFillings

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_LargePieces
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SharpIntegralFillings
lemma exists_closed_large_continuousOn
    {A B : Type*} [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [SecondCountableTopology B] [MeasurableSpace B]
    [OpensMeasurableSpace B] (μ : Measure A) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    {f : A → B} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set A, IsClosed K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  classical
  let I := countableBasis B
  obtain ⟨δ,hδ,hδsum⟩ := ENNReal.exists_pos_sum_of_countable' hε I
  have H (i : I) : ∃ U F : Set A,
      f ⁻¹' (i : Set B) ⊆ U ∧ F ⊆ f ⁻¹' (i : Set B) ∧
      IsOpen U ∧ IsClosed F ∧ μ (U \ F) < δ i := by
    let S := f ⁻¹' (i : Set B)
    have hS : MeasurableSet S := hf (isOpen_of_mem_countableBasis i.property).measurableSet
    have hδi : δ i / 2 ≠ 0 := (ENNReal.half_pos (hδ i).ne').ne'
    obtain ⟨U,hSU,hU,_,hμU⟩ := hS.exists_isOpen_sdiff_lt (measure_ne_top μ S) hδi
    obtain ⟨F,hFS,hF,hμF⟩ := hS.exists_isClosed_sdiff_lt (measure_ne_top μ S) hδi
    refine ⟨U,F,hSU,hFS,hU,hF,?_⟩
    calc μ (U \ F) ≤ μ ((U \ S) ∪ (S \ F)) := by
          apply measure_mono
          intro x hx
          by_cases hxs : x ∈ S
          · exact Or.inr ⟨hxs,hx.2⟩
          · exact Or.inl ⟨hx.1,hxs⟩
      _ ≤ μ (U \ S) + μ (S \ F) := measure_union_le _ _
      _ < δ i / 2 + δ i / 2 := ENNReal.add_lt_add hμU hμF
      _ = δ i := ENNReal.add_halves _
  choose U F hSU hFS hU hF hμ using H
  let K : Set A := (⋃ i : I, U i \ F i)ᶜ
  refine ⟨K, (isOpen_iUnion (fun i => (hU i).sdiff (hF i))).isClosed_compl, ?_, ?_⟩
  · calc μ Kᶜ = μ (⋃ i : I, U i \ F i) := by simp [K]
      _ ≤ ∑' i : I, μ (U i \ F i) := measure_iUnion_le _
      _ ≤ ∑' i : I, δ i := ENNReal.tsum_le_tsum (fun i => (hμ i).le)
      _ < ε := hδsum
  · apply (isBasis_countableBasis B).continuousOn_iff.mpr
    intro V hV
    let i : I := ⟨V,hV⟩
    refine ⟨U i,hU i,?_⟩
    ext x
    constructor
    · rintro ⟨hx,hxK⟩
      exact ⟨hSU i hx,hxK⟩
    · rintro ⟨hxU,hxK⟩
      have hxF : x ∈ F i := by
        by_contra h
        exact hxK (mem_iUnion.mpr ⟨i,hxU,h⟩)
      exact ⟨hFS i hxF,hxK⟩

end SharpIntegralFillings

namespace SharpIntegralFillings
open Metric

lemma exists_large_continuousOn_uniformly
    {A B : Type*} [TopologicalSpace A] [PseudoMetrizableSpace A]
    [MeasurableSpace A] [BorelSpace A]
    [TopologicalSpace B] [SecondCountableTopology B] [MeasurableSpace B]
    [OpensMeasurableSpace B] (μ : Measure A)
    {s : Set A} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {f : A → B} (hf : Measurable f) {u : ℕ → A → ℝ}
    (hu : ∀ n, Measurable (u n))
    (hc : ∀ᵐ x ∂μ.restrict s, Tendsto (fun n => u n x) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t ⊆ s, MeasurableSet t ∧ μ (s \ t) ≤ ENNReal.ofReal ε ∧
      ContinuousOn f t ∧ TendstoUniformlyOn u (fun _ => 0) atTop t := by
  let ν := μ.restrict s
  have : IsFiniteMeasure ν := ⟨by simpa [ν] using hsf.lt_top⟩
  obtain ⟨K,hK,hμK,hcf⟩ := exists_closed_large_continuousOn ν hf
    (show ENNReal.ofReal (ε/2) ≠ 0 from (ENNReal.ofReal_pos.mpr (half_pos hε)).ne')
  obtain ⟨e,he,hμe,hue⟩ := tendstoUniformlyOn_of_ae_tendsto'
    (fun n => (hu n).stronglyMeasurable) stronglyMeasurable_const hc
    (half_pos hε)
  let t := s ∩ (K \ e)
  refine ⟨t,inter_subset_left,hs.inter (hK.measurableSet.diff he),?_,
    hcf.mono (fun _ h => h.2.1),hue.mono (fun _ h => h.2.2)⟩
  calc μ (s \ t) = ν (Kᶜ ∪ e) := by
        rw [Measure.restrict_apply (hK.measurableSet.compl.union he)]
        congr 1
        ext x
        simp only [t,Set.mem_sdiff,mem_inter_iff,mem_union,mem_compl_iff]
        tauto
    _ ≤ ν Kᶜ + ν e := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε/2) + ENNReal.ofReal (ε/2) := add_le_add hμK.le hμe
    _ = ENNReal.ofReal ε := by rw [←ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]; congr 1; ring
end SharpIntegralFillings

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Partitions
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
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

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}
lemma exists_radius_uniform_metric_error
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ s ∩ ball x δ, ∀ z ∈ s ∩ ball x δ,
      |dist (f y) (f z)-metricSeminorm f x (y-z)| ≤ ε*‖y-z‖ := by
  have hp := eventually_seminorm_bound_of_dense (fun y => metricSeminorm_lipschitz hf y)
    (metricSeminorm_lipschitz hf x) (denseRange_denseSeq E) hc (half_pos hε)
  obtain ⟨a,ha,hap⟩ := Metric.mem_nhdsWithin_iff.1 hp
  obtain ⟨N,hN⟩ := (eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hu (ε/2) (half_pos hε)))
  have hNN := hN N le_rfl
  refine ⟨min a (r N/3), lt_min ha (div_pos (hr N) (by norm_num)), ?_⟩
  intro y hy z hz
  have hyp : ∀ v : E, |metricSeminorm f y v-metricSeminorm f x v| ≤ ε/2*‖v‖ :=
    hap ⟨show dist y x < a from lt_of_lt_of_le hy.2 (min_le_left _ _),hy.1⟩
  have hyz : ‖z-y‖ < r N := by
    have h₁ : ‖y-x‖ < r N/3 := by
      exact lt_of_lt_of_le (by simpa only [mem_ball,dist_eq_norm] using hy.2) (min_le_right _ _)
    have h₂ : ‖z-x‖ < r N/3 := by
      exact lt_of_lt_of_le (by simpa only [mem_ball,dist_eq_norm] using hz.2) (min_le_right _ _)
    have h₃ : ‖z-y‖ ≤ ‖z-x‖+‖y-x‖ := by
      calc ‖z-y‖ = ‖(z-x)-(y-x)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    linarith [hr N]
  have he₁ := metricErrorModulus_bound hf y (z-y) hyz
  have he₂ := hyp (z-y)
  have hm : metricErrorModulus f (r N) y < ε/2 := by
    have hm := hNN y hy.1
    simpa only [dist_zero_left,Real.norm_eq_abs,
      abs_of_nonneg (metricErrorModulus_nonneg hf _ _)] using hm
  have hpneg : metricSeminorm f x (y-z) = metricSeminorm f x (z-y) := by
    rw [←neg_sub z y,map_neg_eq_map]
  rw [hpneg,dist_comm,norm_sub_rev]
  calc |dist (f z) (f y)-metricSeminorm f x (z-y)| ≤
        |dist (f z) (f y)-metricSeminorm f y (z-y)| +
          |metricSeminorm f y (z-y)-metricSeminorm f x (z-y)| := abs_sub_le _ _ _
    _ ≤ metricErrorModulus f (r N) y*‖z-y‖+ε/2*‖z-y‖ := by
      apply add_le_add _ he₂
      simpa only [←add_sub_assoc,add_sub_cancel_left] using he₁
    _ ≤ ε*‖z-y‖ := by nlinarith [norm_nonneg (z-y)]

lemma exists_radius_nearIsometric
    (hf : LipschitzWith K f) {s : Set E} {x : E}
    (hc : ∀ j : ℕ, ContinuousWithinAt (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ s ∩ ball x δ, ∀ z ∈ s ∩ ball x δ,
      (1-ε)*metricSeminorm f x (y-z) ≤ dist (f y) (f z) ∧
      dist (f y) (f z) ≤ (1+ε)*metricSeminorm f x (y-z) := by
  obtain ⟨δ,hδ,H⟩ := exists_radius_uniform_metric_error hf hc hr hu (div_pos hε hA)
  refine ⟨δ,hδ,?_⟩
  intro y hy z hz
  have he : |dist (f y) (f z)-metricSeminorm f x (y-z)| ≤
      ε*metricSeminorm f x (y-z) := by
    apply (H y hy z hz).trans
    calc (ε/A)*‖y-z‖ ≤ (ε/A)*(A*metricSeminorm f x (y-z)) :=
          mul_le_mul_of_nonneg_left (hbound _) (div_pos hε hA).le
      _ = ε*metricSeminorm f x (y-z) := by field_simp
  obtain ⟨hl,hr⟩ := abs_le.1 he
  constructor <;> linarith

lemma exists_nearIsometric_partition
    [MeasurableSpace E] [BorelSpace E] {s : Set E} [Nonempty s]
    (hs : MeasurableSet s) (hf : LipschitzWith K f)
    (hc : ∀ x ∈ s, ∀ j : ℕ, ContinuousWithinAt
      (fun y => metricSeminorm f y (denseSeq E j)) s x)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n)
    (hu : TendstoUniformlyOn (fun n => metricErrorModulus f (r n)) (fun _ => 0) atTop s)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ x ∈ s, ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → s) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      (⋃ i, t i) = s ∧ ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
  choose δ hδ hlocal using fun x : s =>
    exists_radius_nearIsometric hf (hc x x.property) hr hu hA (hbound x x.property) hε
  obtain ⟨c,hcvr⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
    (fun x : s => ball (x : E) (δ x)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.2 ⟨⟨x,hx⟩,mem_ball_self (hδ ⟨x,hx⟩)⟩)
  let t : ℕ → Set E := fun i => s ∩ ball (c i : E) (δ (c i))
  refine ⟨c,disjointed t, fun i => MeasurableSet.disjointed
    (fun j => hs.inter isOpen_ball.measurableSet) i,disjoint_disjointed t,?_,?_⟩
  · rw [iUnion_disjointed]
    apply Subset.antisymm
    · exact iUnion_subset (fun i => inter_subset_left)
    · intro x hx
      obtain ⟨i,hi⟩ := mem_iUnion.1 (hcvr hx)
      exact mem_iUnion.2 ⟨i,hx,hi⟩
  · intro i y hy z hz
    exact hlocal (c i) y (disjointed_le t i hy) z (disjointed_le t i hz)

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem exists_ae_nearIsometric_partition
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ ∞)
    {A : ℝ} (hA : 0 < A) (hbound : ∀ x ∈ s, ∀ v, ‖v‖ ≤ A*metricSeminorm f x v)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℕ → E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      (∀ i, (t i).Nonempty → c i ∈ s) ∧
      ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
  classical
  let r : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hr : ∀ n, 0 < r n := fun n => by dsimp [r] <;> positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : ∀ᵐ x ∂μ.restrict s,
      Tendsto (fun n => metricErrorModulus f (r n) x) atTop (𝓝 0) := by
    filter_upwards [(ae_hasCenteredMetricDifferential μ hf).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := μ) (s := s)))] with x hx
    exact metricErrorModulus_tendsto_zero hf hx hr0
  have H (j : ℕ) := exists_large_continuousOn_uniformly μ hs hsf
    (show Measurable (fun x i => metricSeminorm f x (denseSeq E i)) from
      Measurable.of_eval (fun index => measurable_metricSeminorm_apply hf (denseSeq E index)))
    (fun i => measurable_metricErrorModulus hf (r i)) hc (hr j)
  choose u hus hum hμu hcu huu using H
  have HP (j : ℕ) : ∃ (c : ℕ → E) (t : ℕ → Set E),
      (∀ i, MeasurableSet (t i)) ∧ (⋃ i, t i) = u j ∧
      (∀ i, (t i).Nonempty → c i ∈ s) ∧
      ∀ i, ∀ y ∈ t i, ∀ z ∈ t i,
        (1-ε)*metricSeminorm f (c i) (y-z) ≤ dist (f y) (f z) ∧
        dist (f y) (f z) ≤ (1+ε)*metricSeminorm f (c i) (y-z) := by
    by_cases hne : (u j).Nonempty
    · let _ : Nonempty (u j) := hne.to_subtype
      obtain ⟨c,t,ht,_,htu,hineq⟩ := exists_nearIsometric_partition (hum j) hf
        (fun x hx i => (continuousOn_pi.1 (hcu j) i) x hx) hr (huu j) hA
        (fun x hx => hbound x (hus j hx)) hε
      exact ⟨fun i => c i,t,ht,htu,fun i _ => hus j (c i).property,hineq⟩
    · refine ⟨fun _ => 0,fun _ => ∅,fun _ => MeasurableSet.empty,?_,?_,?_⟩
      · simp [not_nonempty_iff_eq_empty.mp hne]
      · simp
      · simp
  choose c t htm htunion hcs htineq using HP
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let T : ℕ → Set E := fun i => t (e i).1 (e i).2
  have hTunion : (⋃ i, T i) = ⋃ j, u j := by
    ext x
    simp only [T,mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨(e i).1,htunion (e i).1 ▸ mem_iUnion.2 ⟨(e i).2,hi⟩⟩
    · rintro ⟨j,hj⟩
      obtain ⟨i,hi⟩ := mem_iUnion.1 ((htunion j).symm ▸ hj)
      refine ⟨e.symm (j,i),?_⟩
      simpa using hi
  have hu0 : μ (s \ ⋃ j, u j) = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto (by simpa using ENNReal.tendsto_ofReal hr0)
    filter_upwards [] with j
    exact (measure_mono (sdiff_subset_sdiff_right (subset_iUnion u j))).trans (hμu j)
  refine ⟨fun i => c (e i).1 (e i).2,disjointed T,
    fun i => MeasurableSet.disjointed (fun k => htm (e k).1 (e k).2) i,
    ?_,disjoint_disjointed T,?_,?_,?_⟩
  · intro i x hx
    apply hus (e i).1
    rw [←htunion (e i).1]
    exact mem_iUnion.2 ⟨(e i).2,disjointed_le T i hx⟩
  · rw [iUnion_disjointed,hTunion]
    exact hu0
  · intro i hi
    exact hcs _ _ (hi.mono (disjointed_le T i))
  · intro i y hy z hz
    exact htineq _ _ y (disjointed_le T i hy) z (disjointed_le T i hz)

end SharpIntegralFillings.MetricDifferentiation
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_FullRank
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
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

theorem exists_ae_bilipschitz_partition_of_bound_oai
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ (⊤ : ℝ≥0∞))
    {A : ℝ≥0} (hA : 0 < A)
    (hbound : ∀ x ∈ s, ∀ v : E, ‖v‖ ≤ (A : ℝ)*metricSeminorm f x v) :
    ∃ t : ℕ → Set E,
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      ∀ i, LipschitzWith K (fun x : t i => f x) ∧
        AntilipschitzWith (2*A) (fun x : t i => f x) := by
  obtain ⟨c,t,htm,hts,hdisj,ht0,hcs,hineq⟩ :=
    exists_ae_nearIsometric_partition μ hf hs hsf
      (show 0 < (A : ℝ) from hA) hbound (show (0 : ℝ) < 1/2 by norm_num)
  refine ⟨t,htm,hts,hdisj,ht0,fun i => ⟨LipschitzWith.of_dist_le_mul (fun a b => hf.dist_le_mul a b),?_⟩⟩
  apply AntilipschitzWith.of_le_mul_dist
  intro a b
  have hlo := (hineq i a a.property b b.property).1
  have hb := hbound (c i) (hcs i ⟨a,a.property⟩) ((a : E)-(b : E))
  change dist (a : E) (b : E) ≤ (↑(2*A) : ℝ)*dist (f a) (f b)
  rw [dist_eq_norm]
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ (A : ℝ) from A.coe_nonneg)
    (show 0 ≤ dist (f a) (f b) - (1-(1:ℝ)/2)*metricSeminorm f (c i) ((a : E)-(b : E)) from sub_nonneg.mpr hlo)]

end SharpIntegralFillings.MetricDifferentiation

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SharpIntegralFillings.MetricDifferentiation.exists_ae_bilipschitz_partition_of_bound_oai.{u_1, u_2} := @OAI.SharpIntegralFillings.MetricDifferentiation.exists_ae_bilipschitz_partition_of_bound_oai.{u_1, u_2}
