-- Prove2me | solution 1 for OAI.SharpIntegralFillings.EuclideanStraightening.exists_straightened_pieces
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:36:11.39956+00:00
-- url     : https://prove2.me/submissions/5c169fe6-cc71-46ef-8bc3-0f7277a0d4c5

import Mathlib
import Definitions.Def_FillingCoefficient
import Definitions.Def_OAIQ219IF000
import Theorems.Thm_OAI_SharpIntegralFillings_MetricDifferentiation_exists_ae_bilipschitz_partition_of_bound

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_Straightening
attribute [-instance] _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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

namespace SharpIntegralFillings
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace EuclideanStraightening
variable {d : ℕ}

lemma replaceMap_lipschitz (j : Fin d) {g : Euc d → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊) (replaceMap j g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h1 := hg.dist_le_mul x y
  have h2 := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).lipschitz.dist_le_mul x y
  have h3 : ‖(g x-x j)-(g y-y j)‖ ≤ ((K:ℝ)+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊)*‖x-y‖ := by
    have htriangle : ‖(g x-x j)-(g y-y j)‖ ≤ ‖g x-g y‖+‖x j-y j‖ := by
      convert norm_sub_le (g x-g y) (x j-y j) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    simp only [dist_eq_norm] at h1 h2
    change ‖x j-y j‖ ≤ _ at h2
    nlinarith
  simp only [replaceMap,dist_eq_norm]
  have he : x+(g x-x j) • EuclideanSpace.single j 1-
      (y+(g y-y j) • EuclideanSpace.single j 1) =
      (x-y)+((g x-x j)-(g y-y j)) • EuclideanSpace.single j 1 := by
    module
  rw [he]
  calc
    _ ≤ ‖x-y‖ + ‖((g x-x j)-(g y-y j)) • EuclideanSpace.single j 1‖ := norm_add_le _ _
    _ = ‖x-y‖+‖(g x-x j)-(g y-y j)‖ := by simp [norm_smul]
    _ ≤ ‖x-y‖+(((K:ℝ)+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊)*‖x-y‖) := add_le_add_right h3 ‖x-y‖
    _ = _ := by simp only [NNReal.coe_add,NNReal.coe_one] <;> ring

lemma det_updateRow_one (j : Fin d) (v : Fin d → ℝ) :
    (Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j v).det = v j := by
  have he : (∑ i : Fin d, v i • (1 : Matrix (Fin d) (Fin d) ℝ) i) = v := by
    ext l
    simp [Matrix.one_apply]
  rw [←he,Matrix.det_updateRow_sum]
  simp [Matrix.one_apply]

lemma replaceMap_hasFDerivAt {g : Euc d → ℝ} {x : Euc d} (hg : DifferentiableAt ℝ g x)
    (j : Fin d) : HasFDerivAt (replaceMap j g)
      (ContinuousLinearMap.id ℝ (Euc d)+(fderiv ℝ g x-EuclideanSpace.proj j).smulRight
        (EuclideanSpace.single j 1)) x :=
  (hasFDerivAt_id x).add ((hg.hasFDerivAt.sub (EuclideanSpace.proj j).hasFDerivAt).smul_const _)

lemma det_replaceMap_fderiv {g : Euc d → ℝ} {x : Euc d} (hg : DifferentiableAt ℝ g x)
    (j : Fin d) :
    (Matrix.of fun i l : Fin d => fderiv ℝ (replaceMap j g) x (EuclideanSpace.single l 1) i).det =
      fderiv ℝ g x (EuclideanSpace.single j 1) := by
  rw [(replaceMap_hasFDerivAt hg j).fderiv]
  have he : (Matrix.of fun i l : Fin d =>
      (ContinuousLinearMap.id ℝ (Euc d)+(fderiv ℝ g x-EuclideanSpace.proj j).smulRight
        (EuclideanSpace.single j 1)) (EuclideanSpace.single l 1) i) =
      Matrix.updateRow (1 : Matrix (Fin d) (Fin d) ℝ) j
        (fun l => fderiv ℝ g x (EuclideanSpace.single l 1)) := by
    ext i l
    by_cases hi : i=j
    · subst i
      simp [ContinuousLinearMap.smulRight_apply,PiLp.single_apply,
        Matrix.updateRow,Function.update]
    · simp [ContinuousLinearMap.smulRight_apply,PiLp.single_apply,
        Matrix.updateRow,Function.update,Matrix.one_apply,hi]
  rw [he,det_updateRow_one]

lemma straightenMap_lipschitz {k : ℕ} (j : Fin (k+1)) {g : Euc (k+1) → ℝ}
    {K : ℝ≥0} (hg : LipschitzWith K g) :
    LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc (k+1) →L[ℝ] ℝ)‖₊) (straightenMap j g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (switchZero j (replaceMap j g x)) (switchZero j (replaceMap j g y)) ≤ _
  rw [(switchZero j).isometry.dist_eq]
  exact (replaceMap_lipschitz j hg).dist_le_mul x y

end EuclideanStraightening
end SharpIntegralFillings

end

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

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Density
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

namespace SharpIntegralFillings
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

omit [MeasurableSpace E] [BorelSpace E] in

lemma seminorm_continuous_finiteDimensional (p : Seminorm ℝ E) : Continuous p := by
  classical
  let b := Module.finBasis ℝ E
  have hsum (I : Finset (Fin (Module.finrank ℝ E)))
      (q : Fin (Module.finrank ℝ E) → E) :
      p (∑ i ∈ I, q i) ≤ ∑ i ∈ I, p (q i) := by
    induction I using Finset.induction_on with
    | empty => simp
    | @insert i I hi ih =>
      simp only [Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)
  have hb (v : E) : p v ≤ ∑ i, ‖b.repr v i‖ * p (b i) := by
    convert hsum Finset.univ (fun i => b.repr v i • b i) using 1
    · rw [b.sum_repr]
    · simp only [map_smul_eq_mul]
  have hcont : Continuous (fun v => ∑ i, ‖b.repr v i‖ * p (b i)) := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp b.continuous_coe_repr).norm.mul_const _
  apply Seminorm.continuous_of_continuousAt_zero
  have hc : Tendsto (fun v => ∑ i, ‖b.repr v i‖ * p (b i)) (𝓝 0) (𝓝 0) := by
    simpa using hcont.tendsto 0
  simpa [ContinuousAt] using tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hc (fun v => apply_nonneg p v) hb

end SharpIntegralFillings
end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_ScalarBound
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

namespace SharpIntegralFillings
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
lemma scalar_derivative_bound_of_metric_differential
    {s : Set E} {x : E} {F r : E → ℝ} {p : Seminorm ℝ E} {ℓ : E →L[ℝ] ℝ}
    (hx : Tendsto (fun t => μ (s ∩ closedBall x t) / μ (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (hF : HasFDerivWithinAt F ℓ s x)
    (hr : (fun y => r y-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    {K : ℝ} (hbound : ∀ y ∈ s, |F y-F x| ≤ K*r y) (v : E) :
    |ℓ v| ≤ K*p v := by
  have hv : v ∈ tangentConeAt ℝ s x := by
    rw [tangentConeAt_eq_univ_of_density_one μ s x hx]
    exact mem_univ v
  obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hv
  have hd₀ := tangentConeAt.lim_zero atTop hc hcd
  have ht : Tendsto (fun j => x+d j) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd₀,hd⟩
  have hl : Tendsto (fun j => ‖c j‖ * |F (x+d j)-F x|) atTop (𝓝 |ℓ v|) := by
    simpa only [Real.norm_eq_abs,smul_eq_mul,abs_mul] using (hF.lim hd₀ hd hcd).norm
  have hsmall := (hr.comp_tendsto ht).norm_right.mul_isBigO
    (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => ‖(x+d j)-x‖*‖c j‖) atTop (𝓝 ‖v‖) := by
    simpa only [norm_smul,add_sub_cancel_left,mul_comm] using hcd.norm
  have hzero := hsmall.tendsto_zero_of_tendsto hnorm
  have hp := (seminorm_continuous_finiteDimensional p).tendsto v |>.comp hcd
  have hlim : Tendsto (fun j => ‖c j‖*r (x+d j)) atTop (𝓝 (p v)) := by
    convert hzero.add hp using 1
    · ext j
      simp only [Function.comp_apply,add_sub_cancel_left,map_smul_eq_mul]
      ring
    · simp
  apply le_of_tendsto_of_tendsto hl (hlim.const_mul K)
  filter_upwards [hd] with j hj
  have hh := mul_le_mul_of_nonneg_left (hbound (x+d j) hj) (norm_nonneg (c j))
  simpa only [mul_left_comm] using hh

end SharpIntegralFillings

namespace SharpIntegralFillings.MetricDifferentiation
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]
  {X : Type*} [MetricSpace X]

lemma HasCenteredMetricDifferentialWithin.scalar_bound
    {s : Set E} {f : s → X} {p : Seminorm ℝ E} {x : s}
    (h : HasCenteredMetricDifferentialWithin s f p x)
    (hx : Tendsto (fun t => μ (s ∩ closedBall (x : E) t) / μ (closedBall (x : E) t))
      (𝓝[>] 0) (𝓝 1))
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u)
    {F : E → ℝ} (hF : ∀ y : s, F y = u (f y))
    {ℓ : E →L[ℝ] ℝ} (hD : HasFDerivWithinAt F ℓ s x) (v : E) :
    |ℓ v| ≤ (K : ℝ)*p v := by
  classical
  let r : E → ℝ := fun z => if hz : z ∈ s then dist (f ⟨z,hz⟩) (f x) else 0
  have hr : (fun y => r y-p (y-(x : E))) =o[𝓝[s] (x : E)] (fun y => y-(x : E)) := by
    rw [nhdsWithin_eq_map_subtype_coe x.property, Asymptotics.isLittleO_map]
    change (fun y : s => dist (f y) (f x)-p ((y : E)-(x : E))) =o[𝓝 x]
      (fun y : s => (y : E)-(x : E)) at h
    convert h using 1
    · ext y
      simp only [Function.comp_apply,r,dite_eq_left y.property,Subtype.coe_eta]
    · rfl
  apply scalar_derivative_bound_of_metric_differential μ hx hD hr (v := v)
  intro y hy
  have hh := hu.dist_le_mul (f ⟨y,hy⟩) (f x)
  rw [Real.dist_eq, ←hF ⟨y,hy⟩, ←hF x] at hh
  simpa only [r,dite_eq_left hy] using hh

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma scalarOn_lipschitzOn {s : Set E} {f : s → X} {K J : ℝ≥0}
    (hf : LipschitzWith J f) {u : X → ℝ} (hu : LipschitzWith K u) :
    LipschitzOnWith (K*J) (scalarOn f u) s := by
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  simpa only [scalarOn,dite_eq_left ha,dite_eq_left hb,Function.comp_apply,Subtype.dist_eq] using
    (hu.comp hf).dist_le_mul ⟨a,ha⟩ ⟨b,hb⟩

lemma ae_scalarOn_derivative_bound {s : Set E} (hs : MeasurableSet s) {f : s → X}
    {J : ℝ≥0} (hf : LipschitzWith J f) {p : E → Seminorm ℝ E}
    (hd : ∀ᵐ x ∂μ.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩)
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ x ∂μ.restrict s, ∀ v,
      |fderivWithin ℝ (scalarOn f u) s x v| ≤ (K : ℝ)*p x v := by
  obtain ⟨F,hF,heq⟩ := (scalarOn_lipschitzOn hf hu).extend_real
  have haediff := hF.ae_differentiableAt (μ := μ)
  filter_upwards [hd,ae_restrict_mem hs,Besicovitch.ae_tendsto_measure_inter_div μ s,
    haediff.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hxs hxd hFx
  have hD : HasFDerivWithinAt (scalarOn f u) (fderivWithin ℝ (scalarOn f u) s x) s x := by
    apply DifferentiableWithinAt.hasFDerivWithinAt
    exact hFx.differentiableWithinAt.congr heq (heq hxs)
  intro v
  apply (hx hxs).scalar_bound μ hxd hu _ hD v
  intro y
  simp only [scalarOn,dite_eq_left y.property,Subtype.coe_eta]
end SharpIntegralFillings.MetricDifferentiation

open Set MeasureTheory
open scoped RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_Degenerate
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
open MeasureTheory Filter Set
open scoped Topology

variable {X : Type*} [MetricSpace X]
lemma det_rows_eq_zero_of_seminorm_kernel {n : ℕ}
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (L : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hL : ∀ i, ∃ K : ℝ, ∀ v, |L i v| ≤ K*p v)
    (hker : ¬ ∀ v, p v = 0 → v = 0) :
    Matrix.det (fun i j => L i (EuclideanSpace.single j 1)) = 0 := by
  classical
  push Not at hker
  obtain ⟨v,hpv,hv⟩ := hker
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨fun j => v j,?_,?_⟩
  · intro h
    apply hv
    ext j
    simpa using congrFun h j
  · ext i
    obtain ⟨K,hK⟩ := hL i
    have hLv : L i v = 0 := by
      apply abs_nonpos_iff.mp
      simpa only [hpv,mul_zero] using hK v
    have hsum : ∑ j, v j • EuclideanSpace.single j (1 : ℝ) = v := by
      simpa using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    have hli := congrArg (L i) hsum
    rw [_root_.map_sum] at hli
    simp only [map_smul,smul_eq_mul] at hli
    change ∑ j, L i (EuclideanSpace.single j 1) * v j = 0
    simpa only [mul_comm,hLv] using hli

theorem ae_scalarOn_det_eq_zero_of_degenerate {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    {f : s → X} {K : ℝ≥0} (hf : LipschitzWith K f)
    {p : EuclideanSpace ℝ (Fin n) → Seminorm ℝ (EuclideanSpace ℝ (Fin n))}
    (hd : ∀ᵐ x ∂volume.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩)
    (π : Fin n → X → ℝ) (hπ : ∀ i, ∃ J : ℝ≥0, LipschitzWith J (π i)) :
    ∀ᵐ x ∂volume.restrict s, (¬ ∀ v, p x v = 0 → v = 0) →
      Matrix.det (fun i j => fderivWithin ℝ (scalarOn f (π i)) s x
        (EuclideanSpace.single j 1)) = 0 := by
  choose J hJ using hπ
  have hb : ∀ᵐ x ∂volume.restrict s, ∀ i v,
      |fderivWithin ℝ (scalarOn f (π i)) s x v| ≤ (J i : ℝ)*p x v := by
    rw [eventually_all]
    intro i
    exact ae_scalarOn_derivative_bound volume hs hf hd (hJ i)
  filter_upwards [hb] with x hx hker
  exact det_rows_eq_zero_of_seminorm_kernel (p x) _ (fun i => ⟨J i,hx i⟩) hker

end SharpIntegralFillings.MetricDifferentiation

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Differentiation_FullRank
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma exists_nat_lower_bound_iff {p : Seminorm ℝ E} (hp : Continuous p) :
    (∃ n : ℕ, ∀ v : E, ‖v‖ ≤ ((n : ℝ)+1)*p v) ↔ ∀ v, p v = 0 → v = 0 := by
  constructor
  · rintro ⟨n,hn⟩ v hv
    have := hn v
    rw [hv,mul_zero] at this
    exact norm_eq_zero.mp (le_antisymm this (norm_nonneg v))
  · intro hp0
    by_cases hE : Subsingleton E
    · exact ⟨0, fun v => by simp [Subsingleton.elim v 0]⟩
    let : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    obtain ⟨v,hv⟩ := exists_ne (0 : E)
    have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hs : (Metric.sphere (0 : E) 1).Nonempty := by
      refine ⟨‖v‖⁻¹ • v,?_⟩
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_pos hnorm,inv_mul_cancel₀ hnorm.ne']
    obtain ⟨w,hw,hwmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hs hp.continuousOn
    have hwnorm : ‖w‖ = 1 := by simpa using hw
    have hw0 : w ≠ 0 := by intro h; simp [h] at hwnorm
    have hpw : 0 < p w := lt_of_le_of_ne (apply_nonneg p w) (by
      intro h; exact hw0 (hp0 w h.symm))
    obtain ⟨n,hn⟩ := exists_nat_gt (1 / p w)
    refine ⟨n,fun z => ?_⟩
    by_cases hz : z = 0
    · simp [hz]
    have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hzunit : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_pos hznorm,inv_mul_cancel₀ hznorm.ne']
    have hmin : p w ≤ p (‖z‖⁻¹ • z) := hwmin hzunit
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_inv,abs_of_pos hznorm] at hmin
    have hn' : 1 ≤ ((n : ℝ)+1)*p w := by
      have hh : 1 < (n : ℝ)*p w := (div_lt_iff₀ hpw).mp hn
      nlinarith
    calc ‖z‖ = ‖z‖*1 := (mul_one _).symm
      _ ≤ ‖z‖*(((n : ℝ)+1)*p w) := mul_le_mul_of_nonneg_left hn' (norm_nonneg z)
      _ ≤ ‖z‖*(((n : ℝ)+1)*(‖z‖⁻¹*p z)) := by
        gcongr
      _ = ((n : ℝ)+1)*p z := by field_simp

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

lemma measurableSet_metricSeminorm_lower_bound (hf : LipschitzWith K f) (A : ℝ) :
    MeasurableSet {x : E | ∀ v : E, ‖v‖ ≤ A * metricSeminorm f x v} := by
  have heq : {x : E | ∀ v : E, ‖v‖ ≤ A * metricSeminorm f x v} =
      ⋂ i : ℕ, {x : E | ‖denseSeq E i‖ ≤ A * metricSeminorm f x (denseSeq E i)} := by
    ext x
    simp only [mem_ofPred_eq,mem_iInter]
    constructor
    · exact fun h i => h _
    · intro h v
      exact (denseRange_denseSeq E).induction_on v
        (isClosed_le continuous_norm ((metricSeminorm_lipschitz hf x).continuous.const_mul A)) h
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le measurable_const ((measurable_metricSeminorm_apply hf _).const_mul A)

theorem exists_bilipschitz_fullRank_pieces
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ (⊤ : ℝ≥0∞)) :
    ∃ (t : ℕ → Set E) (J : ℕ → ℝ≥0),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      μ ((s ∩ {x | ∃ n : ℕ, ∀ v : E,
        ‖v‖ ≤ ((n : ℝ)+1)*metricSeminorm f x v}) \ ⋃ i, t i) = 0 ∧
      ∀ i, LipschitzWith K (fun x : t i => f x) ∧
        AntilipschitzWith (J i) (fun x : t i => f x) := by
  classical
  let U : ℕ → Set E := fun n => s ∩ {x | ∀ v : E,
    ‖v‖ ≤ ((n : ℝ)+1)*metricSeminorm f x v}
  have hU (n : ℕ) : MeasurableSet (U n) :=
    hs.inter (measurableSet_metricSeminorm_lower_bound hf _)
  have hUf (n : ℕ) : μ (U n) ≠ (⊤ : ℝ≥0∞) :=
    ((measure_mono inter_subset_left).trans_lt hsf.lt_top).ne
  have H (n : ℕ) := exists_ae_bilipschitz_partition_of_bound μ hf (hU n) (hUf n)
    (A := n+1) (by positivity) (by
      intro x hx v
      simpa using hx.2 v)
  choose T hTm hTs hTd hT0 hTb using H
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let V : ℕ → Set E := fun i => T (e i).1 (e i).2
  let t := disjointed V
  have htV (i : ℕ) : t i ⊆ T (e i).1 (e i).2 := disjointed_le V i
  have hcover (n : ℕ) : (⋃ j, T n j) ⊆ ⋃ i, t i := by
    rw [iUnion_disjointed]
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨e.symm (n,j),?_⟩
    simpa [V] using hj
  refine ⟨t,fun i => 2*((e i).1+1),
    fun i => MeasurableSet.disjointed (fun j => hTm _ _) i,
    fun i => (htV i).trans ((hTs _ _).trans inter_subset_left),disjoint_disjointed V,?_,?_⟩
  · have hnull (n : ℕ) : μ (U n \ ⋃ i, t i) = 0 :=
      measure_mono_null (sdiff_subset_sdiff_right (hcover n)) (hT0 n)
    apply measure_mono_null _ (measure_iUnion_null hnull)
    intro x hx
    obtain ⟨n,hn⟩ := hx.1.2
    exact mem_iUnion.mpr ⟨n,⟨⟨hx.1.1,hn⟩,hx.2⟩⟩
  · intro i
    refine ⟨LipschitzWith.of_dist_le_mul (fun a b => hf.dist_le_mul a b),?_⟩
    apply AntilipschitzWith.of_le_mul_dist
    intro a b
    exact (hTb _ _).2.le_mul_dist ⟨a,htV i a.property⟩ ⟨b,htV i b.property⟩

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open MeasureTheory Filter Set Metric
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X]

theorem exists_lipschitz_chart_decomposition {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s) (hsf : volume s ≠ (⊤ : ℝ≥0∞))
    {f : s → X} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin n)))
      (J : ℕ → ℝ≥0) (hts : ∀ i, t i ⊆ s),
      (∀ i, MeasurableSet (t i)) ∧ Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      (∀ i, LipschitzWith K (fun x : t i => f ⟨x,hts i x.property⟩) ∧
        AntilipschitzWith (J i) (fun x : t i => f ⟨x,hts i x.property⟩)) ∧
      ∀ (π : Fin n → X → ℝ), (∀ i, ∃ L : ℝ≥0, LipschitzWith L (π i)) →
        ∀ᵐ x ∂volume.restrict s, x ∉ ⋃ i, t i →
          Matrix.det (fun i j => fderivWithin ℝ (scalarOn f (π i)) s x
            (EuclideanSpace.single j 1)) = 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let Y := Set.range f
  let : SeparableSpace Y := (isSeparable_range hf.continuous).separableSpace
  let F : s → Y := fun x => ⟨f x,x,rfl⟩
  let e := kuratowskiEmbedding Y
  have he : Isometry e := kuratowskiEmbedding.isometry Y
  let F₀ : E → ↥(lp (fun _ : ℕ => ℝ) (⊤ : ENNReal)) :=
    fun x => if hx : x ∈ s then e (F ⟨x,hx⟩) else 0
  have hF₀ : LipschitzOnWith K F₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    dsimp only [F₀]
    rw [dite_eq_left hx,dite_eq_left hy,he.dist_eq]
    exact hf.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,heq⟩ := hF₀.extend_lp_infty
  let Z := Set.range g
  let : SeparableSpace Z := (isSeparable_range hg.continuous).separableSpace
  let : Nonempty Z := ⟨⟨g 0,0,rfl⟩⟩
  let G : E → Z := fun x => ⟨g x,x,rfl⟩
  have hG : LipschitzWith K G := LipschitzWith.of_dist_le_mul hg.dist_le_mul
  have hdist (y z : s) : dist (G y) (G z) = dist (f y) (f z) := by
    change dist (g y) (g z) = _
    rw [←heq y.property, ←heq z.property]
    dsimp only [F₀]
    rw [dite_eq_left y.property,dite_eq_left z.property]
    exact he.dist_eq (F y) (F z)
  let p := metricSeminorm G
  have hdiff : ∀ᵐ x ∂volume.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩ := by
    have hd := (ae_hasCenteredMetricDifferential volume hG).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := volume) (s := s)))
    filter_upwards [hd] with x hx hxs
    have hc : Tendsto (fun y : s => (y : E)) (𝓝 (⟨x,hxs⟩ : s)) (𝓝 x) :=
      continuous_subtype_val.tendsto _
    have hr := hx.comp_tendsto hc
    change (fun y : s => dist (G (y : E)) (G ((⟨x,hxs⟩ : s) : E)) -
      p x ((y : E)-x)) =o[𝓝 (⟨x,hxs⟩ : s)] (fun y : s => (y : E)-x) at hr
    have hdist' (y : s) : dist (G (y : E)) (G x) = dist (f y) (f ⟨x,hxs⟩) :=
      hdist y ⟨x,hxs⟩
    simpa only [HasCenteredMetricDifferentialWithin,hdist'] using hr
  obtain ⟨t,J,htm,hts,htd,ht0,htb⟩ := exists_bilipschitz_fullRank_pieces volume hG hs hsf
  refine ⟨t,J,hts,htm,htd,?_,?_⟩
  · intro i
    constructor
    · apply LipschitzWith.of_dist_le_mul
      intro a b
      exact hf.dist_le_mul ⟨a,hts i a.property⟩ ⟨b,hts i b.property⟩
    · apply AntilipschitzWith.of_le_mul_dist
      intro a b
      have hh := (htb i).2.le_mul_dist a b
      change dist (a : E) (b : E) ≤ (J i : ℝ)*dist (G a) (G b) at hh
      rw [hdist ⟨a,hts i a.property⟩ ⟨b,hts i b.property⟩] at hh
      exact hh
  · intro π hπ
    have hcover : ∀ᵐ x ∂volume.restrict s, (∀ v, p x v = 0 → v = 0) → x ∈ ⋃ i, t i := by
      have hz : ∀ᵐ x ∂volume, x ∉
          (s ∩ {x | ∃ n : ℕ, ∀ v : E, ‖v‖ ≤ ((n : ℝ)+1)*metricSeminorm G x v}) \ ⋃ i, t i :=
        ae_iff.mpr (by
          convert ht0 using 1
          all_goals try with_reducible_and_instances rfl
          congr 1
          ext x
          simp only [mem_ofPred_eq,not_not]
          rfl)
      filter_upwards [hz.filter_mono (ae_mono Measure.restrict_le_self),ae_restrict_mem hs] with x hx hxs hp0
      have hbound := (exists_nat_lower_bound_iff (metricSeminorm_lipschitz hG x).continuous).2 hp0
      by_contra hnot
      exact hx ⟨⟨hxs,hbound⟩,hnot⟩
    filter_upwards [hcover,ae_scalarOn_det_eq_zero_of_degenerate hs hf hdiff π hπ] with x hx hv hnot
    apply hv
    exact fun hp0 => hnot (hx hp0)

end SharpIntegralFillings.MetricDifferentiation

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
end

section
-- module Solutions.OAIQ219_IF.IntegralFillings_Charts_StraightPieces
attribute [-instance] _root_.OAI.SharpIntegralFillings.Foundations.testClass_nonempty _root_.OAI.SharpIntegralFillings.Foundations.unitTestClass_nonempty _root_.OAI.SharpIntegralFillings.Optimality.instNonemptyElemEucUnitBall
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

namespace SharpIntegralFillings.EuclideanStraightening
open Set MeasureTheory Filter
open scoped Topology NNReal

variable {d : ℕ}
lemma coordinate_scalarOn_fderiv {s : Set (Euc d)} {x : Euc d}
    (hu : UniqueDiffWithinAt ℝ s x) (hxs : x ∈ s) {F : Euc d → Euc d}
    (hF : DifferentiableAt ℝ F x) (i : Fin d) :
    fderivWithin ℝ (MetricDifferentiation.scalarOn (fun y : s => F y)
      (EuclideanSpace.proj i)) s x =
      (EuclideanSpace.proj i).comp (fderiv ℝ F x) := by
  apply HasFDerivWithinAt.fderivWithin _ hu
  have hD := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hF.hasFDerivAt
  apply hD.hasFDerivWithinAt.congr
  · intro y hy
    simp only [MetricDifferentiation.scalarOn,dite_eq_left hy,Function.comp_apply]
  · simp only [MetricDifferentiation.scalarOn,dite_eq_left hxs,Function.comp_apply]

theorem exists_replaceMap_pieces {s : Set (Euc d)} (hs : MeasurableSet s)
    (hsf : volume s ≠ (⊤ : ℝ≥0∞)) (j : Fin d) {g : Euc d → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    ∃ (t : ℕ → Set (Euc d)) (J : ℕ → ℝ≥0) (_hts : ∀ i, t i ⊆ s),
      (∀ i, MeasurableSet (t i)) ∧ Pairwise (fun i l => Disjoint (t i) (t l)) ∧
      (∀ i, LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊)
          (fun x : t i => replaceMap j g x) ∧
        AntilipschitzWith (J i) (fun x : t i => replaceMap j g x)) ∧
      ∀ᵐ x ∂volume.restrict s, x ∉ ⋃ i, t i →
        fderiv ℝ g x (EuclideanSpace.single j 1) = 0 := by
  classical
  let F : s → Euc d := fun x => replaceMap j g x
  have hF : LipschitzWith (1+K+‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ)‖₊) F := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    exact (replaceMap_lipschitz j hg).dist_le_mul a b
  obtain ⟨t,J,hts,htm,htd,htb,hzero⟩ :=
    MetricDifferentiation.exists_lipschitz_chart_decomposition hs hsf hF
  refine ⟨t,J,hts,htm,htd,htb,?_⟩
  let π : Fin d → Euc d → ℝ := fun i x => x i
  have hπ (i : Fin d) : ∃ L : ℝ≥0, LipschitzWith L (π i) :=
    ⟨‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖₊,
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).lipschitz⟩
  filter_upwards [hzero π hπ,ae_uniqueDiffWithinAt volume s,
    (hg.ae_differentiableAt (μ := volume)).filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem hs] with x hx hu hgx hxs hnot
  have he (i : Fin d) : fderivWithin ℝ (MetricDifferentiation.scalarOn F (π i)) s x =
      (EuclideanSpace.proj i).comp (fderiv ℝ (replaceMap j g) x) :=
    coordinate_scalarOn_fderiv hu hxs (replaceMap_hasFDerivAt hgx j).differentiableAt i
  have hd := hx hnot
  simp only [he,ContinuousLinearMap.comp_apply] at hd
  rw [←det_replaceMap_fderiv hgx j]
  exact hd

end SharpIntegralFillings.EuclideanStraightening

namespace SharpIntegralFillings.EuclideanStraightening
open Set MeasureTheory Filter
open scoped Topology NNReal

theorem exists_straightened_pieces_oai {k : ℕ} {s : Set (Euc (k+1))}
    (hs : MeasurableSet s) (hsf : volume s ≠ (⊤ : ℝ≥0∞))
    {g : Euc (k+1) → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    ∃ (t : ℕ → Set (Euc (k+1))) (dir : ℕ → Fin (k+1)) (J : ℕ → ℝ≥0),
      (∀ i, t i ⊆ s) ∧ (∀ i, MeasurableSet (t i)) ∧
      Pairwise (fun i l => Disjoint (t i) (t l)) ∧
      (∀ i, LipschitzWith (1+K+‖(EuclideanSpace.proj (dir i) : Euc (k+1) →L[ℝ] ℝ)‖₊)
          (fun x : t i => straightenMap (dir i) g x) ∧
        AntilipschitzWith (J i) (fun x : t i => straightenMap (dir i) g x)) ∧
      ∀ᵐ x ∂volume.restrict s, x ∉ ⋃ i, t i → fderiv ℝ g x = 0 := by
  classical
  choose t J hts htm _htd htb hz using fun j : Fin (k+1) =>
    exists_replaceMap_pieces hs hsf j hg
  let := Denumerable.ofEncodableOfInfinite (Fin (k+1) × ℕ)
  let e : ℕ ≃ Fin (k+1) × ℕ := (Denumerable.eqv _).symm
  let V : ℕ → Set (Euc (k+1)) := fun i => t (e i).1 (e i).2
  have hsub (i : ℕ) : disjointed V i ⊆ t (e i).1 (e i).2 := disjointed_le V i
  have hcover : (⋃ i, disjointed V i) = ⋃ j, ⋃ l, t j l := by
    rw [iUnion_disjointed]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨(e i).1,(e i).2,hi⟩
    · rintro ⟨j,l,h⟩
      refine ⟨e.symm (j,l),?_⟩
      simpa only [V,e.apply_symm_apply] using h
  refine ⟨disjointed V,fun i => (e i).1,fun i => J (e i).1 (e i).2,
    fun i => (hsub i).trans (hts _ _),
    fun i => MeasurableSet.disjointed (fun l => htm (e l).1 (e l).2) i,
    disjoint_disjointed V,?_,?_⟩
  · intro i
    constructor
    · apply LipschitzWith.of_dist_le_mul
      intro a b
      exact (straightenMap_lipschitz (e i).1 hg).dist_le_mul a b
    · apply AntilipschitzWith.of_le_mul_dist
      intro a b
      have h := (htb (e i).1 (e i).2).2.le_mul_dist
        ⟨a,hsub i a.property⟩ ⟨b,hsub i b.property⟩
      simpa only [straightenMap,Function.comp_apply,(switchZero (e i).1).isometry.dist_eq,
        Subtype.dist_eq] using h
  · filter_upwards [ae_all_iff.mpr hz] with x hx hnot
    have h0 (j : Fin (k+1)) : fderiv ℝ g x (EuclideanSpace.single j 1) = 0 := by
      apply hx j
      intro hj
      apply hnot
      rw [hcover]
      exact mem_iUnion.mpr ⟨j,hj⟩
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin (k+1)) ℝ).toBasis.ext
    intro j
    simpa only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,ContinuousLinearMap.coe_coe,
      _root_.zero_apply] using h0 j

end SharpIntegralFillings.EuclideanStraightening
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

end

end OAI
end

theorem solution : type_of% @OAI.SharpIntegralFillings.EuclideanStraightening.exists_straightened_pieces_oai := @OAI.SharpIntegralFillings.EuclideanStraightening.exists_straightened_pieces_oai
