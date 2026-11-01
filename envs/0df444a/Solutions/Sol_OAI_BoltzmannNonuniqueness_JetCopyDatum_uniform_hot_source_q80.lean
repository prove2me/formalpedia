-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.uniform_hot_source_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:06:41.038642+00:00
-- url     : https://prove2.me/submissions/f05da8a7-7671-4f11-bba3-fdbefef84619

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_HotRepresentative_ae_good_q80

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AxialFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Singular line integrals in the Carleman slice bound

For `q > 1`, the one-dimensional slice of the transverse power singularity
is integrable away from the line through the axis and has exactly the
power `|A|^(1-q)` appearing in Section 3, equation `ker:line-integral`.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.AxialSlices

theorem lineProfile_pos (q s : ℝ) : 0 < lineProfile q s := by
  unfold lineProfile
  exact Real.rpow_pos_of_pos (by positivity) _

theorem integrable_lineProfile {q : ℝ} (hq : 1 < q) : Integrable (lineProfile q) := by
  change Integrable (fun s : ℝ => (1 + s ^ 2) ^ (-q / 2))
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (r := q) (by simpa using hq)
  simpa only [Real.norm_eq_abs, sq_abs] using h

theorem lineConstant_pos {q : ℝ} (hq : 1 < q) : 0 < lineConstant q := by
  have hs : Function.support (lineProfile q) = univ := by
    ext s
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (lineProfile_pos q s).ne'
  apply (integral_pos_iff_support_of_nonneg (fun s => (lineProfile_pos q s).le)
    (integrable_lineProfile hq)).mpr
  rw [hs]
  simp

theorem lineProfile_scale (q A s : ℝ) (hA : A ≠ 0) :
    (A ^ 2 + s ^ 2) ^ (-q / 2) = |A| ^ (-q) * lineProfile q (s / |A|) := by
  have ha : 0 < |A| := abs_pos.mpr hA
  have hsq : A ^ 2 + s ^ 2 = |A| ^ 2 * (1 + (s / |A|) ^ 2) := by
    field_simp
    nlinarith [sq_abs A]
  rw [hsq, Real.mul_rpow (sq_nonneg _) (by positivity)]
  have hp : (|A| ^ 2) ^ (-q / 2) = |A| ^ (-q) := by
    rw [← Real.rpow_natCast_mul ha.le 2]
    congr 1
    ring
  rw [hp]
  rfl

theorem integrable_singular_line {q A : ℝ} (hq : 1 < q) (hA : A ≠ 0) :
    Integrable (fun s : ℝ => (A ^ 2 + s ^ 2) ^ (-q / 2)) := by
  have h := ((integrable_lineProfile hq).comp_div (abs_ne_zero.mpr hA)).const_mul
    (|A| ^ (-q))
  apply h.congr
  filter_upwards [] with s
  exact (lineProfile_scale q A s hA).symm

/-- Exact singular line integral, including finiteness in a separate theorem above. -/
theorem singular_line_formula {q A : ℝ} (hq : 1 < q) (hA : A ≠ 0) :
    Integrable (fun s : ℝ => (A ^ 2 + s ^ 2) ^ (-q / 2)) ∧
      (∫ s : ℝ, (A ^ 2 + s ^ 2) ^ (-q / 2)) = lineConstant q * |A| ^ (1 - q) := by
  refine ⟨integrable_singular_line hq hA, ?_⟩
  have ha : 0 < |A| := abs_pos.mpr hA
  simp_rw [lineProfile_scale q A _ hA]
  rw [integral_const_mul, Measure.integral_comp_div]
  simp only [abs_abs, smul_eq_mul]
  have hp : |A| ^ (-q) * |A| = |A| ^ (1 - q) := by
    calc
      |A| ^ (-q) * |A| = |A| ^ (-q) * |A| ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = |A| ^ (-q + 1) := (Real.rpow_add ha _ _).symm
      _ = |A| ^ (1 - q) := by congr 1; ring
  change |A| ^ (-q) * (|A| * lineConstant q) = _
  rw [← mul_assoc, hp, mul_comm]

end BoltzmannNonuniqueness.AxialSlices

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityWeight
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.TransverseAverage.circleArea_isFiniteMeasure _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-!
# The transverse singularity in the velocity majorant

Section 3 uses `H(v) = exp(-‖v‖²) * ⟨v⟩^(-100) * (1 + ‖v̄‖^(-q))`.
Thus its polynomial factor is `(1 + ‖v‖²)^(-50)`. The values assigned on
the velocity axis use Mathlib's real-power convention and do not affect
Lebesgue integrability.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.VelocityWeight

theorem singularity_nonneg (q : ℝ) (u : Transverse) : 0 ≤ singularity q u :=
  Real.rpow_nonneg (norm_nonneg _) _

theorem H_nonneg (q : ℝ) (v : Velocity) : 0 ≤ H q v := by
  unfold H singularity
  positivity

theorem H_pos (q : ℝ) (v : Velocity) : 0 < H q v := by
  unfold H
  apply mul_pos
  · exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)
  · linarith [singularity_nonneg q (transverse v)]

end BoltzmannNonuniqueness.VelocityWeight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_TransverseAverage
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Uniform transverse disk bounds

This proves the translated disk estimate `ker:disk-singularity` from Section 3.
The singular contribution is split at distance `R` from the origin. Inside,
polar integration is explicit; outside, the singularity is at most `R⁻ᑫ`.
-/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.TransverseDisk

theorem disk_volume_real (a : Transverse) {R : ℝ} (hR : 0 ≤ R) :
    volume.real (ball a R) = Real.pi * R ^ 2 := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hR, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

private theorem singularity_split_bound {q R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (u : Transverse) :
    singularity q u ≤ (ball (0 : Transverse) R).indicator (singularity q) u + R ^ (-q) := by
  by_cases hu : u ∈ ball (0 : Transverse) R
  · rw [indicator_of_mem hu]
    have hn : 0 ≤ R ^ (-q) := Real.rpow_nonneg hR.le _
    linarith
  · rw [indicator_of_notMem hu, zero_add]
    have hnorm : R ≤ ‖u‖ := le_of_not_gt (by simpa only [mem_ball_zero_iff] using hu)
    exact Real.rpow_le_rpow_of_nonpos hR hnorm (neg_nonpos.mpr hq)

end BoltzmannNonuniqueness.TransverseDisk

end

end

section

/-!
# Transverse collision-line coordinates

An orthonormal line chart gives the regular and singular terms in the
geometric slice estimate of Section 3. The singular distance is assumed
nonzero here; the product-measure argument must remove its null exceptional set.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.AxialSlices

namespace BoltzmannNonuniqueness.TransverseLine

theorem inner_quarterTurn (e : Transverse) : inner ℝ e (quarterTurn e) = 0 := by
  simp [PiLp.inner_apply, quarterTurn, Fin.sum_univ_two]
  ring

theorem norm_quarterTurn (e : Transverse) : ‖quarterTurn e‖ = ‖e‖ := by
  have h : ‖quarterTurn e‖ ^ 2 = ‖e‖ ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, quarterTurn, Fin.sum_univ_two]
    ring
  nlinarith [norm_nonneg e, norm_nonneg (quarterTurn e)]

theorem norm_line_sq (e : Transverse) (D s : ℝ) (he : ‖e‖ = 1) :
    ‖line e D s‖ ^ 2 = D ^ 2 + s ^ 2 := by
  have hnorm : e 0 ^ 2 + e 1 ^ 2 = 1 := by
    have hsq : ‖e‖ ^ (2 : ℕ) = 1 := by rw [he]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at hsq
    exact hsq
  calc
    _ = (D ^ 2 + s ^ 2) * (e 0 ^ 2 + e 1 ^ 2) := by
      simp [line, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, quarterTurn]
      ring
    _ = _ := by rw [hnorm, mul_one]

theorem inner_line (e : Transverse) (D s : ℝ) (he : ‖e‖ = 1) :
    inner ℝ e (line e D s) = D := by
  simp only [line, inner_add_right, inner_smul_right, inner_quarterTurn,
    real_inner_self_eq_norm_sq, he]
  ring

theorem line_singularity (q : ℝ) (e : Transverse) (D s : ℝ) (he : ‖e‖ = 1) :
    ‖line e D s‖ ^ (-q) = (D ^ 2 + s ^ 2) ^ (-q / 2) := by
  rw [← norm_line_sq e D s he, ← Real.rpow_natCast_mul (norm_nonneg _) 2]
  congr 1
  ring

theorem lineWeight_nonneg (q : ℝ) (e : Transverse) (D s : ℝ) :
    0 ≤ lineWeight q e D s := by
  unfold lineWeight
  positivity

theorem integrable_line_singularity {q D : ℝ} (hq : 1 < q) (hD : D ≠ 0)
    (e : Transverse) (he : ‖e‖ = 1) :
    Integrable (fun s : ℝ => ‖line e D s‖ ^ (-q)) := by
  simpa only [line_singularity q e D _ he] using integrable_singular_line hq hD

theorem integrableOn_lineWeight {q D : ℝ} (hq : 1 < q) (hD : D ≠ 0)
    (e : Transverse) (he : ‖e‖ = 1) (m R : ℝ) :
    IntegrableOn (lineWeight q e D) (Icc (m - R) (m + R)) := by
  exact (integrableOn_const (measure_Icc_lt_top.ne)).add
    (integrable_line_singularity hq hD e he).integrableOn

/-- The line bound is uniform in the center of the retained segment. -/
theorem integral_lineWeight_le {q D R : ℝ} (hq : 1 < q) (hD : D ≠ 0)
    (hR : 0 ≤ R) (e : Transverse) (he : ‖e‖ = 1) (m : ℝ) :
    (∫ s in Icc (m - R) (m + R), lineWeight q e D s) ≤
      2 * R + lineConstant q * |D| ^ (1 - q) := by
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (m - R) (m + R)) :=
    integrableOn_const measure_Icc_lt_top.ne
  have hs := integrable_line_singularity hq hD e he
  have hb := setIntegral_le_integral (s := Icc (m - R) (m + R)) hs
    (Filter.Eventually.of_forall (fun s => Real.rpow_nonneg (norm_nonneg (line e D s)) (-q)))
  unfold lineWeight
  rw [integral_add hc hs.integrableOn, setIntegral_const, smul_eq_mul, mul_one]
  have hvol : volume.real (Icc (m - R) (m + R)) = 2 * R := by
    rw [Real.volume_real_Icc]
    rw [max_eq_left (by linarith : 0 ≤ m + R - (m - R))]
    ring
  rw [hvol]
  have hfull : (∫ s : ℝ, ‖line e D s‖ ^ (-q)) = lineConstant q * |D| ^ (1 - q) := by
    simp_rw [line_singularity q e D _ he]
    exact (singular_line_formula hq hD).2
  linarith

theorem lintegral_lineWeight_le {q D R : ℝ} (hq : 1 < q) (hD : D ≠ 0)
    (hR : 0 ≤ R) (e : Transverse) (he : ‖e‖ = 1) (m : ℝ) :
    (∫⁻ s in Icc (m - R) (m + R), ENNReal.ofReal (lineWeight q e D s)) ≤
      ENNReal.ofReal (2 * R + lineConstant q * |D| ^ (1 - q)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_lineWeight hq hD e he m R)
    (Filter.Eventually.of_forall (fun s => lineWeight_nonneg q e D s))]
  exact ENNReal.ofReal_le_ofReal (integral_lineWeight_le hq hD hR e he m)

end BoltzmannNonuniqueness.TransverseLine

end

end

section

/-!
# Transverse angular averages

The angular singularity in `ker:transverse-expectation` is integrable when
`q < 2`. Gaussian Cartesian integration and polar coordinates prove this
without choosing a trigonometric chart on the unit circle.
-/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.TransverseAverage

theorem norm_unitAxis : ‖unitAxis‖ = 1 := by
  simp [unitAxis, EuclideanSpace.single, PiLp.norm_single]

private theorem radialMeasure_ne_zero : Measure.volumeIoiPow 1 ≠ 0 := by
  intro hz
  have h := Measure.volumeIoiPow_apply_Iio 1 (⟨1, by norm_num⟩ : Ioi (0 : ℝ))
  rw [hz] at h
  norm_num at h

private instance radialMeasure_neZero : NeZero (Measure.volumeIoiPow 1) :=
  ⟨radialMeasure_ne_zero⟩

theorem circleArea_real_univ : circleArea.real univ = 2 * Real.pi := by
  rw [circleArea, Measure.toSphere_real_apply_univ]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two]
  norm_num [ENNReal.toReal_ofReal, Real.pi_pos.le]

private theorem integrable_abs_rpow_gaussian {q : ℝ} (hq : q < 2) :
    Integrable (fun x : ℝ => |x| ^ (1 - q) * Real.exp (-x ^ 2)) := by
  have hr := integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one
    (show -1 < 1 - q by linarith)
  have h := (integrable_fun_norm_addHaar (volume : Measure ℝ)
    (f := fun r : ℝ => r ^ (1 - q) * Real.exp (-r ^ 2))).mpr
      (by simpa using hr)
  simpa only [Real.norm_eq_abs, sq_abs] using h

private theorem cartesianSplit_measurePreserving : MeasurePreserving cartesianSplit :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)

private theorem gaussianPower_unitAxis (q : ℝ) (x : Transverse) :
    gaussianPower q unitAxis x = |x 0| ^ (1 - q) * Real.exp (-‖x‖ ^ 2) := by
  simp [gaussianPower, unitAxis, EuclideanSpace.inner_single_left]

theorem integrable_gaussianPower_unitAxis {q : ℝ} (hq : q < 2) :
    Integrable (gaussianPower q unitAxis) := by
  have hi := (integrable_abs_rpow_gaussian hq).mul_prod (integrable_exp_neg_mul_sq zero_lt_one)
  have hc := cartesianSplit_measurePreserving.integrable_comp_of_integrable hi
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [gaussianPower_unitAxis]
  change |x 0| ^ (1 - q) * Real.exp (-‖x‖ ^ 2) =
    |x 0| ^ (1 - q) * Real.exp (-(x 0) ^ 2) * Real.exp (-1 * (x 1) ^ 2)
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, neg_add_rev,
    Real.exp_add, neg_mul, one_mul]
  ring

private theorem gaussianPower_rotate (e : Transverse) (he : ‖e‖ = 1) :
    ∃ R : Transverse ≃ₗᵢ[ℝ] Transverse,
      ∀ q x, gaussianPower q e (R x) = gaussianPower q unitAxis x := by
  let R : Transverse ≃ₗᵢ[ℝ] Transverse := (ℝ ∙ (e - unitAxis))ᗮ.reflection
  have hnorm : ‖e‖ = ‖unitAxis‖ := he.trans norm_unitAxis.symm
  have hRe : R e = unitAxis := Submodule.reflection_sub hnorm
  refine ⟨R, ?_⟩
  intro q x
  have hi : inner ℝ e (R x) = inner ℝ unitAxis x := by
    have h := R.inner_map_eq_flip e x
    rw [hRe] at h
    exact h.symm
  simp only [gaussianPower, hi, R.norm_map]

theorem integrable_gaussianPower {q : ℝ} (hq : q < 2)
    (e : Transverse) (he : ‖e‖ = 1) : Integrable (gaussianPower q e) := by
  obtain ⟨R, hR⟩ := gaussianPower_rotate e he
  apply (R.measurePreserving.integrable_comp_emb R.toHomeomorph.measurableEmbedding).mp
  change Integrable (fun x => gaussianPower q e (R x))
  simpa only [hR] using integrable_gaussianPower_unitAxis hq

theorem integral_gaussianPower (q : ℝ) (e : Transverse) (he : ‖e‖ = 1) :
    (∫ x, gaussianPower q e x) = ∫ x, gaussianPower q unitAxis x := by
  obtain ⟨R, hR⟩ := gaussianPower_rotate e he
  rw [← R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding]
  simp only [hR]

private theorem gaussianPower_polar (q : ℝ) (e : Transverse)
    (ω : Circle) (r : Ioi (0 : ℝ)) :
    gaussianPower q e ((r : ℝ) • (ω : Transverse)) = angular q e ω * radialGaussian q r := by
  have hω : ‖(ω : Transverse)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hr : 0 < (r : ℝ) := r.property
  simp only [gaussianPower, angular, radialGaussian, inner_smul_right, abs_mul,
    abs_of_pos hr, norm_smul, Real.norm_eq_abs, hω, mul_one]
  rw [Real.mul_rpow hr.le (abs_nonneg _)]
  ring

private theorem integrable_polar_gaussianPower {q : ℝ} (hq : q < 2)
    (e : Transverse) (he : ‖e‖ = 1) :
    Integrable (fun p : Circle × Ioi (0 : ℝ) => angular q e p.1 * radialGaussian q p.2)
      (circleArea.prod (Measure.volumeIoiPow 1)) := by
  let H := homeomorphUnitSphereProd Transverse
  have hs : Integrable (fun x : ({0}ᶜ : Set Transverse) => gaussianPower q e x)
      ((volume : Measure Transverse).comap (↑)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mp
      (integrable_gaussianPower hq e he).integrableOn
  have hp := (volume : Measure Transverse).measurePreserving_homeomorphUnitSphereProd
  have hi := (hp.integrable_comp_emb H.measurableEmbedding).mp
    (show Integrable ((fun p => gaussianPower q e ((H.symm p : ({0}ᶜ : Set Transverse)) : Transverse))
      ∘ H) ((volume : Measure Transverse).comap (↑)) by
      simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hs)
  convert hi using 1
  · funext p
    simp only [H, homeomorphUnitSphereProd_symm_apply_coe, gaussianPower_polar]
  · simp only [circleArea, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub]

theorem integrable_angular {q : ℝ} (hq : q < 2)
    (e : Transverse) (he : ‖e‖ = 1) : Integrable (angular q e) circleArea := by
  obtain ⟨r, hr⟩ := (integrable_polar_gaussianPower hq e he).prod_left_ae.exists
  have hc : radialGaussian q r ≠ 0 := by
    unfold radialGaussian
    exact ne_of_gt (mul_pos (Real.rpow_pos_of_pos r.property _) (Real.exp_pos _))
  exact (integrable_mul_const_iff (isUnit_iff_ne_zero.mpr hc) _).mp hr

theorem integrable_radialGaussian {q : ℝ} (hq : q < 2) :
    Integrable (radialGaussian q) (Measure.volumeIoiPow 1) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hi : IntegrableOn (fun r : ℝ => r ^ (2 - q) * Real.exp (-r ^ 2)) (Ioi 0) :=
    by simpa only [neg_mul, one_mul] using
      integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one (by linarith : -1 < 2 - q)
  have hs := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hi
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  simp only [Function.comp_def, radialGaussian, pow_one,
    ENNReal.toReal_ofReal r.property.le, smul_eq_mul]
  rw [show 2 - q = 1 + (1 - q) by ring, Real.rpow_add r.property, Real.rpow_one]
  ring

theorem integral_radialGaussian_pos {q : ℝ} (hq : q < 2) :
    0 < ∫ r, radialGaussian q r ∂Measure.volumeIoiPow 1 := by
  have hp : ∀ r, 0 < radialGaussian q r := by
    intro r
    exact mul_pos (Real.rpow_pos_of_pos r.property _) (Real.exp_pos _)
  apply (integral_pos_iff_support_of_nonneg (fun r => (hp r).le)
    (integrable_radialGaussian hq)).mpr
  have hs : Function.support (radialGaussian q) = univ := by
    apply Set.eq_univ_of_forall
    intro r
    exact ne_of_gt (hp r)
  rw [hs]
  exact Measure.measure_univ_pos.mpr radialMeasure_ne_zero

private theorem gaussian_polar_identity (q : ℝ) (e : Transverse) :
    (∫ x, gaussianPower q e x) = (∫ ω, angular q e ω ∂circleArea) *
      ∫ r, radialGaussian q r ∂Measure.volumeIoiPow 1 := by
  let H := homeomorphUnitSphereProd Transverse
  have hp := (volume : Measure Transverse).measurePreserving_homeomorphUnitSphereProd.integral_comp
    H.measurableEmbedding (fun p => gaussianPower q e (H.symm p))
  calc
    _ = ∫ x : ({0}ᶜ : Set Transverse), gaussianPower q e x
        ∂((volume : Measure Transverse).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫ p : Circle × Ioi (0 : ℝ), angular q e p.1 * radialGaussian q p.2
        ∂circleArea.prod (Measure.volumeIoiPow 1) := by
      simpa only [circleArea, H, Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe, gaussianPower_polar,
        finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using hp
    _ = _ := integral_prod_mul _ _

theorem integral_angular_eq {q : ℝ} (hq : q < 2) (e : Transverse) (he : ‖e‖ = 1) :
    (∫ ω, angular q e ω ∂circleArea) = ∫ ω, angular q unitAxis ω ∂circleArea := by
  apply mul_right_cancel₀ (ne_of_gt (integral_radialGaussian_pos hq))
  rw [← gaussian_polar_identity, ← gaussian_polar_identity, integral_gaussianPower q e he]

theorem angularMass_pos (q : ℝ) : 0 < angularMass q := by
  have h : 0 ≤ ∫ ω, angular q unitAxis ω ∂circleArea :=
    integral_nonneg (fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  unfold angularMass
  linarith [Real.pi_pos]

theorem integral_one_add_angular {q : ℝ} (hq : q < 2)
    (e : Transverse) (he : ‖e‖ = 1) :
    (∫ ω, 1 + angular q e ω ∂circleArea) = angularMass q := by
  rw [integral_add (integrable_const 1) (integrable_angular hq e he), integral_const,
    smul_eq_mul, mul_one, circleArea_real_univ, integral_angular_eq hq e he]
  rfl

theorem kernel_nonneg (q : ℝ) (e n : Transverse) : 0 ≤ kernel q e n := by
  unfold kernel
  positivity

private theorem kernel_on_ray (q : ℝ) (e : Transverse) (ω : Circle) (r : Ioi (0 : ℝ)) :
    kernel q e ((r : ℝ) • (ω : Transverse)) = (1 + angular q e ω) * (r : ℝ)⁻¹ := by
  have hω : ‖(ω : Transverse)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hr : 0 < (r : ℝ) := r.property
  simp [kernel, angular, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hω,
    smul_smul, inv_mul_cancel₀ hr.ne', div_eq_mul_inv]

private theorem radialCutoff_weight (D : ℝ) (r : Ioi (0 : ℝ)) :
    (r : ℝ) * radialCutoff D r = (Iio D).indicator (fun _ : ℝ => (1 : ℝ)) r := by
  have hr₀ : (r : ℝ) ≠ 0 := (show (0 : ℝ) < r from r.property).ne'
  by_cases hr : (r : ℝ) < D <;> simp [radialCutoff, hr, indicator, hr₀]

private theorem integrable_radialCutoff {D : ℝ} (_hD : 0 < D) :
    Integrable (radialCutoff D) (Measure.volumeIoiPow 1) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hi : IntegrableOn ((Iio D).indicator (fun _ : ℝ => (1 : ℝ))) (Ioi 0) := by
    rw [integrableOn_indicator_iff measurableSet_Iio]
    have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 D) :=
      integrableOn_const (by simp)
    rw [inter_comm, Ioi_inter_Iio]
    exact hc
  have hs := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hi
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  simp only [pow_one, ENNReal.toReal_ofReal r.property.le, smul_eq_mul,
    radialCutoff_weight, Function.comp_def]

private theorem integral_radialCutoff {D : ℝ} (hD : 0 < D) :
    (∫ r, radialCutoff D r ∂Measure.volumeIoiPow 1) = D := by
  rw [Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [pow_one, smul_eq_mul]
  have heq : (fun r : Ioi (0 : ℝ) => (ENNReal.ofReal (r : ℝ)).toReal * radialCutoff D r) =
      fun r : Ioi (0 : ℝ) => (Iio D).indicator (fun _ : ℝ => (1 : ℝ)) r := by
    funext r
    rw [ENNReal.toReal_ofReal (show (0 : ℝ) ≤ r from le_of_lt r.property), radialCutoff_weight]
  rw [heq]
  rw [integral_subtype_comap measurableSet_Ioi,
    integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
    inter_comm, Ioi_inter_Iio, setIntegral_const, smul_eq_mul, mul_one]
  simp [measureReal_def, Real.volume_Ioo, hD.le]

private theorem cutoff_kernel_polar (q D : ℝ) (e : Transverse)
    (ω : Circle) (r : Ioi (0 : ℝ)) :
    (ball (0 : Transverse) D).indicator (kernel q e) ((r : ℝ) • (ω : Transverse)) =
      (1 + angular q e ω) * radialCutoff D r := by
  have hω : ‖(ω : Transverse)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hr : 0 < (r : ℝ) := r.property
  by_cases hrD : (r : ℝ) < D
  · rw [indicator_of_mem]
    · simp only [kernel_on_ray, radialCutoff, ite_eq_left hrD]
    · simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hω,
        mul_one] using hrD
  · rw [indicator_of_notMem]
    · simp only [radialCutoff, ite_eq_right hrD, mul_zero]
    · simpa only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hω,
        mul_one] using hrD

theorem integrableOn_kernel_centeredDisk {q D : ℝ} (hq : q < 2) (hD : 0 < D)
    (e : Transverse) (he : ‖e‖ = 1) : IntegrableOn (kernel q e) (ball 0 D) := by
  let H := homeomorphUnitSphereProd Transverse
  have hi := ((integrable_const 1).add (integrable_angular hq e he)).mul_prod
    (integrable_radialCutoff hD)
  have hp : MeasurePreserving H ((volume : Measure Transverse).comap (↑))
      (circleArea.prod (Measure.volumeIoiPow 1)) := by
    simpa only [circleArea, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using
      (volume : Measure Transverse).measurePreserving_homeomorphUnitSphereProd
  have hs := hp.integrable_comp_of_integrable hi
  have hsub : Integrable (fun x : ({0}ᶜ : Set Transverse) =>
      (ball (0 : Transverse) D).indicator (kernel q e) x)
      ((volume : Measure Transverse).comap (↑)) := by
    convert hs using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    have h := cutoff_kernel_polar q D e (H x).1 (H x).2
    simpa only [H, ← homeomorphUnitSphereProd_symm_apply_coe,
      Homeomorph.symm_apply_apply, Function.comp_def, Pi.add_apply] using h
  have hfull : Integrable ((ball (0 : Transverse) D).indicator (kernel q e)) := by
    have h : IntegrableOn ((ball (0 : Transverse) D).indicator (kernel q e)) {0}ᶜ := by
      apply (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).mpr
      exact hsub
    simpa only [IntegrableOn, restrict_compl_singleton] using h
  exact (integrable_indicator_iff measurableSet_ball).mp hfull

/-- The radial Jacobian exactly cancels the inverse-distance factor. -/
theorem integral_kernel_centeredDisk {q D : ℝ} (hq : q < 2) (hD : 0 < D)
    (e : Transverse) (he : ‖e‖ = 1) :
    (∫ n in ball (0 : Transverse) D, kernel q e n) = D * angularMass q := by
  let H := homeomorphUnitSphereProd Transverse
  let f := (ball (0 : Transverse) D).indicator (kernel q e)
  have hp := (volume : Measure Transverse).measurePreserving_homeomorphUnitSphereProd.integral_comp
    H.measurableEmbedding (fun p => f (H.symm p))
  calc
    _ = ∫ n, f n := (integral_indicator measurableSet_ball).symm
    _ = ∫ x : ({0}ᶜ : Set Transverse), f x ∂((volume : Measure Transverse).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl, restrict_compl_singleton]
    _ = ∫ p : Circle × Ioi (0 : ℝ), (1 + angular q e p.1) * radialCutoff D p.2
        ∂circleArea.prod (Measure.volumeIoiPow 1) := by
      simpa only [f, circleArea, H, Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe, cutoff_kernel_polar,
        finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using hp
    _ = (∫ ω, 1 + angular q e ω ∂circleArea) *
        ∫ r, radialCutoff D r ∂Measure.volumeIoiPow 1 :=
      integral_prod_mul (fun ω : Circle => 1 + angular q e ω) (radialCutoff D)
    _ = _ := by rw [integral_one_add_angular hq e he, integral_radialCutoff hD]; ring

private theorem translated_cutoff_eq {d : ℝ} (_hd : 0 < d) (q : ℝ)
    (e v p : Transverse) (hp : p ∈ ball (0 : Transverse) d) :
    (ball (0 : Transverse) (‖v‖ + d)).indicator (kernel q e) (v - p) = kernel q e (v - p) := by
  apply indicator_of_mem
  rw [mem_ball_zero_iff]
  have hp' : ‖p‖ < d := mem_ball_zero_iff.mp hp
  exact (norm_sub_le v p).trans_lt (by linarith)

theorem integrableOn_kernel_translatedDisk {q d : ℝ} (hq : q < 2) (hd : 0 < d)
    (e : Transverse) (he : ‖e‖ = 1) (v : Transverse) :
    IntegrableOn (fun p => kernel q e (v - p)) (ball (0 : Transverse) d) := by
  have hD : 0 < ‖v‖ + d := by positivity
  have hi := (integrableOn_kernel_centeredDisk hq hD e he).integrable_indicator measurableSet_ball
  have hs := ((volume : Measure Transverse).measurePreserving_sub_left v).integrable_comp_of_integrable hi
  exact hs.integrableOn.congr_fun (fun p hp => translated_cutoff_eq hd q e v p hp) measurableSet_ball

theorem integral_kernel_translatedDisk_le {q d : ℝ} (hq : q < 2) (hd : 0 < d)
    (e : Transverse) (he : ‖e‖ = 1) (v : Transverse) :
    (∫ p in ball (0 : Transverse) d, kernel q e (v - p)) ≤ (‖v‖ + d) * angularMass q := by
  have hD : 0 < ‖v‖ + d := by positivity
  let f := (ball (0 : Transverse) (‖v‖ + d)).indicator (kernel q e)
  have hi : Integrable f :=
    (integrableOn_kernel_centeredDisk hq hD e he).integrable_indicator measurableSet_ball
  have hs := ((volume : Measure Transverse).measurePreserving_sub_left v).integrable_comp_of_integrable hi
  calc
    _ = ∫ p in ball (0 : Transverse) d, f (v - p) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro p hp
      exact (translated_cutoff_eq hd q e v p hp).symm
    _ ≤ ∫ p, f (v - p) :=
      setIntegral_le_integral hs (ae_of_all _ (fun p =>
        indicator_nonneg (fun n _ => kernel_nonneg q e n) (v - p)))
    _ = ∫ n, f n :=
      ((volume : Measure Transverse).measurePreserving_sub_left v).integral_comp
        (Homeomorph.subLeft v).measurableEmbedding f
    _ = _ := by
      rw [integral_indicator measurableSet_ball, integral_kernel_centeredDisk hq hD e he]

theorem norm_direction {v : Transverse} (hv : v ≠ 0) : ‖direction v‖ = 1 :=
  norm_smul_inv_norm hv

private theorem direction_inner_self {v : Transverse} (hv : v ≠ 0) :
    inner ℝ (direction v) v = ‖v‖ := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [direction, real_inner_smul_left, real_inner_self_eq_norm_sq]
  field_simp

private theorem kernel_small_shift_le {q : ℝ} (hq : 1 < q)
    {v p : Transverse} (hv : v ≠ 0) (hp : ‖p‖ ≤ ‖v‖ / 2) :
    kernel q (direction v) (v - p) ≤ 2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v‖ := by
  have hv₀ : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have he : ‖direction v‖ = 1 := norm_direction hv
  have hip : inner ℝ (direction v) p ≤ ‖p‖ := by
    have h := abs_real_inner_le_norm (direction v) p
    rw [he, one_mul] at h
    exact (le_abs_self _).trans h
  have hilow : ‖v‖ / 2 ≤ inner ℝ (direction v) (v - p) := by
    rw [inner_sub_right, direction_inner_self hv]
    linarith
  have hnn : ‖v‖ / 2 ≤ ‖v - p‖ := by
    have h := abs_real_inner_le_norm (direction v) (v - p)
    rw [he, one_mul] at h
    exact hilow.trans ((le_abs_self _).trans h)
  have hn₀ : 0 < ‖v - p‖ := lt_of_lt_of_le (by positivity) hnn
  have hnupper : ‖v - p‖ ≤ ‖v‖ + ‖p‖ := norm_sub_le v p
  have hcos : (1 / 3 : ℝ) ≤ |inner ℝ (direction v) (direction (v - p))| := by
    have hinner : inner ℝ (direction v) (direction (v - p)) =
        inner ℝ (direction v) (v - p) / ‖v - p‖ := by
      simp only [direction, inner_smul_right, div_eq_mul_inv]
      ring
    rw [hinner]
    apply le_trans _ (le_abs_self _)
    apply (le_div_iff₀ hn₀).mpr
    nlinarith
  have hpow : |inner ℝ (direction v) (direction (v - p))| ^ (1 - q) ≤
      (1 / 3 : ℝ) ^ (1 - q) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hcos (by linarith)
  calc
    _ ≤ (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v - p‖ := by
      apply div_le_div_of_nonneg_right _ hn₀.le
      change 1 + |inner ℝ (direction v) (direction (v - p))| ^ (1 - q) ≤ _
      linarith
    _ ≤ (1 + (1 / 3 : ℝ) ^ (1 - q)) / (‖v‖ / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hnn
    _ = _ := by field_simp

theorem expectationConstant_pos (q : ℝ) : 0 < expectationConstant q := by
  unfold expectationConstant
  have hM := angularMass_pos q
  positivity

/-- The uniform disk case of `ker:transverse-expectation`, with explicit integrability above. -/
theorem uniformDisk_expectation_le {q d : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d)
    {v : Transverse} (hv : v ≠ 0) :
    (∫ p in ball (0 : Transverse) d, kernel q (direction v) (v - p)) / (Real.pi * d ^ 2) ≤
      expectationConstant q / ‖v‖ := by
  have hv₀ : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have he : ‖direction v‖ = 1 := norm_direction hv
  have hden : 0 < Real.pi * d ^ 2 := by positivity
  have hM : 0 < angularMass q := angularMass_pos q
  have hsmall : 0 ≤ 2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) := by positivity
  by_cases hdsmall : d ≤ ‖v‖ / 2
  · have hi := integrableOn_kernel_translatedDisk hq₂ hd (direction v) he v
    have hc : IntegrableOn
        (fun _ : Transverse => 2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v‖)
        (ball (0 : Transverse) d) := integrableOn_const measure_ball_lt_top.ne
    have hb : (∫ p in ball (0 : Transverse) d, kernel q (direction v) (v - p)) ≤
        Real.pi * d ^ 2 * (2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v‖) := by
      calc
        _ ≤ ∫ _p in ball (0 : Transverse) d,
            2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v‖ :=
          setIntegral_mono_on hi hc measurableSet_ball (fun p hp =>
            kernel_small_shift_le hq₁ hv ((mem_ball_zero_iff.mp hp).le.trans hdsmall))
        _ = _ := by
          rw [setIntegral_const, smul_eq_mul, TransverseDisk.disk_volume_real 0 hd.le]
    have hn : (∫ p in ball (0 : Transverse) d, kernel q (direction v) (v - p)) /
        (Real.pi * d ^ 2) ≤ 2 * (1 + (1 / 3 : ℝ) ^ (1 - q)) / ‖v‖ := by
      apply (div_le_iff₀ hden).mpr
      nlinarith [hb]
    apply hn.trans
    apply div_le_div_of_nonneg_right _ hv₀.le
    unfold expectationConstant
    have h : 0 ≤ 6 * angularMass q / Real.pi := by positivity
    linarith
  · have hrd : ‖v‖ ≤ 2 * d := by linarith
    have hb := integral_kernel_translatedDisk_le hq₂ hd (direction v) he v
    have hb' : (∫ p in ball (0 : Transverse) d, kernel q (direction v) (v - p)) ≤
        3 * d * angularMass q := by
      have h := mul_le_mul_of_nonneg_right (show ‖v‖ + d ≤ 3 * d by linarith) hM.le
      exact hb.trans h
    have hratio : (3 * d * angularMass q) / (Real.pi * d ^ 2) ≤
        (6 * angularMass q / Real.pi) / ‖v‖ := by
      apply (div_le_div_iff₀ hden hv₀).mpr
      rw [← mul_assoc (6 * angularMass q / Real.pi) Real.pi,
        div_mul_cancel₀ _ Real.pi_ne_zero]
      have h := mul_le_mul_of_nonneg_left hrd
        (show 0 ≤ 3 * d * angularMass q by positivity)
      nlinarith
    apply (div_le_div_of_nonneg_right hb' hden.le).trans (hratio.trans _)
    apply div_le_div_of_nonneg_right _ hv₀.le
    unfold expectationConstant
    linarith

theorem kernel_at_zero_input (q : ℝ) {v : Transverse} (hv : v ≠ 0) :
    kernel q (direction v) v = 2 / ‖v‖ := by
  have hn := norm_direction hv
  change (1 + |inner ℝ (direction v) (direction v)| ^ (1 - q)) / ‖v‖ = 2 / ‖v‖
  simp only [real_inner_self_eq_norm_sq, hn, one_pow,
    abs_one, Real.one_rpow, one_add_one_eq_two]

theorem atomZero_expectation_le (q : ℝ) {v : Transverse} (hv : v ≠ 0) :
    (∫ p, kernel q (direction v) (v - p) ∂Measure.dirac (0 : Transverse)) ≤
      expectationConstant q / ‖v‖ := by
  rw [integral_dirac, sub_zero, kernel_at_zero_input q hv]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  unfold expectationConstant
  have hM := angularMass_pos q
  have hr : 0 ≤ (1 / 3 : ℝ) ^ (1 - q) := by positivity
  have h : 0 ≤ 6 * angularMass q / Real.pi := by positivity
  linarith

end BoltzmannNonuniqueness.TransverseAverage

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PlaneChart
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The graph chart for a collision plane

The chart records actual three-dimensional velocities. Its displacement
satisfies the collision-plane equation, and the three-dimensional ball
restriction is precisely the transverse-plus-axial restriction used in
the geometric slice estimate. Identifying its measure with the Carleman
plane measure remains a separate change-of-variables theorem.
-/

noncomputable section

open scoped RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseLine
open BoltzmannNonuniqueness.TransverseAverage

namespace BoltzmannNonuniqueness.PlaneChart

theorem inner_split (v w : Velocity) :
    inner ℝ v w = inner ℝ (transverse v) (transverse w) + axial v * axial w := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    transverse, axial]
  rw [Fin.sum_univ_castSucc]
  congr 1
  ring

theorem transverse_chart (v p : Velocity) (z s : ℝ) :
    transverse (chart v p z s) =
      line (direction (normal v p)) (offset v p - slope v p * z) s :=
  transverse_join _ _

theorem axial_chart (v p : Velocity) (z s : ℝ) : axial (chart v p z s) = axial v + z :=
  axial_join _ _

/-- The graph chart lies on the collision plane whenever the transverse normal is nonzero. -/
theorem chart_on_plane (v p : Velocity) (z s : ℝ) (hn : normal v p ≠ 0) :
    inner ℝ (v - p) (chart v p z s - v) = 0 := by
  have hnn : ‖normal v p‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hscale : ‖normal v p‖ • direction (normal v p) = normal v p := by
    rw [direction, smul_smul, mul_inv_cancel₀ hnn, one_smul]
  simp only [inner_split, transverse_sub, axial_sub, transverse_chart, axial_chart]
  change inner ℝ (normal v p)
    (line (direction (normal v p)) (offset v p - slope v p * z) s - transverse v) +
      axial (v - p) * (axial v + z - axial v) = 0
  conv_lhs => lhs; lhs; rw [← hscale]
  rw [real_inner_smul_left, inner_sub_right,
    inner_line _ _ _ (norm_direction hn)]
  change ‖normal v p‖ * ((offset v p - slope v p * z) - offset v p) +
    axial (v - p) * (axial v + z - axial v) = 0
  unfold slope
  field_simp
  ring

/-- Exact norm of the displacement, used for the genuine ball restriction. -/
theorem chart_displacement_norm_sq (v p : Velocity) (z s : ℝ) :
    ‖chart v p z s - v‖ ^ 2 =
      ‖line (direction (normal v p)) (offset v p - slope v p * z) s - transverse v‖ ^ 2 + z ^ 2 := by
  rw [norm_sq_split, transverse_sub, axial_sub, transverse_chart, axial_chart]
  congr 2
  ring

end BoltzmannNonuniqueness.PlaneChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DatumBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.TransverseAverage.radialMeasure_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Summable cold-jet datum bounds

Section 4 of the supplied manuscript bounds the mass and energy of each annulus by a constant
times `s_j²`, and its absolute entropy by a constant times `s_j² (1 + |log s_j|)`.
Those scalar bounds are summable for the stated geometric scales, and their tails converge
to zero. Indices start at zero; the manuscript's indices starting at one
are obtained by removing the first term.
-/

noncomputable section

open Filter Finset
open scoped Topology BigOperators

namespace BoltzmannNonuniqueness.DatumBounds

theorem scale_pos {s₀ η : ℝ} (hs₀ : 0 < s₀) (j : ℕ) : 0 < scale s₀ η j :=
  mul_pos hs₀ (Real.exp_pos _)

end BoltzmannNonuniqueness.DatumBounds

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetProfiles
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.instCountableLabel _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The cold-jet annuli and opposite stripe enlargements

These are the actual spatial masks of Section 4. The geometric scale is
indexed from zero here, representing the manuscript's first positive index.
-/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.DatumBounds

namespace BoltzmannNonuniqueness.JetGeometry

theorem gapCoefficient_pos {η : ℝ} (hη : 0 < η) : 0 < gapCoefficient η := by
  have h := Real.one_lt_exp_iff.mpr hη
  unfold gapCoefficient
  linarith

theorem gapCoefficient_le {η : ℝ} (hη : η ≤ Real.log 2) : gapCoefficient η ≤ 1 / 16 := by
  have h := Real.exp_le_exp.mpr hη
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  unfold gapCoefficient
  linarith

theorem enlargementWidth_pos {η s : ℝ} (hη : 0 < η) (hs : 0 < s) :
    0 < enlargementWidth η s := by
  have := gapCoefficient_pos hη
  unfold enlargementWidth
  positivity

theorem enlargement_witness {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    {positive : Bool} {y : Transverse} (hy : y ∈ enlargement η s positive) :
    ∃ x ∈ mask η s positive, dist y x ≤ 2 * enlargementWidth η s := by
  have hδ := enlargementWidth_pos hη hs
  obtain ⟨x, hx, hd⟩ := mem_iUnion₂.mp (cthickening_subset_iUnion_closedBall_of_lt (mask η s positive)
    (by positivity : 0 < 2 * enlargementWidth η s) (by linarith) hy)
  exact ⟨x, hx, mem_closedBall.mp hd⟩

theorem enlargement_subset_annulus {η s : ℝ} (hη : 0 < η) (hs : 0 < s)
    (positive : Bool) :
    enlargement η s positive ⊆ {y : Transverse | s < ‖y‖ ∧ ‖y‖ < Real.exp η * s} := by
  intro y hy
  obtain ⟨x, hx, hdist⟩ := enlargement_witness hη hs hy
  have h₁ := norm_sub_norm_le y x
  have h₂ := norm_sub_norm_le x y
  rw [← dist_eq_norm] at h₁ h₂
  rw [dist_comm x y] at h₂
  have hgap : 0 < gapCoefficient η * s ^ 2 := mul_pos (gapCoefficient_pos hη) (sq_pos_of_pos hs)
  have hcore := hx.1
  change s + gapCoefficient η * s ^ 2 < ‖x‖ ∧
    ‖x‖ < Real.exp η * s - gapCoefficient η * s ^ 2 at hcore
  dsimp only [enlargementWidth] at hdist
  constructor <;> linarith [hcore.1, hcore.2]

theorem scale_antitone {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η) :
    Antitone (scale s₀ η) := by
  intro i j hij
  unfold scale
  apply mul_le_mul_of_nonneg_left _ hs₀
  apply Real.exp_le_exp.mpr
  have hcast : (i : ℝ) ≤ j := by exact_mod_cast hij
  nlinarith

theorem outerRadius_eq (s₀ η : ℝ) (j : ℕ) :
    Real.exp η * jetScale s₀ η j = scale s₀ η j := by
  unfold jetScale scale
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem ordered_annuli {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    {i j : ℕ} (hij : i < j) :
    Real.exp η * jetScale s₀ η j ≤ jetScale s₀ η i := by
  rw [outerRadius_eq]
  exact scale_antitone hs₀ hη (Nat.succ_le_iff.mpr hij)

theorem distinct_scale_disjoint {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    {i j : ℕ} (hij : i ≠ j) (a b : Bool) :
    Disjoint (enlargement η (jetScale s₀ η i) a) (enlargement η (jetScale s₀ η j) b) := by
  apply disjoint_left.mpr
  intro y hyi hyj
  have hi := enlargement_subset_annulus hη (scale_pos hs₀ _) a hyi
  have hj := enlargement_subset_annulus hη (scale_pos hs₀ _) b hyj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have h := ordered_annuli hs₀.le hη.le hij
    dsimp only [jetScale] at h
    exact not_lt_of_ge h (hi.1.trans hj.2)
  · have h := ordered_annuli hs₀.le hη.le hji
    dsimp only [jetScale] at h
    exact not_lt_of_ge h (hj.1.trans hi.2)

theorem stripe_distance {s : ℝ} (hs : 0 < s) {x y : Transverse}
    (hx : x ∈ stripe s true) (hy : y ∈ stripe s false) : s ^ 2 / 4 < dist x y := by
  obtain ⟨k, hk₁, hk₂⟩ := hx
  obtain ⟨l, hl₁, hl₂⟩ := hy
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hk₁ hk₂ hl₁ hl₂
  have hcoord : |x 0 - y 0| ≤ dist x y := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs, dist_eq_norm] using PiLp.norm_apply_le (x - y) 0
  have hp : 0 < s ^ 2 := sq_pos_of_pos hs
  rcases le_or_gt k l with hkl | hlk
  · have hcast : (k : ℝ) ≤ l := by exact_mod_cast hkl
    have hh := mul_le_mul_of_nonneg_right hcast hp.le
    have : s ^ 2 / 4 < y 0 - x 0 := by nlinarith
    exact this.trans_le ((le_abs_self _).trans (by simpa only [abs_sub_comm] using hcoord))
  · have hcast : (l : ℝ) + 1 ≤ k := by exact_mod_cast (Int.add_one_le_iff.mpr hlk)
    have hh := mul_le_mul_of_nonneg_right hcast hp.le
    have : s ^ 2 / 4 < x 0 - y 0 := by nlinarith
    exact this.trans_le ((le_abs_self _).trans hcoord)

theorem opposite_enlargements_disjoint {η s : ℝ} (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hs : 0 < s) :
    Disjoint (enlargement η s true) (enlargement η s false) := by
  apply disjoint_left.mpr
  intro y hy₁ hy₂
  obtain ⟨x, hx, hxy⟩ := enlargement_witness hη hs hy₁
  obtain ⟨z, hz, hzy⟩ := enlargement_witness hη hs hy₂
  have hsep := stripe_distance hs hx.2 hz.2
  have hdist := dist_triangle x y z
  rw [dist_comm x y] at hdist
  have hc := mul_le_mul_of_nonneg_right (gapCoefficient_le hηmax) (sq_nonneg s)
  unfold enlargementWidth at hxy hzy
  nlinarith

theorem enlargement_inside_baseBall {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (j : ℕ) (a : Bool) : enlargement η (jetScale s₀ η j) a ⊆ ball 0 s₀ := by
  intro y hy
  have h := (enlargement_subset_annulus hη (scale_pos hs₀ _) a hy).2
  change ‖y‖ < Real.exp η * jetScale s₀ η j at h
  rw [outerRadius_eq] at h
  have hj := scale_antitone hs₀.le hη.le (Nat.zero_le j)
  have hzero : scale s₀ η 0 = s₀ := by simp [scale]
  rw [hzero] at hj
  simpa only [mem_ball, dist_zero_right] using h.trans_le hj

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Pairwise disjoint periodic cold-jet spatial enlargements -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetLattice

theorem integer_distance {m n : ℤ} (h : m ≠ n) : (1 : ℝ) ≤ |(m : ℝ) - n| := by
  have h' := Int.one_le_abs (sub_ne_zero.mpr h)
  exact_mod_cast h'

theorem distinct_transverse_shifts {m n : Lattice}
    (h : ∃ k : Fin 2, m k.castSucc ≠ n k.castSucc) :
    1 ≤ ‖transverseShift m - transverseShift n‖ := by
  obtain ⟨k, hk⟩ := h
  have hn := PiLp.norm_apply_le (transverseShift m - transverseShift n) k
  change ‖(m k.castSucc : ℝ) - n k.castSucc‖ ≤ _ at hn
  rw [Real.norm_eq_abs] at hn
  exact (integer_distance hk).trans hn

theorem common_point_transverse_lattice {s₀ η : ℝ} (hs₀ : 0 < s₀)
    (hsmax : s₀ ≤ 1 / 8) (hη : 0 < η) {t : ℝ} {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) :
    ∀ k : Fin 2, i.lattice k.castSucc = j.lattice k.castSucc := by
  by_contra! h
  have hsep := distinct_transverse_shifts h
  have hi' := enlargement_inside_baseBall hs₀ hη i.annulus i.positive hi.1
  have hj' := enlargement_inside_baseBall hs₀ hη j.annulus j.positive hj.1
  rw [mem_ball, dist_zero_right] at hi' hj'
  have htri := norm_sub_le (transverse x - transverseShift j.lattice)
    (transverse x - transverseShift i.lattice)
  have he : transverse x - transverseShift j.lattice - (transverse x - transverseShift i.lattice) =
      transverseShift i.lattice - transverseShift j.lattice := by abel
  rw [he] at htri
  linarith

theorem common_point_axial_lattice {t : ℝ} (ht : t ≤ 1 / 32)
    {s₀ η : ℝ} {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) :
    i.lattice (Fin.last 2) = j.lattice (Fin.last 2) := by
  by_contra h
  have hsep := integer_distance h
  have htri := abs_sub_le (axialShift i.lattice) (axial x) (axialShift j.lattice)
  rw [abs_sub_comm (axialShift i.lattice) (axial x)] at htri
  have hi' := hi.2
  have hj' := hj.2
  change |axial x - axialShift i.lattice| ≤ 1 / 8 + 2 * t + 1 / 16 at hi'
  change |axial x - axialShift j.lattice| ≤ 1 / 8 + 2 * t + 1 / 16 at hj'
  change 1 ≤ |axialShift i.lattice - axialShift j.lattice| at hsep
  linarith

theorem common_point_lattice {s₀ η t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (ht : t ≤ 1 / 32) {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) :
    i.lattice = j.lattice := by
  have htrans := common_point_transverse_lattice hs₀ hsmax hη hi hj
  have haxial := common_point_axial_lattice ht hi hj
  funext k
  refine Fin.lastCases haxial htrans k

theorem common_point_label {s₀ η t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (ht : t ≤ 1 / 32) {i j : Label} {x : Velocity}
    (hi : x ∈ spatialEnlargement s₀ η t i) (hj : x ∈ spatialEnlargement s₀ η t j) : i = j := by
  have hn := common_point_lattice hs₀ hsmax hη ht hi hj
  have hi' := hi.1
  have hj' := hj.1
  rw [← hn] at hj'
  have ha : i.annulus = j.annulus := by
    by_contra h
    exact (disjoint_left.mp (distinct_scale_disjoint hs₀ hη h i.positive j.positive)) hi' hj'
  have hs : i.positive = j.positive := by
    rw [← ha] at hj'
    by_contra h
    have hd := opposite_enlargements_disjoint hη hηmax
      (DatumBounds.scale_pos (η := η) hs₀ (i.annulus + 1))
    cases hiBool : i.positive <;> cases hjBool : j.positive
    · exact h (hiBool.trans hjBool.symm)
    · rw [hiBool] at hi'
      rw [hjBool] at hj'
      exact (disjoint_left.mp hd) hj' hi'
    · rw [hiBool] at hi'
      rw [hjBool] at hj'
      exact (disjoint_left.mp hd) hi' hj'
    · exact h (hiBool.trans hjBool.symm)
  cases i
  cases j
  simp_all

end BoltzmannNonuniqueness.JetLattice

end

end

section

/-! # Area bounds for the original striped cold-jet masks -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetMaskMeasure

theorem measurableSet_stripe (s : ℝ) (a : Bool) : MeasurableSet (stripe s a) := by
  unfold stripe
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  exact (measurableSet_lt measurable_const (by fun_prop : Measurable (fun y : Transverse => y 0))).inter
    (measurableSet_lt (by fun_prop : Measurable (fun y : Transverse => y 0)) measurable_const)

theorem measurableSet_annularCore (η s : ℝ) : MeasurableSet (annularCore η s) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

theorem measurableSet_mask (η s : ℝ) (a : Bool) : MeasurableSet (mask η s a) :=
  (measurableSet_annularCore η s).inter (measurableSet_stripe s a)

end BoltzmannNonuniqueness.JetMaskMeasure

end

end

section

/-! # A fixed smooth compactly supported thermal probability kernel -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetThermalKernel

theorem J_nonneg (v : Velocity) : 0 ≤ J v := bump.nonneg_normed v

theorem J_smooth : ContDiff ℝ (⊤ : ℕ∞) J := bump.contDiff_normed

theorem J_support : Function.support J = ball 0 1 := bump.support_normed_eq

theorem J_zero {v : Velocity} (hv : 1 ≤ ‖v‖) : J v = 0 := by
  by_contra h
  have hs : v ∈ Function.support J := h
  rw [J_support, mem_ball, dist_zero_right] at hs
  exact not_lt_of_ge hv hs

theorem bound_pos : 0 < bound := inv_pos.mpr bump.integral_pos

theorem J_le (v : Velocity) : J v ≤ bound := by
  unfold J ContDiffBump.normed bound
  exact (div_le_div_of_nonneg_right bump.le_one bump.integral_pos.le).trans_eq (one_div _)

end BoltzmannNonuniqueness.JetThermalKernel

end

end

section

/-! # Mass, support and integrability of translated thermal profiles -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetThermalKernel

namespace BoltzmannNonuniqueness.JetThermalLaw

theorem density_nonneg {d : ℝ} (hd : 0 ≤ d) (a v : Velocity) : 0 ≤ density d a v :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hd _)) (J_nonneg _)

end BoltzmannNonuniqueness.JetThermalLaw

end

end

section

/-! # Uniform mass and centered first moment of the barrier Gaussian -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetGaussianMoments

theorem mass_nonneg : 0 ≤ mass := integral_nonneg (fun _ => (Real.exp_pos _).le)
theorem moment_nonneg : 0 ≤ moment := integral_nonneg (fun _ => by
  exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)

end BoltzmannNonuniqueness.JetGaussianMoments

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarrierKinetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The exact one-dimensional core Jacobian and compression bound -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.AxialDerivative
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetCoreJacobian

theorem jacobian_pos {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z w : ℝ) : 0 < jacobian σ α γ s d t z w := by
  unfold jacobian
  have := A_nonneg hα hγ hs.le (sourceFoot σ α γ s d t z w)
  positivity

end BoltzmannNonuniqueness.JetCoreJacobian

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CarlemanNormalCoordinates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Energy algebra on a Carleman collision plane

These are the exact geometric and Gaussian identities used in Section 3.
The coarea/disintegration formula expressing the gain as a plane integral
is a separate theorem and is not assumed or asserted here.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

/-- The plane equation in the Carleman representation is exactly the energy equation. -/
theorem carleman_energy (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    ‖p‖ ^ 2 + ‖ξ‖ ^ 2 = ‖v‖ ^ 2 + ‖companionVelocity p ξ v‖ ^ 2 := by
  unfold companionVelocity
  rw [norm_sub_sq_real, norm_add_sq_real, inner_add_left]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq] at h
  rw [← real_inner_comm ξ v]
  nlinarith only [h]

/-- The observed speed is bounded by the total incoming energy. -/
theorem carleman_observed_energy_le (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    ‖v‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖ξ‖ ^ 2 := by
  have he := carleman_energy p ξ v h
  nlinarith only [he, sq_nonneg ‖companionVelocity p ξ v‖]

/-- Squared Japanese-bracket inequality used to transfer the polynomial weight. -/
theorem carleman_bracket_sq_le (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    1 + ‖v‖ ^ 2 ≤ (1 + ‖p‖ ^ 2) * (1 + ‖ξ‖ ^ 2) := by
  have he := carleman_observed_energy_le p ξ v h
  nlinarith only [he, mul_nonneg (sq_nonneg ‖p‖) (sq_nonneg ‖ξ‖)]

/-- The Gaussian ratio identity in equation `ker:energy-factor`. -/
theorem carleman_gaussian_ratio (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    Real.exp (-‖ξ‖ ^ 2) / Real.exp (-‖v‖ ^ 2) =
      Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) := by
  rw [← Real.exp_sub]
  congr 1
  have he := carleman_energy p ξ v h
  linarith only [he]

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_WeightAlgebra
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Weight transfer on a collision plane

The exact Gaussian identity and polynomial transfer turn the normalized
gain weight into the tilted cold measure used in `ker:tilted-kernel`.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.VelocityWeight

theorem W_pos (q : ℝ) (v : Velocity) : 0 < W q v := by
  unfold W
  linarith [singularity_nonneg q (transverse v)]

private theorem rpow_neg_fifty {x : ℝ} (hx : 0 ≤ x) :
    x ^ (-50 : ℝ) = (x ^ (50 : ℕ))⁻¹ := by
  rw [show (-50 : ℝ) = -(50 : ℕ) by norm_num, Real.rpow_neg hx, Real.rpow_natCast]

theorem H_ratio (q : ℝ) (ξ v : Velocity) :
    H q ξ / H q v = (Real.exp (-‖ξ‖ ^ 2) / Real.exp (-‖v‖ ^ 2)) *
      ((1 + ‖v‖ ^ 2) ^ (50 : ℕ) / (1 + ‖ξ‖ ^ 2) ^ (50 : ℕ)) * (W q ξ / W q v) := by
  unfold H
  change (Real.exp (-‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ (-50 : ℝ) * W q ξ) /
    (Real.exp (-‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (-50 : ℝ) * W q v) = _
  rw [rpow_neg_fifty (by positivity), rpow_neg_fifty (by positivity)]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem polynomial_ratio_le (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    (1 + ‖v‖ ^ 2) ^ (50 : ℕ) / (1 + ‖ξ‖ ^ 2) ^ (50 : ℕ) ≤
      (1 + ‖p‖ ^ 2) ^ (50 : ℕ) := by
  apply (div_le_iff₀ (by positivity : 0 < (1 + ‖ξ‖ ^ 2) ^ (50 : ℕ))).mpr
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (carleman_bracket_sq_le p ξ v h) 50

theorem tiltConstant_pos : 0 < tiltConstant := by unfold tiltConstant; positivity

theorem polynomial_le_gaussian (p : Velocity) :
    (1 + ‖p‖ ^ 2) ^ (50 : ℕ) ≤ tiltConstant * Real.exp (‖p‖ ^ 2) := by
  have hf : 0 < (Nat.factorial 50 : ℝ) := by positivity
  have h := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (1 + ‖p‖ ^ 2) (by positivity) 50)
  calc
    _ ≤ Real.exp (1 + ‖p‖ ^ 2) * (Nat.factorial 50 : ℝ) := h
    _ = _ := by unfold tiltConstant; rw [Real.exp_add]; ring

/-- The complete weight ratio estimate preceding the tilted-kernel bound. -/
theorem collision_weight_ratio_le (q : ℝ) (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    H q ξ / H q v ≤ tiltConstant *
      Real.exp (2 * ‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) * (W q ξ / W q v) := by
  rw [H_ratio, carleman_gaussian_ratio p ξ v h]
  have hw : 0 ≤ W q ξ / W q v := div_nonneg (W_pos q ξ).le (W_pos q v).le
  calc
    _ ≤ Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) *
        (1 + ‖p‖ ^ 2) ^ (50 : ℕ) * (W q ξ / W q v) := by
      apply mul_le_mul_of_nonneg_right _ hw
      exact mul_le_mul_of_nonneg_left (polynomial_ratio_le p ξ v h) (Real.exp_nonneg _)
    _ ≤ Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) *
        (tiltConstant * Real.exp (‖p‖ ^ 2)) * (W q ξ / W q v) := by
      apply mul_le_mul_of_nonneg_right _ hw
      exact mul_le_mul_of_nonneg_left (polynomial_le_gaussian p) (Real.exp_nonneg _)
    _ = _ := by
      rw [show Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) *
          (tiltConstant * Real.exp (‖p‖ ^ 2)) =
          tiltConstant * (Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) *
            Real.exp (‖p‖ ^ 2)) by ring, ← Real.exp_add]
      congr 3
      ring

/-- The singular part of the transverse normalization is uniformly bounded. -/
theorem singular_fraction_le_one {r : ℝ} (hr : 0 < r) (q : ℝ) :
    r ^ (-q) / (1 + r ^ (-q)) ≤ 1 := by
  apply (div_le_one (by positivity : 0 < 1 + r ^ (-q))).mpr
  linarith

/-- Near the axis, the regular part gains the positive power `q-1`. -/
theorem regular_fraction_le_power {r : ℝ} (hr : 0 < r) (q : ℝ) :
    r⁻¹ / (1 + r ^ (-q)) ≤ r ^ (q - 1) := by
  apply (div_le_iff₀ (by positivity : 0 < 1 + r ^ (-q))).mpr
  have he : r ^ (q - 1) * r ^ (-q) = r⁻¹ := by
    rw [← Real.rpow_add hr, show (q - 1) + -q = -1 by ring, Real.rpow_neg_one]
  rw [mul_add, mul_one, he]
  linarith [Real.rpow_nonneg hr.le (q - 1)]

theorem regular_fraction_le_one {r q : ℝ} (hr : 0 < r) (hq : 1 ≤ q) :
    r⁻¹ / (1 + r ^ (-q)) ≤ 1 := by
  by_cases hr₁ : r ≤ 1
  · exact (regular_fraction_le_power hr q).trans
      (Real.rpow_le_one hr.le hr₁ (by linarith))
  · have hi : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_not_ge hr₁)
    apply (div_le_one (by positivity : 0 < 1 + r ^ (-q))).mpr
    linarith [Real.rpow_nonneg hr.le (-q)]

/-- The shell alternative used to extract either a cold or a Gaussian tail. -/
theorem shell_alternative (p k : Velocity) {R : ℝ}
    (h : R < ‖p‖ + ‖k‖) : R / 4 < ‖p‖ ∨ R / 2 < ‖p + k‖ := by
  have he : k = (p + k) - p := by abel
  have hn : ‖k‖ ≤ ‖p + k‖ + ‖p‖ := by
    calc ‖k‖ = ‖(p + k) - p‖ := congrArg norm he
         _ ≤ ‖p + k‖ + ‖p‖ := norm_sub_le _ _
  by_cases hp : R / 4 < ‖p‖
  · exact Or.inl hp
  · exact Or.inr (by linarith)

theorem gaussian_shell_decay {w : Velocity} {R : ℝ} (hR : 0 ≤ R)
    (hw : R / 2 ≤ ‖w‖) : Real.exp (-‖w‖ ^ 2) ≤ Real.exp (-R ^ 2 / 4) := by
  apply Real.exp_le_exp.mpr
  nlinarith [norm_nonneg w]

end BoltzmannNonuniqueness.VelocityWeight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CarlemanOperator
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Nonnegative Carleman gain

Gamba, Panferov and Villani, *Upper Maxwellian bounds for the spatially
homogeneous Boltzmann equation*, Arch. Ration. Mech. Anal. 194 (2009),
253–282, Appendix C, Lemma 16 and the hard-sphere remark. The author's
preprint https://www.csun.edu/~panferov/research/umb_5.pdf gives the formula
on pp. 23–24. Their hard-sphere rate is `|g|/(4π)` in outgoing-direction
coordinates. Multiplication by `2π` gives the present absolute-normal
kernel and the coefficient `2` below.

The nonnegative measurable form of that identity is expressed in an explicit
plane chart. Its density formulation includes the plane-chart measure
identification and allows arbitrary nonnegative measurable densities.
-/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.PlaneChart
open scoped ENNReal

namespace BoltzmannNonuniqueness

/-- The algebraic estimate applies to every nondegenerate point of the actual chart. -/
theorem chart_weight_ratio_le (q : ℝ) (v p : Velocity) (z s : ℝ)
    (hn : normal v p ≠ 0) :
    VelocityWeight.H q (chart v p z s) / VelocityWeight.H q v ≤
      VelocityWeight.tiltConstant *
        Real.exp (2 * ‖p‖ ^ 2 - ‖companionVelocity p (chart v p z s) v‖ ^ 2) *
        (VelocityWeight.W q (chart v p z s) / VelocityWeight.W q v) :=
  VelocityWeight.collision_weight_ratio_le q p (chart v p z s) v (chart_on_plane v p z s hn)

theorem chartGain_mono_measure {c d : Measure Velocity} (hcd : c ≤ d)
    (h : Velocity → ℝ≥0∞) (v : Velocity) : chartGain c h v ≤ chartGain d h v := by
  unfold chartGain
  exact mul_le_mul' (le_rfl : (2 : ℝ≥0∞) ≤ 2)
    (lintegral_mono' hcd (fun _ => le_rfl))

theorem chartGain_add_measure (c d : Measure Velocity) (h : Velocity → ℝ≥0∞)
    (v : Velocity) : chartGain (c + d) h v = chartGain c h v + chartGain d h v := by
  unfold chartGain
  rw [lintegral_add_measure, mul_add]

theorem chartGain_smul_measure (a : ℝ≥0∞) (c : Measure Velocity)
    (h : Velocity → ℝ≥0∞) (v : Velocity) :
    chartGain (a • c) h v = a * chartGain c h v := by
  unfold chartGain
  rw [lintegral_smul_measure]
  simp only [smul_eq_mul]
  ac_rfl

/-- A bound proved for the explicit chart gain transfers to the original gain
under the stated published input. -/
theorem nonnegativeGain_le_of_chartGain
    (hcarleman : Published.GPV2009CarlemanInput)
    {f g : Velocity → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {B : Velocity → ℝ≥0∞}
    (hB : ∀ᵐ v : Velocity ∂volume, chartGain (volume.withDensity f) g v ≤ B v) :
    ∀ᵐ v : Velocity ∂volume, nonnegativeGain f g v ≤ B v := by
  filter_upwards [hcarleman f g hf hg, hB] with v hv hb
  rwa [hv]

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianFrequency
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The loss frequency of the normalized barrier Gaussian -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetGaussianMoments

namespace BoltzmannNonuniqueness.GaussianFrequency

theorem density_eq_gaussian {d : ℝ} (hd : 0 < d) (c b : ℝ) (u v : Velocity) :
    density c b d u v = gaussian (c * (d ^ 3)⁻¹) (b / d ^ 2) u v := by
  simp only [density, JetThermalLaw.scaled, kernel, gaussian, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd), mul_pow]
  have he : -b * ((d⁻¹) ^ 2 * ‖v - u‖ ^ 2) = -(b / d ^ 2) * ‖v - u‖ ^ 2 := by
    field_simp
  rw [he]
  ring

end BoltzmannNonuniqueness.GaussianFrequency

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_GainNonnegative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positivity and domination for the original gain integral -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.GainOrder

theorem integrand_nonneg {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (p : Velocity × Sphere) : 0 ≤ integrand f v p :=
  mul_nonneg (mul_nonneg (collisionKernel_nonneg _ _ _) (hf _)) (hf _)

theorem integrand_mono {f g : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w) (hfg : ∀ w, f w ≤ g w)
    (v : Velocity) (p : Velocity × Sphere) : integrand f v p ≤ integrand g v p := by
  unfold integrand
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hfg _) (collisionKernel_nonneg _ _ _))
    (hfg _) (hf _) (mul_nonneg (collisionKernel_nonneg _ _ _) ((hf _).trans (hfg _)))

theorem integrand_measurable {f : Velocity → ℝ} (hf : Measurable f) (v : Velocity) :
    Measurable (integrand f v) := by
  have hleft : Measurable (fun p : Velocity × Sphere => scatterLeft v p.1 p.2) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hright : Measurable (fun p : Velocity × Sphere => scatterRight v p.1 p.2) := by
    unfold scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : Velocity × Sphere => collisionKernel v p.1 p.2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact (hk.mul (hf.comp hleft)).mul (hf.comp hright)

theorem integrable_of_le {f g : Velocity → ℝ} (hm : Measurable f)
    (hf : ∀ w, 0 ≤ f w) (hfg : ∀ w, f w ≤ g w) (v : Velocity)
    (hg : Integrable (integrand g v) ((volume : Measure Velocity).prod sphereArea)) :
    Integrable (integrand f v) ((volume : Measure Velocity).prod sphereArea) := by
  apply hg.mono' (integrand_measurable hm v).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hf v p)]
  exact integrand_mono hf hfg v p

theorem integrable_const_mul (c : ℝ) {f : Velocity → ℝ} (v : Velocity)
    (hf : Integrable (integrand f v) ((volume : Measure Velocity).prod sphereArea)) :
    Integrable (integrand (fun w => c * f w) v) ((volume : Measure Velocity).prod sphereArea) := by
  convert hf.const_mul (c ^ 2) using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  unfold integrand
  ring

end BoltzmannNonuniqueness.GainOrder

end

end

section

/-! # Conversion from the nonnegative Carleman gain to the real collision operator -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.GainNonnegative

theorem self_eq_lintegral {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w) (v : Velocity) :
    nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v =
      ∫⁻ p, ENNReal.ofReal (GainOrder.integrand f v p)
        ∂((volume : Measure Velocity).prod sphereArea) := by
  unfold nonnegativeGain gainPairMeasure
  apply lintegral_congr
  intro p
  have hp := mul_nonneg (hf (scatterLeft v p.1 p.2)) (hf (scatterRight v p.1 p.2))
  have he : ENNReal.ofReal (collisionKernel v p.1 p.2) / 2 =
      ENNReal.ofReal (collisionKernel v p.1 p.2 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [← ENNReal.ofReal_mul (hf (scatterLeft v p.1 p.2)),
    ← ENNReal.ofReal_add hp hp, he,
    ← ENNReal.ofReal_mul (div_nonneg (collisionKernel_nonneg _ _ _) (by norm_num))]
  congr 1
  unfold GainOrder.integrand
  ring

theorem integrable_of_bound {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    {B : ℝ} (v : Velocity)
    (hb : nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v ≤
      ENNReal.ofReal B) :
    Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea) := by
  refine ⟨(GainOrder.integrand_measurable hm v).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (GainOrder.integrand_nonneg hf v)),
    ← self_eq_lintegral hf v]
  exact hb.trans_lt ENNReal.ofReal_lt_top

theorem gain_le_of_bound {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    {B : ℝ} (hB : 0 ≤ B) (v : Velocity) (x : Position)
    (hb : nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v ≤
      ENNReal.ofReal B) : gain (fun p => f p.2) x v ≤ B := by
  have hi := integrable_of_bound hm hf v hb
  have he : gain (fun p => f p.2) x v =
      (nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (f w)) v).toReal := by
    rw [self_eq_lintegral hf]
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (GainOrder.integrand_nonneg hf v)) hi.aestronglyMeasurable
  rw [he]
  simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

end BoltzmannNonuniqueness.GainNonnegative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The relative-speed cutoff used in the finite approximations -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCutoff

theorem rate_nonneg (b : ℝ) (v w : Velocity) : 0 ≤ rate b v w := by
  unfold rate
  split_ifs <;> positivity

theorem kernel_nonneg (b : ℝ) (v w : Velocity) (ω : Sphere) : 0 ≤ kernel b v w ω := by
  unfold kernel
  split_ifs
  · exact collisionKernel_nonneg _ _ _
  · exact le_rfl

theorem kernel_le (b : ℝ) (v w : Velocity) (ω : Sphere) : kernel b v w ω ≤ collisionKernel v w ω := by
  unfold kernel
  split_ifs
  · exact le_rfl
  · exact collisionKernel_nonneg _ _ _

theorem integrable_gain (b : ℝ) {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (hi : Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea)) :
    Integrable (integrand b f v) ((volume : Measure Velocity).prod sphereArea) := by
  have he (p : Velocity × Sphere) : integrand b f v p =
      if ‖v - p.1‖ < b then GainOrder.integrand f v p else 0 := by
    unfold integrand kernel GainOrder.integrand
    split_ifs <;> simp only [zero_mul]
  change Integrable (fun p => integrand b f v p) _
  simp_rw [he]
  apply hi.mono'
  · exact ((GainOrder.integrand_measurable hm v).ite
      (measurableSet_lt (by fun_prop) measurable_const) measurable_const).aestronglyMeasurable
  · filter_upwards [] with p
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (GainOrder.integrand_nonneg hf v p)]
    · simpa only [norm_zero] using GainOrder.integrand_nonneg hf v p

end BoltzmannNonuniqueness.CollisionCutoff

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianEstimates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Centered Gaussians as mixtures of uniform disks

The mixing density in Section 3 is `2 a³ / d⁴ * exp (-a²/d²)` on positive
radii. The formulas below retain the ordinary, unnormalized Lebesgue density
of each disk so that the normalization factors remain explicit.
-/

noncomputable section

open MeasureTheory Set Metric Filter
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransverseAverage
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.GaussianDiskMixture

theorem gaussianDensity_nonneg (d : ℝ) (p : Transverse) : 0 ≤ gaussianDensity d p := by
  unfold gaussianDensity
  positivity

theorem diskDensity_nonneg (a : ℝ) (p : Transverse) : 0 ≤ diskDensity a p := by
  unfold diskDensity
  apply indicator_nonneg _ p
  intro x hx
  positivity

theorem mixingDensity_nonneg (d : ℝ) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ mixingDensity d a := by
  unfold mixingDensity
  positivity

theorem measurable_gaussianDensity (d : ℝ) : Measurable (gaussianDensity d) := by
  unfold gaussianDensity
  fun_prop

theorem measurable_mixingDensity (d : ℝ) : Measurable (mixingDensity d) := by
  unfold mixingDensity
  fun_prop

theorem diskDensity_eq_ite (a : ℝ) (p : Transverse) :
    diskDensity a p = if ‖p‖ < a then (Real.pi * a ^ 2)⁻¹ else 0 := by
  simp [diskDensity, indicator]

theorem measurable_diskDensity : Measurable (fun ap : ℝ × Transverse => diskDensity ap.1 ap.2) := by
  simp only [diskDensity_eq_ite]
  apply Measurable.ite (measurableSet_lt measurable_snd.norm measurable_fst) <;> fun_prop

theorem integrableOn_mixingDensity {d : ℝ} (hd : 0 < d) :
    IntegrableOn (mixingDensity d) (Ioi 0) := by
  have hi := (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / d ^ 2)
    (by positivity) (show (-1 : ℝ) < 3 by norm_num)).const_mul (2 / d ^ 4)
  change Integrable _ _
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  simp only [mixingDensity, Real.rpow_ofNat]
  rw [show -(1 / d ^ 2) * a ^ 2 = -a ^ 2 / d ^ 2 by ring]
  ring

private theorem integral_gaussian_tail {b : ℝ} (hb : 0 < b) (r : ℝ) :
    (∫ a in Ioi r, a * Real.exp (-b * a ^ 2)) =
      (2 * b)⁻¹ * Real.exp (-b * r ^ 2) := by
  have hb₀ : b ≠ 0 := hb.ne'
  have hderiv : ∀ a : ℝ, HasDerivAt
      (fun a => -(2 * b)⁻¹ * Real.exp (-b * a ^ 2))
      (a * Real.exp (-b * a ^ 2)) a := by
    intro a
    convert (((hasDerivAt_pow 2 a).const_mul (-b)).exp.const_mul (-(2 * b)⁻¹)) using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
    ring
  have hi : Integrable (fun a : ℝ => a * Real.exp (-b * a ^ 2)) := by
    simpa only [Real.rpow_one] using
      integrable_rpow_mul_exp_neg_mul_sq hb (show (-1 : ℝ) < 1 by norm_num)
  have ht : Tendsto (fun a : ℝ => -(2 * b)⁻¹ * Real.exp (-b * a ^ 2)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))
    simpa only [mul_zero, Function.comp_def] using h.const_mul (-(2 * b)⁻¹)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := r) (fun a _ => hderiv a) hi.integrableOn ht
  simpa only [zero_sub, neg_mul, neg_neg] using h

theorem integral_radius_tail {d : ℝ} (hd : 0 < d) (r : ℝ) :
    (∫ a in Ioi r, a * Real.exp (-a ^ 2 / d ^ 2)) =
      d ^ 2 / 2 * Real.exp (-r ^ 2 / d ^ 2) := by
  have h := integral_gaussian_tail (b := 1 / d ^ 2) (by positivity) r
  convert h using 1
  · congr 1
    funext a
    congr 2
    ring
  · congr 1 <;> field_simp

private theorem integral_radius_cubic {d : ℝ} (hd : 0 < d) :
    (∫ a in Ioi (0 : ℝ), a ^ 3 * Real.exp (-a ^ 2 / d ^ 2)) = d ^ 4 / 2 := by
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 4)))
    (fun a : ℝ => Real.exp (-(1 / d ^ 2) * a ^ 2))
  have hg := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin 4)) (b := 1 / d ^ 2) (by positivity)
  rw [hg] at h
  rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)] at h
  simp only [ENNReal.ofReal_one, one_pow, one_mul] at h
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  norm_num [finrank_euclideanSpace, Real.rpow_natCast] at h
  have hd₀ : d ≠ 0 := hd.ne'
  have hrewrite : (fun a : ℝ => a ^ 3 * Real.exp (-((d ^ 2)⁻¹ * a ^ 2))) =
      fun a => a ^ 3 * Real.exp (-a ^ 2 / d ^ 2) := by funext a; congr 2; ring
  rw [hrewrite] at h
  field_simp at h
  simp only [neg_div] at ⊢
  linarith

theorem integral_mixingDensity {d : ℝ} (hd : 0 < d) :
    (∫ a in Ioi (0 : ℝ), mixingDensity d a) = 1 := by
  have heq : mixingDensity d = fun a => (2 / d ^ 4) *
      (a ^ 3 * Real.exp (-a ^ 2 / d ^ 2)) := by
    funext a
    unfold mixingDensity
    ring
  rw [heq, integral_const_mul, integral_radius_cubic hd]
  field_simp

private theorem layerCake_integrand {d : ℝ} (hd : 0 < d) (p : Transverse)
    {a : ℝ} (ha : 0 < a) :
    mixingDensity d a * diskDensity a p =
      (Ioi ‖p‖).indicator (fun a => (2 / (Real.pi * d ^ 4)) *
        (a * Real.exp (-a ^ 2 / d ^ 2))) a := by
  have hd₀ : d ≠ 0 := hd.ne'
  have ha₀ : a ≠ 0 := ha.ne'
  by_cases hp : ‖p‖ < a
  · simp only [mixingDensity, diskDensity, indicator_of_mem
      (show p ∈ ball (0 : Transverse) a from mem_ball_zero_iff.mpr hp),
      indicator_of_mem (show a ∈ Ioi ‖p‖ from hp)]
    field_simp
  · simp only [diskDensity, indicator_of_notMem
      (show p ∉ ball (0 : Transverse) a from fun h => hp (mem_ball_zero_iff.mp h)),
      mul_zero, indicator_of_notMem (show a ∉ Ioi ‖p‖ from hp)]

theorem integrableOn_layerCake {d : ℝ} (hd : 0 < d) (p : Transverse) :
    IntegrableOn (fun a => mixingDensity d a * diskDensity a p) (Ioi 0) := by
  have hi : Integrable (fun a : ℝ => a * Real.exp (-a ^ 2 / d ^ 2)) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / d ^ 2)
      (by positivity) (show (-1 : ℝ) < 1 by norm_num)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext a
    rw [Real.rpow_one]
    congr 2
    ring
  have hc := (hi.const_mul (2 / (Real.pi * d ^ 4))).indicator
    (measurableSet_Ioi (a := ‖p‖))
  exact hc.integrableOn.congr_fun (fun a ha => (layerCake_integrand hd p ha).symm)
    measurableSet_Ioi

/-- Pointwise layer-cake identity, with the positive-radius mixing law normalized below. -/
theorem density_layerCake {d : ℝ} (hd : 0 < d) (p : Transverse) :
    (∫ a in Ioi (0 : ℝ), mixingDensity d a * diskDensity a p) = gaussianDensity d p := by
  have hd₀ : d ≠ 0 := hd.ne'
  rw [setIntegral_congr_fun measurableSet_Ioi (fun a ha => layerCake_integrand hd p ha),
    integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_left (norm_nonneg p), integral_const_mul, integral_radius_tail hd]
  unfold gaussianDensity
  field_simp

theorem lintegral_density_layerCake {d : ℝ} (hd : 0 < d) (p : Transverse) :
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (mixingDensity d a * diskDensity a p)) =
      ENNReal.ofReal (gaussianDensity d p) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_layerCake hd p), density_layerCake hd]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  exact mul_nonneg (mixingDensity_nonneg d (le_of_lt ha)) (diskDensity_nonneg a p)

theorem lintegral_mixingDensity {d : ℝ} (hd : 0 < d) :
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (mixingDensity d a)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_mixingDensity hd),
    integral_mixingDensity hd, ENNReal.ofReal_one]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  exact mixingDensity_nonneg d (le_of_lt ha)

private theorem lintegral_diskDensity_mul (φ : Transverse → ℝ≥0∞) (a : ℝ) (ha : 0 < a) :
    (∫⁻ p, ENNReal.ofReal (diskDensity a p) * φ p) =
      (ENNReal.ofReal (Real.pi * a ^ 2))⁻¹ * ∫⁻ p in ball (0 : Transverse) a, φ p := by
  have heq : (fun p => ENNReal.ofReal (diskDensity a p) * φ p) =
      (ball (0 : Transverse) a).indicator
        (fun p => ENNReal.ofReal ((Real.pi * a ^ 2)⁻¹) * φ p) := by
    funext p
    by_cases hp : p ∈ ball (0 : Transverse) a <;> simp [diskDensity, indicator, hp]
  rw [heq, lintegral_indicator measurableSet_ball,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_inv_of_pos (by positivity)]

private theorem measurable_layerCake (d : ℝ) (φ : Transverse → ℝ≥0∞)
    (hφ : Measurable φ) : Measurable (fun pa : Transverse × ℝ =>
      ENNReal.ofReal (mixingDensity d pa.2 * diskDensity pa.2 pa.1) * φ pa.1) := by
  have hs : Measurable (Prod.swap : Transverse × ℝ → ℝ × Transverse) := measurable_swap
  have hdp := measurable_diskDensity.comp hs
  have hm := (measurable_mixingDensity d).comp
    (measurable_snd : Measurable (Prod.snd : Transverse × ℝ → ℝ))
  have hprod := hm.mul hdp
  have hr := hprod.ennreal_ofReal
  have hp := hφ.comp (measurable_fst : Measurable (Prod.fst : Transverse × ℝ → Transverse))
  have h := hr.mul hp
  simpa only [Function.comp_def, Pi.mul_def, Prod.fst_swap, Prod.snd_swap] using h

private theorem lintegral_layerCake_mul {d : ℝ} (hd : 0 < d)
    (φ : Transverse → ℝ≥0∞) (p : Transverse) :
    (∫⁻ a in Ioi (0 : ℝ),
      ENNReal.ofReal (mixingDensity d a * diskDensity a p) * φ p) =
      ENNReal.ofReal (gaussianDensity d p) * φ p := by
  have hm : Measurable (fun a => ENNReal.ofReal (mixingDensity d a * diskDensity a p)) :=
    ((measurable_mixingDensity d).mul
      (measurable_diskDensity.comp (measurable_id.prodMk measurable_const))).ennreal_ofReal
  rw [lintegral_mul_const _ hm, lintegral_density_layerCake hd]

private theorem lintegral_layerCake_disk {d a : ℝ} (φ : Transverse → ℝ≥0∞)
    (ha : 0 < a) :
    (∫⁻ p, ENNReal.ofReal (mixingDensity d a * diskDensity a p) * φ p) =
      ENNReal.ofReal (mixingDensity d a) *
        ((ENNReal.ofReal (Real.pi * a ^ 2))⁻¹ * ∫⁻ p in ball (0 : Transverse) a, φ p) := by
  simp_rw [ENNReal.ofReal_mul (mixingDensity_nonneg d ha.le), mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_diskDensity_mul φ a ha]

/-- Tonelli's theorem expresses every nonnegative measurable Gaussian expectation
as a probability mixture of normalized disk expectations. -/
theorem lintegral_gaussian_mixture {d : ℝ} (hd : 0 < d)
    (φ : Transverse → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ p, ENNReal.ofReal (gaussianDensity d p) * φ p) =
      ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (mixingDensity d a) *
        ((ENNReal.ofReal (Real.pi * a ^ 2))⁻¹ * ∫⁻ p in ball (0 : Transverse) a, φ p) := by
  calc
    _ = ∫⁻ p, ∫⁻ a in Ioi (0 : ℝ),
        ENNReal.ofReal (mixingDensity d a * diskDensity a p) * φ p :=
      lintegral_congr (fun p => (lintegral_layerCake_mul hd φ p).symm)
    _ = ∫⁻ a in Ioi (0 : ℝ), ∫⁻ p,
        ENNReal.ofReal (mixingDensity d a * diskDensity a p) * φ p :=
      lintegral_lintegral_swap (measurable_layerCake d φ hφ).aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      exact lintegral_layerCake_disk φ ha

theorem integrable_diskDensity {a : ℝ} (_ha : 0 < a) : Integrable (diskDensity a) := by
  apply (integrableOn_const measure_ball_lt_top.ne).integrable_indicator measurableSet_ball

theorem integral_diskDensity {a : ℝ} (ha : 0 < a) : (∫ p, diskDensity a p) = 1 := by
  unfold diskDensity
  rw [integral_indicator measurableSet_ball, setIntegral_const, smul_eq_mul,
    TransverseDisk.disk_volume_real 0 ha.le]
  field_simp

theorem lintegral_diskDensity {a : ℝ} (ha : 0 < a) :
    (∫⁻ p, ENNReal.ofReal (diskDensity a p)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_diskDensity ha)
    (ae_of_all _ (diskDensity_nonneg a)), integral_diskDensity ha, ENNReal.ofReal_one]

theorem lintegral_gaussianDensity {d : ℝ} (hd : 0 < d) :
    (∫⁻ p, ENNReal.ofReal (gaussianDensity d p)) = 1 := by
  have h := lintegral_gaussian_mixture hd (fun _ => 1) measurable_const
  simp only [mul_one] at h
  rw [h]
  calc
    _ = ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (mixingDensity d a) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      have hn := lintegral_diskDensity_mul (fun _ => 1) a ha
      simp only [mul_one] at hn
      rw [← hn, lintegral_diskDensity ha, mul_one]
    _ = 1 := lintegral_mixingDensity hd

theorem gaussianLaw_isProbabilityMeasure {d : ℝ} (hd : 0 < d) :
    IsProbabilityMeasure (gaussianLaw d) := by
  constructor
  rw [gaussianLaw, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    lintegral_gaussianDensity hd]

theorem gaussian_kernel_lintegral_le {q d : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d)
    {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, ENNReal.ofReal (gaussianDensity d p) *
      ENNReal.ofReal (kernel q (direction v) (v - p))) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  have hm : Measurable (fun p => kernel q (direction v) (v - p)) := by
    unfold kernel
    fun_prop
  rw [lintegral_gaussian_mixture hd _ hm.ennreal_ofReal]
  calc
    _ ≤ ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (mixingDensity d a) *
        ENNReal.ofReal (expectationConstant q / ‖v‖) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
      have ha₀ : 0 < a := ha
      apply mul_le_mul_right
      have hi := integrableOn_kernel_translatedDisk hq₂ ha₀ (direction v) (norm_direction hv) v
      have heq : (∫⁻ p in ball (0 : Transverse) a,
          ENNReal.ofReal (kernel q (direction v) (v - p))) =
          ENNReal.ofReal (∫ p in ball (0 : Transverse) a, kernel q (direction v) (v - p)) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hi
          (ae_of_all _ (fun p => kernel_nonneg q (direction v) (v - p)))
      rw [heq]
      have hnorm : (ENNReal.ofReal (Real.pi * a ^ 2))⁻¹ *
          ENNReal.ofReal (∫ p in ball (0 : Transverse) a, kernel q (direction v) (v - p)) =
          ENNReal.ofReal ((∫ p in ball (0 : Transverse) a, kernel q (direction v) (v - p)) /
            (Real.pi * a ^ 2)) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), div_eq_mul_inv, mul_comm]
      rw [hnorm]
      exact ENNReal.ofReal_le_ofReal (uniformDisk_expectation_le hq₁ hq₂ ha₀ hv)
    _ = _ := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_mixingDensity hd, one_mul]

theorem gaussianLaw_kernel_lintegral_le {q d : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d) {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, ENNReal.ofReal (kernel q (direction v) (v - p)) ∂gaussianLaw d) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  have hm : Measurable (fun p => ENNReal.ofReal (kernel q (direction v) (v - p))) := by
    unfold kernel
    fun_prop
  rw [gaussianLaw, lintegral_withDensity_eq_lintegral_mul volume
    (measurable_gaussianDensity d).ennreal_ofReal hm]
  exact gaussian_kernel_lintegral_le hq₁ hq₂ hd hv

end BoltzmannNonuniqueness.GaussianDiskMixture

end

end

section

/-!
# Gaussian parameter laws for compressed sheets

The probability and exponential-moment assertions in `ker:parameter-sheets`
use only measurable axial maps. Both the original axial Gaussian (variance
`1 / 2`) and the widened Gaussian (variance `1`) satisfy the bounds below.
The collision gain estimate is not assumed or asserted here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace BoltzmannNonuniqueness.GaussianSheets

theorem original_gaussian_density (a : ℝ) :
    gaussianPDFReal 0 (1 / 2) a = (Real.sqrt Real.pi)⁻¹ * Real.exp (-a ^ 2) := by
  unfold gaussianPDFReal
  norm_num
  have h₂ : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp

private theorem integrable_gaussianReal_iff {v : ℝ≥0} (hv : v ≠ 0) (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 v) ↔
      Integrable (fun a => gaussianPDFReal 0 v a * f a) := by
  rw [gaussianReal_of_var_ne_zero 0 hv,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 v)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v _),
    smul_eq_mul]

/-- A quadratic exponential changes the centered Gaussian variance by a factor of two. -/
theorem gaussianPDF_mul_exp_quarter {v : ℝ≥0} (hv : v ≠ 0) (a : ℝ) :
    gaussianPDFReal 0 v a * Real.exp (a ^ 2 / (4 * (v : ℝ))) =
      Real.sqrt 2 * gaussianPDFReal 0 (2 * v) a := by
  have hv₀ : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hv
  have hs : Real.sqrt (2 * Real.pi * (2 * (v : ℝ))) =
      Real.sqrt 2 * Real.sqrt (2 * Real.pi * (v : ℝ)) := by
    rw [show 2 * Real.pi * (2 * (v : ℝ)) = 2 * (2 * Real.pi * (v : ℝ)) by ring,
      Real.sqrt_mul (by norm_num)]
  have he : -a ^ 2 / (2 * (v : ℝ)) + a ^ 2 / (4 * (v : ℝ)) =
      -a ^ 2 / (2 * (2 * (v : ℝ))) := by field_simp <;> ring
  unfold gaussianPDFReal
  simp only [sub_zero, NNReal.coe_mul, NNReal.coe_ofNat]
  rw [mul_assoc, ← Real.exp_add, he, hs]
  have hs₀ : Real.sqrt (2 * Real.pi * (v : ℝ)) ≠ 0 := by positivity
  have h₂ : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  field_simp

theorem integrable_exp_quarter_gaussian {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun a : ℝ => Real.exp (a ^ 2 / (4 * (v : ℝ)))) (gaussianReal 0 v) := by
  apply (integrable_gaussianReal_iff hv _).mpr
  have hi := (integrable_gaussianPDFReal 0 (2 * v)).const_mul (Real.sqrt 2)
  exact hi.congr (ae_of_all _ (fun a => (gaussianPDF_mul_exp_quarter hv a).symm))

theorem integral_exp_quarter_gaussian {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ a : ℝ, Real.exp (a ^ 2 / (4 * (v : ℝ))) ∂gaussianReal 0 v) = Real.sqrt 2 := by
  have h₂v : (2 : ℝ≥0) * v ≠ 0 := mul_ne_zero (by norm_num) hv
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul, gaussianPDF_mul_exp_quarter hv, integral_const_mul,
    integral_gaussianPDFReal_eq_one 0 h₂v, mul_one]

private theorem exp_image_le {v : ℝ≥0} (hv : v ≠ 0) (hv₁ : v ≤ 1)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 16)
    {Φ : ℝ → ℝ} (hΦ : ∀ a, |Φ a| ≤ A + δ * |a|) (a : ℝ) :
    Real.exp (8 * (Φ a) ^ 2) ≤
      Real.exp (16 * A ^ 2) * Real.exp (a ^ 2 / (4 * (v : ℝ))) := by
  have hvpos : 0 < (v : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hv
  have hvle : (v : ℝ) ≤ 1 := by exact_mod_cast hv₁
  have hsq : (Φ a) ^ 2 ≤ (A + δ * |a|) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Φ a)) (by positivity)).mpr (hΦ a)
  have hδsq : 16 * δ ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ₁)]
  have hsplit : 8 * (Φ a) ^ 2 ≤ 16 * A ^ 2 + a ^ 2 / 4 := by
    have hmul := mul_le_mul_of_nonneg_right hδsq (sq_nonneg a)
    nlinarith [sq_nonneg (A - δ * |a|), sq_abs a]
  have hdiv : a ^ 2 / 4 ≤ a ^ 2 / (4 * (v : ℝ)) := by
    apply div_le_div_of_nonneg_left (sq_nonneg a) (by positivity)
    linarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- The Gaussian parameter integrand is genuinely integrable, before taking its image law. -/
theorem integrable_exp_image {v : ℝ≥0} (hv : v ≠ 0) (hv₁ : v ≤ 1)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 16)
    {Φ : ℝ → ℝ} (hΦm : Measurable Φ) (hΦ : ∀ a, |Φ a| ≤ A + δ * |a|) :
    Integrable (fun a => Real.exp (8 * (Φ a) ^ 2)) (gaussianReal 0 v) := by
  apply ((integrable_exp_quarter_gaussian hv).const_mul (Real.exp (16 * A ^ 2))).mono'
  · exact (by fun_prop : Measurable (fun a => Real.exp (8 * (Φ a) ^ 2))).aestronglyMeasurable
  · filter_upwards [] with a
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_image_le hv hv₁ hA hδ hδ₁ hΦ a

/-- The constant `2 * exp (16 * A²)` works for the original and wider parameter laws. -/
theorem integral_exp_image_le {v : ℝ≥0} (hv : v ≠ 0) (hv₁ : v ≤ 1)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 16)
    {Φ : ℝ → ℝ} (hΦm : Measurable Φ) (hΦ : ∀ a, |Φ a| ≤ A + δ * |a|) :
    (∫ a, Real.exp (8 * (Φ a) ^ 2) ∂gaussianReal 0 v) ≤ 2 * Real.exp (16 * A ^ 2) := by
  calc
    _ ≤ ∫ a, Real.exp (16 * A ^ 2) * Real.exp (a ^ 2 / (4 * (v : ℝ)))
        ∂gaussianReal 0 v :=
      integral_mono (integrable_exp_image hv hv₁ hA hδ hδ₁ hΦm hΦ)
        ((integrable_exp_quarter_gaussian hv).const_mul _) (exp_image_le hv hv₁ hA hδ hδ₁ hΦ)
    _ = Real.exp (16 * A ^ 2) * Real.sqrt 2 := by
      rw [integral_const_mul, integral_exp_quarter_gaussian hv]
    _ ≤ _ := by
      have hs : Real.sqrt (2 : ℝ) ≤ 2 := by
        apply Real.sqrt_le_iff.mpr
        norm_num
      nlinarith [Real.exp_pos (16 * A ^ 2)]

theorem integrable_axialLaw_exp {v : ℝ≥0} (hv : v ≠ 0) (hv₁ : v ≤ 1)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 16)
    {Φ : ℝ → ℝ} (hΦm : Measurable Φ) (hΦ : ∀ a, |Φ a| ≤ A + δ * |a|) :
    Integrable (fun a : ℝ => Real.exp (8 * a ^ 2)) (axialLaw v Φ) := by
  rw [axialLaw, if_pos hΦm.aemeasurable]
  apply (integrable_map_measure (by fun_prop) hΦm.aemeasurable).mpr
  exact integrable_exp_image hv hv₁ hA hδ hδ₁ hΦm hΦ

theorem integral_axialLaw_exp_le {v : ℝ≥0} (hv : v ≠ 0) (hv₁ : v ≤ 1)
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 16)
    {Φ : ℝ → ℝ} (hΦm : Measurable Φ) (hΦ : ∀ a, |Φ a| ≤ A + δ * |a|) :
    (∫ a : ℝ, Real.exp (8 * a ^ 2) ∂axialLaw v Φ) ≤ 2 * Real.exp (16 * A ^ 2) := by
  rw [axialLaw, if_pos hΦm.aemeasurable, integral_map hΦm.aemeasurable (by fun_prop)]
  exact integral_exp_image_le hv hv₁ hA hδ hδ₁ hΦm hΦ

end BoltzmannNonuniqueness.GaussianSheets

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_ScalarEntropyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The scalar power singularity in an axial slice

The exponent `r = 1-q` lies between `-1` and `0`. The interval estimate
below is uniform in the location of its singularity. Values at the
single singular point use the real-power convention and are immaterial.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.AxialSlices

theorem intervalIntegrable_abs_rpow {r : ℝ} (hr : -1 < r) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x| ^ r) volume a b := by
  have hl : LocallyIntegrable (fun x : ℝ => |x| ^ r) := by
    apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := -r)
      (by simp) (by norm_num only [Module.finrank_self, Nat.cast_one] <;> linarith)
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      simp only [one_mul, neg_neg, Real.norm_eq_abs, le_refl]
    · exact (measurable_abs.pow measurable_const).aestronglyMeasurable
  exact (intervalIntegrable_iff').mpr (hl.integrableOn_isCompact isCompact_uIcc)

theorem intervalIntegrable_abs_sub_rpow {r : ℝ} (hr : -1 < r) (t a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x - t| ^ r) volume a b := by
  simpa using (intervalIntegrable_abs_rpow hr (a - t) (b - t)).comp_sub_right t

theorem integral_abs_rpow_zero {r L : ℝ} (hr : -1 < r) (hL : 0 ≤ L) :
    (∫ x : ℝ in 0..L, |x| ^ r) = L ^ (r + 1) / (r + 1) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le hL (fun x hx => by
    rw [abs_of_pos hx.1])]
  rw [integral_rpow (Or.inl hr), Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero]

theorem integral_abs_rpow_symmetric {r L : ℝ} (hr : -1 < r) (hL : 0 ≤ L) :
    (∫ x : ℝ in -L..L, |x| ^ r) = 2 * L ^ (r + 1) / (r + 1) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_abs_rpow hr (-L) 0) (intervalIntegrable_abs_rpow hr 0 L)]
  have hn : (∫ x : ℝ in -L..0, |x| ^ r) = ∫ x : ℝ in 0..L, |x| ^ r := by
    have h := intervalIntegral.integral_comp_neg (fun x : ℝ => |x| ^ r) (a := 0) (b := L)
    simp only [abs_neg, neg_zero] at h
    exact h.symm
  rw [hn, integral_abs_rpow_zero hr hL]
  ring

/-- A power singularity has at most twice the endpoint mass on an interval of length `b-a`.
This is the root-independent estimate in the large-slope case of `ker:scalar-interval`. -/
theorem integral_abs_sub_rpow_le {r a b t : ℝ} (hr : -1 < r) (hr₀ : r ≤ 0)
    (hab : a ≤ b) :
    (∫ x : ℝ in a..b, |x - t| ^ r) ≤ 2 * (b - a) ^ (r + 1) / (r + 1) := by
  have hr₁ : 0 < r + 1 := by linarith
  have hp : 0 ≤ (b - a) ^ (r + 1) / (r + 1) := by positivity
  rw [show 2 * (b - a) ^ (r + 1) / (r + 1) =
    2 * ((b - a) ^ (r + 1) / (r + 1)) by ring]
  by_cases hta : t ≤ a
  · have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hab
      (intervalIntegrable_abs_sub_rpow hr t a b)
      (intervalIntegrable_abs_sub_rpow hr a a b)
      (fun x hx => by
        apply Real.rpow_le_rpow_of_nonpos
        · rw [abs_of_pos (sub_pos.mpr hx.1)]; exact sub_pos.mpr hx.1
        · rw [abs_of_pos (sub_pos.mpr hx.1), abs_of_nonneg (by linarith [hx.1])]
          linarith
        · exact hr₀)
    have he : (∫ x : ℝ in a..b, |x - a| ^ r) =
        (b - a) ^ (r + 1) / (r + 1) := by
      rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => |x| ^ r)]
      simpa using integral_abs_rpow_zero hr (sub_nonneg.mpr hab)
    rw [he] at hmono
    linarith
  by_cases hbt : b ≤ t
  · have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hab
      (intervalIntegrable_abs_sub_rpow hr t a b)
      (intervalIntegrable_abs_sub_rpow hr b a b)
      (fun x hx => by
        apply Real.rpow_le_rpow_of_nonpos
        · rw [abs_of_neg (sub_neg.mpr hx.2)]; linarith [hx.2]
        · rw [abs_of_neg (sub_neg.mpr hx.2), abs_of_nonpos (by linarith [hx.2])]
          linarith
        · exact hr₀)
    have he : (∫ x : ℝ in a..b, |x - b| ^ r) =
        (b - a) ^ (r + 1) / (r + 1) := by
      calc
        _ = ∫ x : ℝ in a..b, |b - x| ^ r := by
          apply intervalIntegral.integral_congr
          intro x _
          exact congrArg (fun y : ℝ => y ^ r) (abs_sub_comm x b)
        _ = _ := by
          rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => |x| ^ r), sub_self]
          exact integral_abs_rpow_zero hr (sub_nonneg.mpr hab)
    rw [he] at hmono
    linarith
  · have hta' : a ≤ t := le_of_not_ge hta
    have htb' : t ≤ b := le_of_not_ge hbt
    have hmono := intervalIntegral.integral_mono_interval
      (show t - (b - a) ≤ a by linarith) hab
      (show b ≤ t + (b - a) by linarith)
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (abs_nonneg (x - t)) r))
      (intervalIntegrable_abs_sub_rpow hr t (t - (b - a)) (t + (b - a)))
    calc
      _ ≤ ∫ x : ℝ in t - (b - a)..t + (b - a), |x - t| ^ r := hmono
      _ = 2 * ((b - a) ^ (r + 1) / (r + 1)) := by
        rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => |x| ^ r)]
        rw [show t - (b - a) - t = -(b - a) by ring,
          show t + (b - a) - t = b - a by ring,
          integral_abs_rpow_symmetric hr (sub_nonneg.mpr hab)]
        ring

theorem abs_affine_rpow (r A B x : ℝ) (hB : B ≠ 0) :
    |A - B * x| ^ r = |B| ^ r * |x - A / B| ^ r := by
  have he : A - B * x = -B * (x - A / B) := by field_simp <;> ring
  rw [he, abs_mul, abs_neg, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]

theorem intervalIntegrable_abs_affine_rpow {r : ℝ} (hr : -1 < r) (A B a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => |A - B * x| ^ r) volume a b := by
  by_cases hB : B = 0
  · simp only [hB, zero_mul, sub_zero]
    exact intervalIntegrable_const
  · have hi := (intervalIntegrable_abs_sub_rpow hr (A / B) a b).const_mul (|B| ^ r)
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact abs_affine_rpow r A B x hB

/-- Large-slope estimate obtained by rescaling the root-independent interval bound. -/
theorem integral_abs_affine_rpow_le {r a b A B : ℝ} (hr : -1 < r) (hr₀ : r ≤ 0)
    (hab : a ≤ b) (hB : B ≠ 0) :
    (∫ x : ℝ in a..b, |A - B * x| ^ r) ≤
      |B| ^ r * (2 * (b - a) ^ (r + 1) / (r + 1)) := by
  simp_rw [abs_affine_rpow r A B _ hB]
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_abs_sub_rpow_le hr hr₀ hab)
    (Real.rpow_nonneg (abs_nonneg B) r)

/-- If the slope is small, the affine function stays a fixed distance from zero. -/
theorem small_slope_distance {A B R x : ℝ} (_hR : 0 ≤ R)
    (hAB : 2 * R * |B| ≤ |A|) (hx : |x| ≤ R) :
    |A| / 2 ≤ |A - B * x| := by
  have hmul : |B * x| ≤ |B| * R := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg B)
  have htri := abs_add_le (A - B * x) (B * x)
  rw [sub_add_cancel] at htri
  nlinarith

/-- The small-slope half of the scalar estimate, before combining the powers of the length. -/
theorem integral_abs_affine_rpow_le_small_slope {r a b A B R : ℝ}
    (hr : -1 < r) (hr₀ : r ≤ 0) (hab : a ≤ b)
    (hR : 0 ≤ R) (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0)
    (hAB : 2 * R * |B| ≤ |A|) :
    (∫ x : ℝ in a..b, |A - B * x| ^ r) ≤ (b - a) * (|A| / 2) ^ r := by
  have h := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_abs_affine_rpow hr A B a b)
    (intervalIntegrable_const (c := (|A| / 2) ^ r))
    (fun x hx => Real.rpow_le_rpow_of_nonpos (by positivity : 0 < |A| / 2)
      (small_slope_distance hR hAB (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)) hr₀)
  simpa using h

theorem scalarConstant_pos {r : ℝ} (hr : -1 < r) : 0 < scalarConstant r := by
  have hr₁ : 0 < r + 1 := by linarith
  unfold scalarConstant
  positivity

private theorem length_le_scaled_power {r l R : ℝ} (hr : r ≤ 0)
    (hl : 0 < l) (hlR : l ≤ 2 * R) :
    l ≤ (2 * R) ^ (-r) * l ^ (r + 1) := by
  have hp := Real.rpow_le_rpow hl.le hlR (neg_nonneg.mpr hr)
  calc
    l = l ^ (r + 1) * l ^ (-r) := by
      rw [← Real.rpow_add hl, show (r + 1) + -r = 1 by ring, Real.rpow_one]
    _ ≤ l ^ (r + 1) * (2 * R) ^ (-r) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hl.le _)
    _ = _ := mul_comm _ _

/-- The scalar interval estimate `ker:scalar-interval`, with an explicit constant.
The singular case `A=0` is understood in the extended sense in the manuscript;
the finite estimate needed off the exceptional line is stated here. -/
theorem integral_abs_affine_rpow_scalar_bound {r a b A B R : ℝ}
    (hr : -1 < r) (hr₀ : r ≤ 0) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0) :
    (∫ x : ℝ in a..b, |A - B * x| ^ r) ≤
      scalarConstant r * (R ^ (-r) * (b - a) ^ (r + 1) * |A| ^ r) := by
  have hr₁ : 0 < r + 1 := by linarith
  have hA₀ : 0 < |A| := abs_pos.mpr hA
  have hl : 0 < b - a := sub_pos.mpr hab
  have hlR : b - a ≤ 2 * R := by linarith
  have hn : 0 ≤ R ^ (-r) * (b - a) ^ (r + 1) * |A| ^ r := by positivity
  have htwo : 0 ≤ (2 : ℝ) ^ (-r) := Real.rpow_nonneg (by norm_num) _
  have hc₁ : (2 : ℝ) ^ (-r) * (2 : ℝ) ^ (-r) ≤ scalarConstant r := by
    unfold scalarConstant
    have hdiv : 0 ≤ 2 / (r + 1) := by positivity
    nlinarith
  have hc₂ : (2 : ℝ) ^ (-r) * (2 / (r + 1)) ≤ scalarConstant r := by
    unfold scalarConstant
    nlinarith
  by_cases hsmall : 2 * R * |B| ≤ |A|
  · calc
      _ ≤ (b - a) * (|A| / 2) ^ r :=
        integral_abs_affine_rpow_le_small_slope hr hr₀ hab.le hR.le ha hb hA hsmall
      _ ≤ ((2 * R) ^ (-r) * (b - a) ^ (r + 1)) * (|A| / 2) ^ r :=
        mul_le_mul_of_nonneg_right (length_le_scaled_power hr₀ hl hlR)
          (Real.rpow_nonneg (by positivity) _)
      _ = ((2 : ℝ) ^ (-r) * (2 : ℝ) ^ (-r)) *
          (R ^ (-r) * (b - a) ^ (r + 1) * |A| ^ r) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR.le,
          Real.div_rpow hA₀.le (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc₁ hn
  · have hlarge : |A| < 2 * R * |B| := lt_of_not_ge hsmall
    have hB : B ≠ 0 := by
      intro hzero
      simp only [hzero, abs_zero, mul_zero] at hlarge
      linarith
    have hdiv : |A| / (2 * R) ≤ |B| :=
      ((div_lt_iff₀ (by positivity : 0 < 2 * R)).mpr (by nlinarith)).le
    have hp := Real.rpow_le_rpow_of_nonpos
      (by positivity : 0 < |A| / (2 * R)) hdiv hr₀
    calc
      _ ≤ |B| ^ r * (2 * (b - a) ^ (r + 1) / (r + 1)) :=
        integral_abs_affine_rpow_le hr hr₀ hab.le hB
      _ ≤ (|A| / (2 * R)) ^ r * (2 * (b - a) ^ (r + 1) / (r + 1)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = ((2 : ℝ) ^ (-r) * (2 / (r + 1))) *
          (R ^ (-r) * (b - a) ^ (r + 1) * |A| ^ r) := by
        rw [Real.div_rpow hA₀.le (by positivity : 0 ≤ 2 * R),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR.le]
        rw [div_eq_mul_inv, mul_inv_rev,
          ← Real.rpow_neg hR.le, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hc₂ hn

/-- The manuscript's scalar slice estimate in its `q` notation. -/
theorem scalar_interval_bound {q a b A B R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0) :
    (∫ x : ℝ in a..b, |A - B * x| ^ (1 - q)) ≤
      scalarConstant (1 - q) * (R ^ (q - 1) * (b - a) ^ (2 - q) * |A| ^ (1 - q)) := by
  have h := integral_abs_affine_rpow_scalar_bound (r := 1 - q) (B := B)
    (by linarith) (by linarith) hab hR ha hb hA
  simpa only [show -(1 - q) = q - 1 by ring, show (1 - q) + 1 = 2 - q by ring] using h

end BoltzmannNonuniqueness.AxialSlices

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricSlice
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Degenerate slices and nonnegative singular integrals

The line integral through the velocity axis is infinite. Its exceptional transverse
parameters form an affine line of two-dimensional measure zero. These results keep
that extended value explicit and justify the almost-everywhere scalar estimates,
including products with arbitrary axial probability measures.
-/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GaussianDiskMixture
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness.GeometricSlice

theorem sliceOffset_eq_zero_iff (v p : Transverse) :
    sliceOffset v p = 0 ↔ inner ℝ v p = ‖v‖ ^ 2 := by
  by_cases hn : v - p = 0
  · have hp : p = v := (sub_eq_zero.mp hn).symm
    subst p
    simp [sliceOffset, direction]
  · have hnorm : ‖v - p‖ ≠ 0 := norm_ne_zero_iff.mpr hn
    rw [sliceOffset, direction, real_inner_smul_left, mul_eq_zero]
    simp only [inv_eq_zero, hnorm, false_or]
    rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm p v]
    constructor <;> intro h <;> linarith

theorem regularTransverse_iff (v p : Transverse) :
    RegularTransverse v p ↔ inner ℝ v p ≠ ‖v‖ ^ 2 := by
  constructor
  · intro h
    exact mt (sliceOffset_eq_zero_iff v p).mpr h.2
  · intro h
    have hs : sliceOffset v p ≠ 0 := mt (sliceOffset_eq_zero_iff v p).mp h
    refine ⟨?_, hs⟩
    intro hn
    apply hs
    simp [sliceOffset, direction, hn]

theorem measurableSet_regularTransverse (v : Transverse) :
    MeasurableSet {p | RegularTransverse v p} := by
  simp_rw [regularTransverse_iff]
  exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl

/-- The bad transverse parameters lie in a proper affine hyperplane. -/
theorem volume_sliceOffset_zero {v : Transverse} (hv : v ≠ 0) :
    volume {p | sliceOffset v p = 0} = 0 := by
  let K : Submodule ℝ Transverse := (innerSL ℝ v).ker
  let S : AffineSubspace ℝ Transverse := AffineSubspace.mk' v K
  have hset : {p | sliceOffset v p = 0} = (S : Set Transverse) := by
    ext p
    rw [mem_ofPred_eq, sliceOffset_eq_zero_iff]
    change inner ℝ v p = ‖v‖ ^ 2 ↔ inner ℝ v (p - v) = 0
    rw [inner_sub_right, real_inner_self_eq_norm_sq, sub_eq_zero]
  have hproper : S ≠ ⊤ := by
    intro hs
    have hm : (0 : Transverse) ∈ S := by rw [hs]; trivial
    change inner ℝ v (0 - v) = 0 at hm
    simp only [zero_sub, inner_neg_right, neg_eq_zero, real_inner_self_eq_norm_sq,
      sq_eq_zero_iff, norm_eq_zero] at hm
    exact hv hm
  rw [hset]
  exact Measure.addHaar_affineSubspace volume S hproper

theorem ae_regularTransverse_volume {v : Transverse} (hv : v ≠ 0) :
    ∀ᵐ p ∂volume, RegularTransverse v p := by
  have hs : ∀ᵐ p ∂volume, sliceOffset v p ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using volume_sliceOffset_zero hv
  filter_upwards [hs] with p hp
  refine ⟨?_, hp⟩
  intro hn
  apply hp
  simp [sliceOffset, direction, hn]

theorem regularTransverse_zero {v : Transverse} (hv : v ≠ 0) :
    RegularTransverse v 0 := by
  rw [regularTransverse_iff, inner_zero_right]
  exact Ne.symm (ne_of_gt (pow_pos (norm_pos_iff.mpr hv) 2))

theorem ae_regularTransverse_atom {v : Transverse} (hv : v ≠ 0) :
    ∀ᵐ p ∂Measure.dirac (0 : Transverse), RegularTransverse v p := by
  rw [ae_dirac_eq]
  exact regularTransverse_zero hv

theorem ae_regularTransverse_gaussian {v : Transverse} (hv : v ≠ 0) (d : ℝ) :
    ∀ᵐ p ∂gaussianLaw d, RegularTransverse v p :=
  (withDensity_absolutelyContinuous volume _).ae_le (ae_regularTransverse_volume hv)

/-- No regularity of the axial law is needed to preserve the exceptional null set. -/
theorem ae_regularTransverse_prod {v : Transverse} {μ : Measure Transverse}
    {ρ : Measure ℝ} [SFinite ρ] (hμ : ∀ᵐ p ∂μ, RegularTransverse v p) :
    ∀ᵐ p ∂μ.prod ρ, RegularTransverse v p.1 := by
  apply (Measure.ae_prod_iff_ae_ae ((measurableSet_regularTransverse v).preimage measurable_fst)).mpr
  filter_upwards [hμ] with p hp
  exact ae_of_all _ (fun _ => hp)

theorem extendedPower_ae_eq {A : ℝ} (hA : A ≠ 0) (B q : ℝ) :
    (fun x : ℝ => extendedPower q (A - B * x)) =ᵐ[volume]
      (fun x => ENNReal.ofReal (|A - B * x| ^ (1 - q))) := by
  by_cases hB : B = 0
  · exact ae_of_all _ (fun x => by simp [extendedPower, hB, hA])
  · have hz : ∀ᵐ x ∂volume, x ≠ A / B := volume.ae_ne (A / B)
    filter_upwards [hz] with x hx
    have hAx : A - B * x ≠ 0 := by
      intro heq
      apply hx
      apply (eq_div_iff hB).mpr
      nlinarith [sub_eq_zero.mp heq]
    simp only [extendedPower, hAx, ↓reduceIte]

/-- The extended-valued scalar integral has the same finite bound as the ordinary
integral whenever the nonzero intercept excludes an identically singular slice. -/
theorem lintegral_extendedPower_interval_le {q a b A B R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0) :
    (∫⁻ x in Ioc a b, extendedPower q (A - B * x)) ≤
      ENNReal.ofReal (AxialSlices.scalarConstant (1 - q) *
        (R ^ (q - 1) * (b - a) ^ (2 - q) * |A| ^ (1 - q))) := by
  have hi := AxialSlices.intervalIntegrable_abs_affine_rpow
    (show -1 < 1 - q by linarith) A B a b
  rw [lintegral_congr_ae (ae_restrict_of_ae (extendedPower_ae_eq hA B q))]
  rw [← ofReal_integral_eq_lintegral_ofReal hi.1
    (ae_of_all _ (fun x => Real.rpow_nonneg (abs_nonneg _) _))]
  rw [← intervalIntegral.integral_of_le hab.le]
  exact ENNReal.ofReal_le_ofReal (AxialSlices.scalar_interval_bound hq₁ hq₂ hab hR ha hb hA)

theorem measurable_extendedKernel (q : ℝ) (v : Transverse) :
    Measurable (extendedKernel q v) := by
  classical
  unfold extendedKernel
  apply Measurable.ite (measurableSet_regularTransverse v) _ measurable_const
  unfold kernel
  fun_prop

theorem extendedKernel_ae_eq {v : Transverse} {μ : Measure Transverse}
    (hμ : ∀ᵐ p ∂μ, RegularTransverse v p) (q : ℝ) :
    extendedKernel q v =ᵐ[μ] fun p => ENNReal.ofReal (kernel q (direction v) (v - p)) := by
  filter_upwards [hμ] with p hp
  simp only [extendedKernel, hp, ↓reduceIte]

theorem atom_extendedKernel_lintegral_le (q : ℝ) {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, extendedKernel q v p ∂Measure.dirac (0 : Transverse)) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  rw [lintegral_congr_ae (extendedKernel_ae_eq (ae_regularTransverse_atom hv) q),
    lintegral_dirac]
  simpa only [integral_dirac, sub_zero] using ENNReal.ofReal_le_ofReal (atomZero_expectation_le q hv)

theorem gaussian_extendedKernel_lintegral_le {q d : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d) {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, extendedKernel q v p ∂gaussianLaw d) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  rw [lintegral_congr_ae (extendedKernel_ae_eq (ae_regularTransverse_gaussian hv d) q)]
  exact gaussianLaw_kernel_lintegral_le hq₁ hq₂ hd hv

/-- The line estimate with its correct extended value at zero distance. -/
theorem lintegral_lineWeight_le_extended {q R : ℝ} (hq : 1 < q) (hR : 0 ≤ R)
    (e : Transverse) (he : ‖e‖ = 1) (D m : ℝ) :
    (∫⁻ s in Icc (m - R) (m + R),
      ENNReal.ofReal (TransverseLine.lineWeight q e D s)) ≤
      ENNReal.ofReal (2 * R) + ENNReal.ofReal (AxialSlices.lineConstant q) * extendedPower q D := by
  have hc := AxialSlices.lineConstant_pos hq
  by_cases hD : D = 0
  · rw [extendedPower, ite_eq_left hD, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hc)),
      add_top]
    exact le_top
  · rw [extendedPower, ite_eq_right hD, ← ENNReal.ofReal_mul hc.le,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact TransverseLine.lintegral_lineWeight_le hq hD hR e he m

theorem rectangleLineMass_le {q a b A B R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0)
    (e : Transverse) (he : ‖e‖ = 1) (m : ℝ) :
    rectangleLineMass q e A B m R a b ≤
      ENNReal.ofReal (2 * R * (b - a) + AxialSlices.lineConstant q *
        (AxialSlices.scalarConstant (1 - q) *
          (R ^ (q - 1) * (b - a) ^ (2 - q) * |A| ^ (1 - q)))) := by
  have hc := (AxialSlices.lineConstant_pos hq₁).le
  have hs := lintegral_extendedPower_interval_le hq₁ hq₂ hab hR ha hb hA (B := B)
  unfold rectangleLineMass
  calc
    _ ≤ ∫⁻ z in Ioc a b, ENNReal.ofReal (2 * R) +
        ENNReal.ofReal (AxialSlices.lineConstant q) * extendedPower q (A - B * z) :=
      lintegral_mono (fun z => lintegral_lineWeight_le_extended hq₁ hR.le e he _ m)
    _ = ENNReal.ofReal (2 * R) * ENNReal.ofReal (b - a) +
        ENNReal.ofReal (AxialSlices.lineConstant q) *
          ∫⁻ z in Ioc a b, extendedPower q (A - B * z) := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
    _ ≤ ENNReal.ofReal (2 * R) * ENNReal.ofReal (b - a) +
        ENNReal.ofReal (AxialSlices.lineConstant q) *
          ENNReal.ofReal (AxialSlices.scalarConstant (1 - q) *
            (R ^ (q - 1) * (b - a) ^ (2 - q) * |A| ^ (1 - q))) := by
      gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * R),
        ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add (by positivity) (by
          apply mul_nonneg hc
          apply mul_nonneg (AxialSlices.scalarConstant_pos (by linarith)).le
          positivity)]

theorem inner_quarterTurn_line_sub (e v : Transverse) (he : ‖e‖ = 1) (D s : ℝ) :
    inner ℝ (TransverseLine.quarterTurn e) (TransverseLine.line e D s - v) =
      s - inner ℝ (TransverseLine.quarterTurn e) v := by
  have ho : inner ℝ (TransverseLine.quarterTurn e) e = 0 := by
    rw [real_inner_comm, TransverseLine.inner_quarterTurn]
  rw [inner_sub_right]
  simp only [TransverseLine.line, inner_add_right, inner_smul_right, ho,
    real_inner_self_eq_norm_sq, TransverseLine.norm_quarterTurn, he]
  ring

theorem ballLineRegion_subset_rectangle {R : ℝ} (hR : 0 ≤ R)
    (e v : Transverse) (he : ‖e‖ = 1) (D z : ℝ) :
    ballLineRegion e v D z R ⊆
      Icc (inner ℝ (TransverseLine.quarterTurn e) v - R)
        (inner ℝ (TransverseLine.quarterTurn e) v + R) := by
  intro s hs
  have hnorm : ‖TransverseLine.line e D s - v‖ ≤ R := by
    change ‖TransverseLine.line e D s - v‖ ^ 2 + z ^ 2 ≤ R ^ 2 at hs
    nlinarith [sq_nonneg z, norm_nonneg (TransverseLine.line e D s - v)]
  have hi := abs_real_inner_le_norm (TransverseLine.quarterTurn e)
    (TransverseLine.line e D s - v)
  rw [inner_quarterTurn_line_sub e v he, TransverseLine.norm_quarterTurn, he, one_mul] at hi
  have ha := abs_le.mp (hi.trans hnorm)
  constructor <;> linarith [ha.1, ha.2]

theorem ballLineMass_le_rectangle {R : ℝ} (hR : 0 ≤ R)
    (q : ℝ) (e v : Transverse) (he : ‖e‖ = 1) (A B a b : ℝ) :
    ballLineMass q e v A B R a b ≤
      rectangleLineMass q e A B (inner ℝ (TransverseLine.quarterTurn e) v) R a b := by
  apply lintegral_mono
  intro z
  exact lintegral_mono_set (ballLineRegion_subset_rectangle hR e v he (A - B * z) z)

theorem ballLineMass_le {q a b A B R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) (hA : A ≠ 0)
    (e v : Transverse) (he : ‖e‖ = 1) :
    ballLineMass q e v A B R a b ≤
      ENNReal.ofReal (2 * R * (b - a) + AxialSlices.lineConstant q *
        (AxialSlices.scalarConstant (1 - q) *
          (R ^ (q - 1) * (b - a) ^ (2 - q) * |A| ^ (1 - q)))) :=
  (ballLineMass_le_rectangle hR.le q e v he A B a b).trans
    (rectangleLineMass_le hq₁ hq₂ hab hR ha hb hA e he _)

theorem transverseWeight_pos (q : ℝ) (v : Transverse) : 0 < transverseWeight q v := by
  unfold transverseWeight
  positivity

theorem intervalCoefficient_pos {q R ell : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : 0 < R) (hell : 0 < ell) : 0 < intervalCoefficient q R ell := by
  unfold intervalCoefficient
  exact mul_pos (AxialSlices.lineConstant_pos hq₁)
    (mul_pos (AxialSlices.scalarConstant_pos (by linarith))
      (mul_pos (Real.rpow_pos_of_pos hR _) (Real.rpow_pos_of_pos hell _)))

theorem averagingCoefficient_pos {q R ell r : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : 0 < R) (hell : 0 < ell) (hr : 0 ≤ r) : 0 < averagingCoefficient q R ell r := by
  have hc := intervalCoefficient_pos hq₁ hq₂ hR hell
  unfold averagingCoefficient
  positivity

theorem sliceOffset_eq_norm_mul_angle {v : Transverse} (hv : v ≠ 0) (p : Transverse) :
    sliceOffset v p = ‖v‖ * inner ℝ (direction v) (direction (v - p)) := by
  have he : inner ℝ (direction v) (direction (v - p)) = ‖v‖⁻¹ * sliceOffset v p := by
    change inner ℝ (‖v‖⁻¹ • v) (direction (v - p)) = _
    rw [real_inner_smul_left]
    unfold sliceOffset
    congr 1
    exact real_inner_comm _ _
  rw [he, ← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_mul]

theorem sliceOffset_rpow {v : Transverse} (hv : v ≠ 0) (p : Transverse) (q : ℝ) :
    |sliceOffset v p| ^ (1 - q) = ‖v‖ ^ (1 - q) *
      |inner ℝ (direction v) (direction (v - p))| ^ (1 - q) := by
  rw [sliceOffset_eq_norm_mul_angle hv, abs_mul, abs_of_nonneg (norm_nonneg v),
    Real.mul_rpow (norm_nonneg v) (abs_nonneg _)]

private theorem normalized_sum_bound {u w t beta c n : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (ht : 0 ≤ t) (hb : 0 ≤ beta)
    (hc : 0 < c) (hn : 0 < n) :
    (u + w * t * beta) / (c * n) ≤ (u + w * t) / c * ((1 + beta) / n) := by
  have hnum : u + w * t * beta ≤ (u + w * t) * (1 + beta) := by
    nlinarith [mul_nonneg hu hb, mul_nonneg hw ht]
  calc
    _ ≤ ((u + w * t) * (1 + beta)) / (c * n) :=
      div_le_div_of_nonneg_right hnum (mul_nonneg hc.le hn.le)
    _ = _ := by field_simp

private theorem slice_numerator_bound {q a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    {v : Transverse} (hv : v ≠ 0) {p : Transverse} (hp : RegularTransverse v p) :
    (2 * R * (b - a) + AxialSlices.lineConstant q *
      (AxialSlices.scalarConstant (1 - q) *
        (R ^ (q - 1) * (b - a) ^ (2 - q) * |sliceOffset v p| ^ (1 - q)))) /
        (transverseWeight q v * ‖v - p‖) ≤
      averagingCoefficient q R (b - a) ‖v‖ * kernel q (direction v) (v - p) := by
  have hc := (intervalCoefficient_pos hq₁ hq₂ hR (sub_pos.mpr hab)).le
  have h := normalized_sum_bound (by positivity : 0 ≤ 2 * R * (b - a)) hc
    (Real.rpow_nonneg (norm_nonneg v) (1 - q))
    (Real.rpow_nonneg (abs_nonneg (inner ℝ (direction v) (direction (v - p)))) (1 - q))
    (transverseWeight_pos q v) (norm_pos_iff.mpr hp.1)
  rw [sliceOffset_rpow hv]
  simpa only [averagingCoefficient, intervalCoefficient, transverseWeight, kernel, direction, mul_assoc] using h

/-- A pointwise bound with all singular transverse cases handled in the extended reals. -/
theorem normalizedBallSlice_le {q a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) {v : Transverse} (hv : v ≠ 0)
    (t alpha : ℝ) (p : Transverse) :
    normalizedBallSlice q v t p alpha R a b ≤
      ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖) * extendedKernel q v p := by
  classical
  have hc := averagingCoefficient_pos hq₁ hq₂ hR (sub_pos.mpr hab) (norm_nonneg v)
  by_cases hp : RegularTransverse v p
  · rw [normalizedBallSlice, ite_eq_left hp, extendedKernel, ite_eq_left hp]
    have hm := ballLineMass_le hq₁ hq₂ hab hR ha hb hp.2
      (direction (v - p)) v (norm_direction hp.1) (B := (t - alpha) / ‖v - p‖)
    have hw := transverseWeight_pos q v
    have hn := norm_pos_iff.mpr hp.1
    calc
      _ ≤ ENNReal.ofReal (1 / (transverseWeight q v * ‖v - p‖)) *
          ENNReal.ofReal (2 * R * (b - a) + AxialSlices.lineConstant q *
            (AxialSlices.scalarConstant (1 - q) *
              (R ^ (q - 1) * (b - a) ^ (2 - q) * |sliceOffset v p| ^ (1 - q)))) :=
        mul_le_mul_right hm _
      _ = ENNReal.ofReal ((2 * R * (b - a) + AxialSlices.lineConstant q *
            (AxialSlices.scalarConstant (1 - q) *
              (R ^ (q - 1) * (b - a) ^ (2 - q) * |sliceOffset v p| ^ (1 - q)))) /
              (transverseWeight q v * ‖v - p‖)) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖ *
          kernel q (direction v) (v - p)) :=
        ENNReal.ofReal_le_ofReal (slice_numerator_bound hq₁ hq₂ hab hR hv hp)
      _ = _ := ENNReal.ofReal_mul hc.le
  · rw [normalizedBallSlice, ite_eq_right hp, extendedKernel, ite_eq_right hp,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hc))]

theorem averagingCoefficient_bound {q R ell r : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 0 < R) (hell : 0 < ell) (hr : 0 < r) :
    averagingCoefficient q R ell r * (expectationConstant q / r) ≤
      expectationConstant q * (2 * R * ell + intervalCoefficient q R ell) := by
  have hreg := regular_fraction_le_one hr hq₁.le
  have hsing := singular_fraction_le_one hr q
  have hc := (intervalCoefficient_pos hq₁ hq₂ hR hell).le
  have hpow : r ^ (1 - q) * r⁻¹ = r ^ (-q) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hr]
    congr 1
    ring
  calc
    _ = expectationConstant q * (2 * R * ell * (r⁻¹ / (1 + r ^ (-q))) +
        intervalCoefficient q R ell * ((r ^ (1 - q) * r⁻¹) / (1 + r ^ (-q)))) := by
      unfold averagingCoefficient
      ring
    _ = expectationConstant q * (2 * R * ell * (r⁻¹ / (1 + r ^ (-q))) +
        intervalCoefficient q R ell * (r ^ (-q) / (1 + r ^ (-q)))) := by rw [hpow]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (expectationConstant_pos q).le
      have h₁ := mul_le_mul_of_nonneg_left hreg (by positivity : 0 ≤ 2 * R * ell)
      have h₂ := mul_le_mul_of_nonneg_left hsing hc
      nlinarith

/-- Averaging over an arbitrary axial probability leaves the uniform transverse
bound unchanged. The transverse expectation premise is discharged below for each law. -/
theorem normalizedBallSlice_product_bound {q a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hab : a < b) (hR : 0 < R)
    (ha : -R ≤ a) (hb : b ≤ R) {v : Transverse} (hv : v ≠ 0)
    (t : ℝ) (μ : Measure Transverse) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hμ : (∫⁻ p, extendedKernel q v p ∂μ) ≤ ENNReal.ofReal (expectationConstant q / ‖v‖)) :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R a b ∂μ.prod ρ) ≤
      ENNReal.ofReal (expectationConstant q *
        (2 * R * (b - a) + intervalCoefficient q R (b - a))) := by
  have hc := (averagingCoefficient_pos hq₁ hq₂ hR (sub_pos.mpr hab) (norm_nonneg v)).le
  have hm : Measurable (fun p : Transverse × ℝ => extendedKernel q v p.1) :=
    (measurable_extendedKernel q v).comp measurable_fst
  calc
    _ ≤ ∫⁻ p : Transverse × ℝ,
        ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖) * extendedKernel q v p.1 ∂μ.prod ρ :=
      lintegral_mono (fun p => normalizedBallSlice_le hq₁ hq₂ hab hR ha hb hv t p.2 p.1)
    _ = ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖) *
        ∫⁻ p, extendedKernel q v p ∂μ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_prod _ hm.aemeasurable]
      simp only [lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖) *
        ENNReal.ofReal (expectationConstant q / ‖v‖) := mul_le_mul_right hμ _
    _ = ENNReal.ofReal (averagingCoefficient q R (b - a) ‖v‖ *
        (expectationConstant q / ‖v‖)) := (ENNReal.ofReal_mul hc).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (averagingCoefficient_bound hq₁ hq₂ hR (sub_pos.mpr hab) (norm_pos_iff.mpr hv))

theorem geometricConstant_pos {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    0 < geometricConstant q := by
  have he := expectationConstant_pos q
  have hl := AxialSlices.lineConstant_pos hq₁
  have hs := AxialSlices.scalarConstant_pos (show -1 < 1 - q by linarith)
  unfold geometricConstant
  positivity

private theorem geometricConstant_bound {q R ell : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 0 < R) (hell : 0 < ell) :
    expectationConstant q * (2 * R * ell + intervalCoefficient q R ell) ≤
      geometricConstant q * (R * ell + R ^ (q - 1) * ell ^ (2 - q)) := by
  have hu : 0 ≤ R * ell := by positivity
  have hs : 0 ≤ R ^ (q - 1) * ell ^ (2 - q) := by positivity
  have hk : 0 ≤ AxialSlices.lineConstant q * AxialSlices.scalarConstant (1 - q) :=
    mul_nonneg (AxialSlices.lineConstant_pos hq₁).le
      (AxialSlices.scalarConstant_pos (by linarith)).le
  unfold geometricConstant intervalCoefficient
  rw [mul_assoc (expectationConstant q)]
  apply mul_le_mul_of_nonneg_left _ (expectationConstant_pos q).le
  nlinarith [mul_nonneg hk hu]

theorem ballLineRegion_eq_empty_of_outside {R z : ℝ} (hR : 0 ≤ R)
    (hz : z < -R ∨ R < z) (e v : Transverse) (D : ℝ) :
    ballLineRegion e v D z R = ∅ := by
  ext s
  simp only [ballLineRegion, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  intro hs
  rcases hz with hz | hz <;> nlinarith [sq_nonneg ‖TransverseLine.line e D s - v‖]

/-- The genuine ball already clips the axial displacement to `[-R,R]`.
The single lower endpoint is removed only on a Lebesgue-null set. -/
theorem ballLineMass_clip {R : ℝ} (hR : 0 ≤ R)
    (q : ℝ) (e v : Transverse) (A B a b : ℝ) :
    ballLineMass q e v A B R a b =
      ballLineMass q e v A B R (max (-R) a) (min R b) := by
  let F : ℝ → ℝ≥0∞ := fun z => ∫⁻ s in ballLineRegion e v (A - B * z) z R,
    ENNReal.ofReal (TransverseLine.lineWeight q e (A - B * z) s)
  have hz : ∀ᵐ z ∂(volume.restrict (Ioc a b)), z ≠ -R :=
    ae_restrict_of_ae (volume.ae_ne (-R))
  have hF : ∀ z, z ∉ Ioc (-R) R → z ≠ -R → F z = 0 := by
    intro z hout hne
    have ho : z < -R ∨ R < z := by
      by_cases hleft : -R < z
      · right
        have hn : ¬ z ≤ R := fun h => hout ⟨hleft, h⟩
        exact lt_of_not_ge hn
      · left
        exact lt_of_le_of_ne (le_of_not_gt hleft) hne
    simp only [F, ballLineRegion_eq_empty_of_outside hR ho, Measure.restrict_empty, lintegral_zero_measure]
  have hi : Ioc (-R) R ∩ Ioc a b = Ioc (max (-R) a) (min R b) := by
    ext z
    simp only [mem_inter_iff, mem_Ioc, max_lt_iff, le_min_iff]
    tauto
  change (∫⁻ z in Ioc a b, F z) = ∫⁻ z in Ioc (max (-R) a) (min R b), F z
  calc
    _ = ∫⁻ z in Ioc a b, (Ioc (-R) R).indicator F z := by
      apply lintegral_congr_ae
      filter_upwards [hz] with z hne
      by_cases hmem : z ∈ Ioc (-R) R
      · rw [indicator_of_mem hmem]
      · rw [indicator_of_notMem hmem, hF z hmem hne]
    _ = _ := by
      rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc, hi]

theorem normalizedBallSlice_clip {R : ℝ} (hR : 0 ≤ R)
    (q : ℝ) (v : Transverse) (t : ℝ) (p : Transverse) (alpha a b : ℝ) :
    normalizedBallSlice q v t p alpha R a b =
      normalizedBallSlice q v t p alpha R (max (-R) a) (min R b) := by
  classical
  by_cases hp : RegularTransverse v p
  · simp only [normalizedBallSlice, hp, ↓reduceIte]
    rw [ballLineMass_clip hR]
  · simp only [normalizedBallSlice, hp, ↓reduceIte]

/-- The interval estimate for arbitrary axial endpoints, using the actual ball
restriction to clip the interval before applying the scalar estimate. -/
theorem geometric_interval_of_kernel_bound {q a b R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (_hab : a < b) (hR : 0 < R)
    {v : Transverse} (hv : v ≠ 0) (t : ℝ)
    (μ : Measure Transverse) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hreg : ∀ᵐ p ∂μ, RegularTransverse v p)
    (hμ : (∫⁻ p, extendedKernel q v p ∂μ) ≤ ENNReal.ofReal (expectationConstant q / ‖v‖)) :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R a b ∂μ.prod ρ) ≤
      ENNReal.ofReal (geometricConstant q *
        (R * (b - a) + R ^ (q - 1) * (b - a) ^ (2 - q))) := by
  have heq : (fun p : Transverse × ℝ => normalizedBallSlice q v t p.1 p.2 R a b) =
      fun p => normalizedBallSlice q v t p.1 p.2 R (max (-R) a) (min R b) := by
    funext p
    exact normalizedBallSlice_clip hR.le q v t p.1 p.2 a b
  rw [heq]
  by_cases hc : max (-R) a < min R b
  · have hbound := normalizedBallSlice_product_bound hq₁ hq₂ hc hR
      (le_max_left _ _) (min_le_left _ _) hv t μ ρ hμ
    have hgeom := ENNReal.ofReal_le_ofReal
      (geometricConstant_bound hq₁ hq₂ hR (sub_pos.mpr hc))
    apply (hbound.trans hgeom).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (geometricConstant_pos hq₁ hq₂).le
    have hlen : min R b - max (-R) a ≤ b - a := by
      linarith [min_le_right R b, le_max_right (-R) a]
    have hp := Real.rpow_le_rpow (sub_pos.mpr hc).le hlen (show 0 ≤ 2 - q by linarith)
    exact add_le_add (mul_le_mul_of_nonneg_left hlen hR.le)
      (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hR.le _))
  · have hempty : Ioc (max (-R) a) (min R b) = ∅ := Ioc_eq_empty hc
    have hi : (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R
        (max (-R) a) (min R b) ∂μ.prod ρ) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ae_regularTransverse_prod hreg] with p hp
      simp only [normalizedBallSlice, hp, ↓reduceIte, ballLineMass, hempty,
        Measure.restrict_empty, lintegral_zero_measure, mul_zero, Pi.zero_apply]
    rw [hi]
    exact bot_le

/-- Taking the full axial range gives the uniform `C_q R²` ball estimate. -/
theorem geometric_total_of_kernel_bound {q R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hR : 1 ≤ R) {v : Transverse} (hv : v ≠ 0) (t : ℝ)
    (μ : Measure Transverse) (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hreg : ∀ᵐ p ∂μ, RegularTransverse v p)
    (hμ : (∫⁻ p, extendedKernel q v p ∂μ) ≤ ENNReal.ofReal (expectationConstant q / ‖v‖)) :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R (-R) R ∂μ.prod ρ) ≤
      ENNReal.ofReal (geometricTotalConstant q * R ^ 2) := by
  have hR₀ : 0 < R := by linarith
  have h := geometric_interval_of_kernel_bound hq₁ hq₂ (by linarith : -R < R) hR₀ hv t μ ρ hreg hμ
  have hpow : R ^ (q - 1) * (2 * R) ^ (2 - q) = (2 : ℝ) ^ (2 - q) * R := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR₀.le]
    calc
      _ = (2 : ℝ) ^ (2 - q) * (R ^ (q - 1) * R ^ (2 - q)) := by ring
      _ = _ := by rw [← Real.rpow_add hR₀, show q - 1 + (2 - q) = 1 by ring, Real.rpow_one]
  rw [show R - -R = 2 * R by ring, hpow] at h
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have hR₂ : R ≤ R ^ 2 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hR₂ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 - q))
  unfold geometricTotalConstant
  nlinarith [mul_nonneg (geometricConstant_pos hq₁ hq₂).le
    (sub_nonneg.mpr hp)]

end BoltzmannNonuniqueness.GeometricSlice

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SheetGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exponential tilting of cold sheets

These are the transverse density domination and axial moment-tail estimates
used in the proof of the uniform sheet gain bound, Section 3.
-/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture

namespace BoltzmannNonuniqueness.SheetTails

theorem gaussian_tilt_identity {d : ℝ} (hd : 0 < d) (u : Transverse) :
    Real.exp (2 * ‖u‖ ^ 2) * gaussianDensity d u =
      4 * Real.exp (-(3 / (4 * d ^ 2) - 2) * ‖u‖ ^ 2) * gaussianDensity (2 * d) u := by
  have hc : (Real.pi * d ^ 2)⁻¹ = 4 * (Real.pi * (2 * d) ^ 2)⁻¹ := by
    field_simp
    ring
  unfold gaussianDensity
  rw [hc]
  have he : 2 * ‖u‖ ^ 2 + -‖u‖ ^ 2 / d ^ 2 =
      -(3 / (4 * d ^ 2) - 2) * ‖u‖ ^ 2 + -‖u‖ ^ 2 / (2 * d) ^ 2 := by
    field_simp
    ring
  calc
    _ = (4 * (Real.pi * (2 * d) ^ 2)⁻¹) *
        (Real.exp (2 * ‖u‖ ^ 2) * Real.exp (-‖u‖ ^ 2 / d ^ 2)) := by ring
    _ = (4 * (Real.pi * (2 * d) ^ 2)⁻¹) *
        (Real.exp (-(3 / (4 * d ^ 2) - 2) * ‖u‖ ^ 2) *
          Real.exp (-‖u‖ ^ 2 / (2 * d) ^ 2)) := by rw [← Real.exp_add, he, Real.exp_add]
    _ = _ := by ring

/-- The widened transverse Gaussian retains a fixed Gaussian decay factor. -/
theorem gaussian_tilt_le {d : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 8) (u : Transverse) :
    Real.exp (2 * ‖u‖ ^ 2) * gaussianDensity d u ≤
      4 * Real.exp (-46 * ‖u‖ ^ 2) * gaussianDensity (2 * d) u := by
  have hd₂ : d ^ 2 ≤ 1 / 64 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdmax) (by linarith : 0 ≤ 1 / 8 + d)]
  have hk : 46 ≤ 3 / (4 * d ^ 2) - 2 := by
    have h : 48 ≤ 3 / (4 * d ^ 2) :=
      (le_div_iff₀ (by positivity : 0 < 4 * d ^ 2)).mpr (by nlinarith)
    linarith
  rw [gaussian_tilt_identity hd u]
  apply mul_le_mul_of_nonneg_right _ (gaussianDensity_nonneg _ _)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ‖u‖]

theorem gaussian_tilt_tail_le {d U : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 8)
    (hU : 0 ≤ U) (u : Transverse) (hu : U ≤ ‖u‖) :
    Real.exp (2 * ‖u‖ ^ 2) * gaussianDensity d u ≤
      (4 * Real.exp (-46 * U ^ 2)) * gaussianDensity (2 * d) u := by
  apply (gaussian_tilt_le hd hdmax u).trans
  apply mul_le_mul_of_nonneg_right _ (gaussianDensity_nonneg _ _)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply Real.exp_le_exp.mpr
  nlinarith [norm_nonneg u]

end BoltzmannNonuniqueness.SheetTails

end

end

section

/-!
# Probability sheets and their exponential tilts

An elementary sheet is the coordinate pushforward of a centered transverse
Gaussian (or the atom at zero) and an arbitrary axial probability law. The axial
exponential-moment hypothesis is recorded explicitly. All domination statements
below are inequalities of measures, so they also apply to nonnegative kernels.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture
open BoltzmannNonuniqueness.SheetTails

namespace BoltzmannNonuniqueness.SheetMeasures

theorem norm_join_sq (p : Transverse × ℝ) :
    ‖join p‖ ^ 2 = ‖p.1‖ ^ 2 + p.2 ^ 2 := by
  have h := split.apply_symm_apply (p.2, p.1)
  have hj : join p = split.symm (p.2, p.1) := rfl
  have ht : transverse (join p) = p.1 := by
    rw [hj]
    simpa only [split_apply] using congrArg Prod.snd h
  have ha : axial (join p) = p.2 := by
    rw [hj]
    simpa only [split_apply] using congrArg Prod.fst h
  rw [norm_sq_split, ht, ha]

theorem transverseLaw_isProbabilityMeasure {d : ℝ} (hd : 0 ≤ d) :
    IsProbabilityMeasure (transverseLaw d) := by
  unfold transverseLaw
  split_ifs with hz
  · infer_instance
  · exact gaussianLaw_isProbabilityMeasure (lt_of_le_of_ne hd (Ne.symm hz))

theorem sheetLaw_isProbabilityMeasure {d : ℝ} (hd : 0 ≤ d)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] : IsProbabilityMeasure (sheetLaw d ρ) := by
  have := transverseLaw_isProbabilityMeasure hd
  unfold sheetLaw
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem AxialMoment.nonneg {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) : 0 ≤ L :=
  (integral_nonneg (fun _ => (Real.exp_pos _).le)).trans h.bound

theorem mass_smul_normalizeFinite (μ : Measure ℝ) (hμ : μ univ < ∞) :
    μ univ • (normalizeFinite μ hμ : Measure ℝ) = μ := by
  let ν : FiniteMeasure ℝ := ⟨μ, ⟨hμ⟩⟩
  ext s hs
  have he := MeasureTheory.FiniteMeasure.self_eq_mass_mul_normalize ν s
  have he' := congrArg (fun r : ℝ≥0 => (r : ℝ≥0∞)) he.symm
  have hm : (ν.mass : ℝ≥0∞) = μ univ := FiniteMeasure.ennreal_mass
  have hs' : (ν s : ℝ≥0∞) = μ s := FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν s
  have hn : (ν.normalize s : ℝ≥0∞) = (normalizeFinite μ hμ : Measure ℝ) s :=
    ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure ν.normalize s
  rw [ENNReal.coe_mul, hm, hs', hn] at he'
  simpa only [Measure.smul_apply, smul_eq_mul] using he'

theorem axialTilt_eq_mass_smul {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) :
    axialTilt ρ = axialTilt ρ univ • (axialProbability ρ h : Measure ℝ) :=
  (mass_smul_normalizeFinite _ _).symm

private theorem smul_measure_mono {α : Type*} [MeasurableSpace α]
    {c d : ℝ≥0∞} (hcd : c ≤ d) (μ : Measure α) : c • μ ≤ d • μ := by
  apply Measure.le_iff.mpr
  intro s _
  simpa only [Measure.smul_apply, smul_eq_mul] using mul_le_mul_left hcd (μ s)

theorem axialTilt_le_probability {ρ : Measure ℝ} {L : ℝ} (h : AxialMoment ρ L) :
    axialTilt ρ ≤ ENNReal.ofReal L • (axialProbability ρ h : Measure ℝ) := by
  rw [axialTilt_eq_mass_smul h]
  exact smul_measure_mono (axialTilt_mass_le h) _

private theorem withDensity_map_join (μ : Measure (Transverse × ℝ))
    (w : Velocity → ℝ≥0∞) (hw : Measurable w) :
    (μ.map join).withDensity w = (μ.withDensity (fun p => w (join p))).map join := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hf,
    lintegral_map (hw.mul hf) join.measurable,
    lintegral_map hf join.measurable]
  change (∫⁻ p, w (join p) * f (join p) ∂μ) = _
  exact (lintegral_withDensity_eq_lintegral_mul μ
    (show Measurable (fun p => w (join p)) from hw.comp join.measurable)
    (show Measurable (fun p => f (join p)) from hf.comp join.measurable)).symm

theorem tiltedSheet_eq (d : ℝ) (ρ : Measure ℝ) [SFinite ρ] :
    tiltedSheet d ρ = ((transverseTilt d).prod (axialTilt ρ)).map join := by
  unfold tiltedSheet sheetLaw
  rw [withDensity_map_join _ _ (by fun_prop)]
  congr 1
  rw [transverseTilt, axialTilt, prod_withDensity (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  rw [norm_join_sq, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]

theorem transverseTilt_zero : transverseTilt 0 = Measure.dirac 0 := by
  simp [transverseTilt, transverseLaw, dirac_withDensity]

theorem transverseTilt_gaussian {d : ℝ} (hd : 0 < d) :
    transverseTilt d = volume.withDensity (fun p =>
      ENNReal.ofReal (Real.exp (2 * ‖p‖ ^ 2) * gaussianDensity d p)) := by
  simp only [transverseTilt, transverseLaw, ite_eq_right (c := d = 0) hd.ne', gaussianLaw]
  rw [← withDensity_mul _ (measurable_gaussianDensity d |>.ennreal_ofReal) (by fun_prop)]
  congr 1
  funext p
  simp only [Pi.mul_apply]
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]

theorem transverseTilt_le {d : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) :
    transverseTilt d ≤ (4 : ℝ≥0∞) • transverseLaw (2 * d) := by
  obtain rfl | hdpos := hd.eq_or_lt
  · rw [transverseTilt_zero]
    simp only [mul_zero, transverseLaw, ite_true, if_true]
    calc
      Measure.dirac (0 : Transverse) = (1 : ℝ≥0∞) • Measure.dirac 0 := (one_smul _ _).symm
      _ ≤ (4 : ℝ≥0∞) • Measure.dirac 0 := smul_measure_mono (by norm_num) _
  · rw [transverseTilt_gaussian hdpos]
    have h2d : 2 * d ≠ 0 := by positivity
    simp only [transverseLaw, ite_eq_right (c := 2 * d = 0) h2d, gaussianLaw]
    rw [← withDensity_smul _ (measurable_gaussianDensity (2 * d) |>.ennreal_ofReal)]
    apply withDensity_mono
    filter_upwards [] with p
    change ENNReal.ofReal _ ≤ 4 * ENNReal.ofReal _
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    apply ENNReal.ofReal_le_ofReal
    apply (gaussian_tilt_le hdpos hdmax p).trans
    apply mul_le_mul_of_nonneg_right _ (gaussianDensity_nonneg _ _)
    have he : Real.exp (-46 * ‖p‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _))
    linarith

theorem tiltedSheet_le {d : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (ρ : Measure ℝ) [SFinite ρ] :
    tiltedSheet d ρ ≤ (4 : ℝ≥0∞) •
      ((transverseLaw (2 * d)).prod (axialTilt ρ)).map join := by
  have : SFinite (axialTilt ρ) := by unfold axialTilt; infer_instance
  rw [tiltedSheet_eq]
  have hp := Measure.prod_mono (transverseTilt_le hd hdmax)
    (le_refl (axialTilt ρ))
  have hm := Measure.map_mono hp join.measurable
  simpa only [Measure.prod_smul_left,
    Measure.map_smul] using hm

theorem tiltedSheet_le_probability {d L : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (h : AxialMoment ρ L) :
    tiltedSheet d ρ ≤ ENNReal.ofReal (4 * L) •
      sheetLaw (2 * d) (axialProbability ρ h) := by
  apply (tiltedSheet_le hd hdmax ρ).trans
  rw [axialTilt_eq_mass_smul h, Measure.prod_smul_right,
    Measure.map_smul, smul_smul]
  apply smul_measure_mono
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  simpa using mul_le_mul_right (axialTilt_mass_le h) (4 : ℝ≥0∞)

theorem axialTail_eq_mass_smul {ρ : Measure ℝ} {L U : ℝ} (h : AxialMoment ρ L)
    (hU : 0 ≤ U) :
    axialTail ρ U = axialTail ρ U univ • (axialTailProbability ρ h hU : Measure ℝ) :=
  (mass_smul_normalizeFinite _ _).symm

theorem axialTail_le_probability {ρ : Measure ℝ} {L U : ℝ} (h : AxialMoment ρ L)
    (hU : 0 ≤ U) :
    axialTail ρ U ≤ ENNReal.ofReal (Real.exp (-6 * U ^ 2) * L) •
      (axialTailProbability ρ h hU : Measure ℝ) := by
  rw [axialTail_eq_mass_smul h hU]
  exact smul_measure_mono (axialTail_mass_le h hU) _

theorem transverseTilt_finite {d : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) :
    IsFiniteMeasure (transverseTilt d) := by
  have := transverseLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
  have := Measure.smul_finite (transverseLaw (2 * d)) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)
  exact isFiniteMeasure_of_le ((4 : ℝ≥0∞) • transverseLaw (2 * d))
    (transverseTilt_le hd hdmax)

theorem transverseTilt_tail_le {d U : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    (hU : 0 ≤ U) :
    (transverseTilt d).restrict {p : Transverse | U < ‖p‖} ≤
      ENNReal.ofReal (4 * Real.exp (-46 * U ^ 2)) • transverseLaw (2 * d) := by
  obtain rfl | hdpos := hd.eq_or_lt
  · rw [transverseTilt_zero]
    have hz : (Measure.dirac (0 : Transverse)).restrict {p : Transverse | U < ‖p‖} = 0 := by
      apply Measure.restrict_eq_zero.mpr
      simp only [Measure.dirac_apply, indicator_of_notMem (show (0 : Transverse) ∉ {p : Transverse | U < ‖p‖} by simpa using not_lt.mpr hU)]
    rw [hz]
    exact bot_le
  · rw [transverseTilt_gaussian hdpos]
    have hs : MeasurableSet {p : Transverse | U < ‖p‖} :=
      measurableSet_lt measurable_const measurable_norm
    rw [restrict_withDensity hs, ← withDensity_indicator hs]
    have h2d : 2 * d ≠ 0 := by positivity
    simp only [transverseLaw, ite_eq_right (c := 2 * d = 0) h2d, gaussianLaw]
    rw [← withDensity_smul _ (measurable_gaussianDensity (2 * d) |>.ennreal_ofReal)]
    apply withDensity_mono
    filter_upwards [] with p
    by_cases hp : U < ‖p‖
    · simp only [indicator_of_mem (show p ∈ {p : Transverse | U < ‖p‖} from hp),
        Pi.smul_apply, smul_eq_mul]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.exp (-46 * U ^ 2))]
      exact ENNReal.ofReal_le_ofReal (gaussian_tilt_tail_le hdpos hdmax hU p hp.le)
    · simp only [indicator_of_notMem (show p ∉ {p : Transverse | U < ‖p‖} from hp)]
      exact bot_le

private theorem product_tail_le (μ : Measure Transverse) (ν : Measure ℝ)
    [SFinite μ] [SFinite ν] {u : ℝ} (hu : 0 ≤ u) :
    (μ.prod ν).restrict {p : Transverse × ℝ | u < ‖join p‖} ≤
      (μ.restrict {p : Transverse | u / 2 < ‖p‖}).prod ν +
        μ.prod (ν.restrict {a : ℝ | u / 2 < |a|}) := by
  have hs : {p : Transverse × ℝ | u < ‖join p‖} ⊆
      ({p : Transverse | u / 2 < ‖p‖} ×ˢ univ) ∪
        (univ ×ˢ {a : ℝ | u / 2 < |a|}) := by
    intro p hp
    by_contra hn
    have hn₁ : ‖p.1‖ ≤ u / 2 := by simpa using (not_or.mp hn).1
    have hn₂ : |p.2| ≤ u / 2 := by simpa using (not_or.mp hn).2
    have hn₃ := norm_join_sq p
    have hn₄ := sq_abs p.2
    have hs₁ : ‖p.1‖ ^ 2 ≤ (u / 2) ^ 2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hn₁
    have hs₂ : |p.2| ^ 2 ≤ (u / 2) ^ 2 := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.mpr hn₂
    have hs₃ : u ^ 2 < ‖join p‖ ^ 2 := sq_lt_sq₀ hu (norm_nonneg _) |>.mpr hp
    nlinarith
  apply (Measure.restrict_mono_set _ hs).trans
  apply (Measure.restrict_union_le _ _).trans
  rw [← Measure.restrict_prod_eq_prod_univ]
  have he : (μ.prod ν).restrict (univ ×ˢ {a : ℝ | u / 2 < |a|}) =
      μ.prod (ν.restrict {a : ℝ | u / 2 < |a|}) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  rw [he]

private theorem transverse_tail_coefficient_le {L u : ℝ} (hL : 0 ≤ L) :
    ENNReal.ofReal (4 * Real.exp (-46 * (u / 2) ^ 2)) * ENNReal.ofReal L ≤
      tailCoefficient L u := by
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.exp (-46 * (u / 2) ^ 2))]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ hL
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg u]

private theorem axial_tail_coefficient (L u : ℝ) :
    (4 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-6 * (u / 2) ^ 2) * L) =
      tailCoefficient L u := by
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  unfold tailCoefficient
  apply congrArg ENNReal.ofReal
  rw [show -6 * (u / 2) ^ 2 = -(3 / 2) * u ^ 2 by ring]
  ring

/-- The exponentially tilted norm tail is dominated by two probability sheets.
The second axial law is the normalized tilted axial tail and may be an atom
when the tail vanishes. -/
theorem tiltedSheet_tail_le {d L u : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (h : AxialMoment ρ L) (hu : 0 ≤ u) :
    (tiltedSheet d ρ).restrict {p : Velocity | u < ‖p‖} ≤
      tailCoefficient L u •
        (sheetLaw (2 * d) (axialProbability ρ h) +
          sheetLaw (2 * d) (axialTailProbability ρ h (by positivity : 0 ≤ u / 2))) := by
  have := transverseTilt_finite hd hdmax
  have := axialTilt_finite h
  have := transverseLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
  have := axialTail_finite h (show 0 ≤ u / 2 by positivity)
  have ht : ((transverseTilt d).restrict {p : Transverse | u / 2 < ‖p‖}).prod (axialTilt ρ) ≤
      tailCoefficient L u • (transverseLaw (2 * d)).prod (axialProbability ρ h) := by
    apply (Measure.prod_mono (transverseTilt_tail_le hd hdmax (by positivity))
      (axialTilt_le_probability h)).trans
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    exact smul_measure_mono (transverse_tail_coefficient_le h.nonneg) _
  have ha : (transverseTilt d).prod (axialTail ρ (u / 2)) ≤
      tailCoefficient L u •
        (transverseLaw (2 * d)).prod (axialTailProbability ρ h (by positivity : 0 ≤ u / 2)) := by
    apply (Measure.prod_mono (transverseTilt_le hd hdmax)
      (axialTail_le_probability h (by positivity))).trans
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, axial_tail_coefficient]
  rw [tiltedSheet_eq, Measure.restrict_map join.measurable (measurableSet_lt measurable_const measurable_norm)]
  have hb := (product_tail_le (transverseTilt d) (axialTilt ρ) hu).trans (add_le_add ht ha)
  have hm := Measure.map_mono hb join.measurable
  simpa only [Measure.map_add _ _ join.measurable,
    Measure.map_smul, ← smul_add, sheetLaw,
    axialTail, preimage_ofPred_eq] using hm

end BoltzmannNonuniqueness.SheetMeasures

end

end

section

/-!
# Geometric and Gaussian bounds for the gain of an elementary sheet

The ball integrals below use the actual three-dimensional collision chart.
The sheet laws may have an atomic transverse component and arbitrary axial
probability laws. No gain bound is included among the hypotheses.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.SheetMeasures

namespace BoltzmannNonuniqueness.SheetGain

theorem normal_join (v : Velocity) (p : Transverse × ℝ) :
    PlaneChart.normal v (SheetMeasures.join p) = transverse v - p.1 := by
  change transverse (v - PlaneChart.join p.1 p.2) = _
  rw [PlaneChart.transverse_sub, PlaneChart.transverse_join]

theorem slope_join (v : Velocity) (p : Transverse × ℝ) :
    PlaneChart.slope v (SheetMeasures.join p) =
      (axial v - p.2) / ‖transverse v - p.1‖ := by
  unfold PlaneChart.slope
  rw [normal_join]
  change axial (v - PlaneChart.join p.1 p.2) / _ = _
  rw [PlaneChart.axial_sub, PlaneChart.axial_join]

theorem offset_join (v : Velocity) (p : Transverse × ℝ) :
    PlaneChart.offset v (SheetMeasures.join p) = sliceOffset (transverse v) p.1 := by
  unfold PlaneChart.offset sliceOffset
  rw [normal_join]

theorem W_eq_transverseWeight (q : ℝ) (v : Velocity) :
    W q v = transverseWeight q (transverse v) := rfl

theorem chart_weight_join (q : ℝ) (v : Velocity) (p : Transverse × ℝ) (z s : ℝ) :
    W q (PlaneChart.chart v (SheetMeasures.join p) z s) =
      TransverseLine.lineWeight q (direction (transverse v - p.1))
        (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) s := by
  unfold W singularity
  rw [PlaneChart.transverse_chart, normal_join, offset_join, slope_join]
  rfl

theorem chart_ball_join {R : ℝ} (hR : 0 ≤ R) (v : Velocity) (p : Transverse × ℝ)
    (z s : ℝ) :
    ‖PlaneChart.chart v (SheetMeasures.join p) z s - v‖ ≤ R ↔
      s ∈ ballLineRegion (direction (transverse v - p.1)) (transverse v)
        (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) z R := by
  rw [← sq_le_sq₀ (norm_nonneg _) hR, PlaneChart.chart_displacement_norm_sq,
    normal_join, offset_join, slope_join]
  rfl

/-- Clipping the axial chart coordinate loses only the null endpoint `-R`. -/
theorem full_ballLineMass_eq {R : ℝ} (hR : 0 ≤ R) (q : ℝ) (e v : Transverse)
    (A B : ℝ) :
    (∫⁻ z : ℝ, ∫⁻ s in ballLineRegion e v (A - B * z) z R,
      ENNReal.ofReal (TransverseLine.lineWeight q e (A - B * z) s)) =
        ballLineMass q e v A B R (-R) R := by
  unfold ballLineMass
  rw [← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr_ae
  filter_upwards [volume.ae_ne (-R)] with z hz
  by_cases hm : z ∈ Ioc (-R) R
  · simp only [indicator_of_mem hm]
  · rw [indicator_of_notMem hm]
    have hout : z < -R ∨ R < z := by
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at hm
      rcases hm with hm | hm
      · exact Or.inl (lt_of_le_of_ne hm hz)
      · exact Or.inr hm
    rw [ballLineRegion_eq_empty_of_outside hR hout, Measure.restrict_empty, lintegral_zero_measure]

theorem ballChartFiber_le_slice {R : ℝ} (hR : 0 ≤ R) (q : ℝ)
    (v : Velocity) (p : Transverse × ℝ) :
    ballChartFiber q v (SheetMeasures.join p) R ≤
      normalizedBallSlice q (transverse v) (axial v) p.1 p.2 R (-R) R := by
  classical
  by_cases hp : RegularTransverse (transverse v) p.1
  · have hweight : 0 < transverseWeight q (transverse v) := transverseWeight_pos q _
    have hcoef : ENNReal.ofReal (‖transverse v - p.1‖⁻¹) *
        ENNReal.ofReal ((transverseWeight q (transverse v))⁻¹) =
      ENNReal.ofReal (1 / (transverseWeight q (transverse v) * ‖transverse v - p.1‖)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      simp only [one_div, mul_inv_rev]
    have hpoint : ∀ z s : ℝ,
        (if ‖PlaneChart.chart v (SheetMeasures.join p) z s - v‖ ≤ R then
          weightRatio q v (PlaneChart.chart v (SheetMeasures.join p) z s) else 0) =
        ENNReal.ofReal ((transverseWeight q (transverse v))⁻¹) *
          (ballLineRegion (direction (transverse v - p.1)) (transverse v)
            (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) z R).indicator
          (fun s => ENNReal.ofReal (TransverseLine.lineWeight q (direction (transverse v - p.1))
            (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) s)) s := by
      intro z s
      by_cases hm : s ∈ ballLineRegion (direction (transverse v - p.1)) (transverse v)
          (sliceOffset (transverse v) p.1 - (axial v - p.2) / ‖transverse v - p.1‖ * z) z R
      · have hc := (chart_ball_join hR v p z s).mpr hm
        rw [ite_eq_left hc, indicator_of_mem hm]
        unfold weightRatio
        rw [chart_weight_join, W_eq_transverseWeight, div_eq_mul_inv, mul_comm,
          ENNReal.ofReal_mul (inv_nonneg.mpr hweight.le)]
      · have hc := mt (chart_ball_join hR v p z s).mp hm
        simp only [ite_eq_right hc, indicator_of_notMem hm, mul_zero]
    have hm : ∀ z : ℝ, MeasurableSet (ballLineRegion (direction (transverse v - p.1))
        (transverse v) (sliceOffset (transverse v) p.1 -
          (axial v - p.2) / ‖transverse v - p.1‖ * z) z R) := by
      intro z
      unfold ballLineRegion TransverseLine.line
      apply measurableSet_le <;> fun_prop
    unfold ballChartFiber
    simp_rw [normal_join, hpoint, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_indicator (hm _)]
    rw [← mul_assoc, hcoef, full_ballLineMass_eq hR]
    rw [normalizedBallSlice, ite_eq_left hp]
  · rw [normalizedBallSlice, ite_eq_right hp]
    exact le_top

theorem weight_ball_sheet_bound {q d R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hR : 1 ≤ R) {v : Velocity} (hv : transverse v ≠ 0)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    chartRegionGain (sheetLaw d ρ) (weightRatio q v) v (ballRegion v R) ≤
      2 * ENNReal.ofReal (geometricTotalConstant q * R ^ 2) := by
  have hs : (∫⁻ p, normalizedBallSlice q (transverse v) (axial v) p.1 p.2 R (-R) R
      ∂(transverseLaw d).prod ρ) ≤ ENNReal.ofReal (geometricTotalConstant q * R ^ 2) := by
    apply geometric_total_of_kernel_bound hq₁ hq₂ hR hv
    · obtain rfl | hdpos := hd.eq_or_lt
      · simpa only [transverseLaw, ite_true, if_true] using ae_regularTransverse_atom hv
      · simpa only [transverseLaw, ite_eq_right hdpos.ne'] using ae_regularTransverse_gaussian hv d
    · obtain rfl | hdpos := hd.eq_or_lt
      · simpa only [transverseLaw, ite_true, if_true] using atom_extendedKernel_lintegral_le q hv
      · simpa only [transverseLaw, ite_eq_right hdpos.ne'] using
          gaussian_extendedKernel_lintegral_le hq₁ hq₂ hdpos hv
  unfold chartRegionGain
  change 2 * (∫⁻ p, ballChartFiber q v p R ∂sheetLaw d ρ) ≤ _
  unfold sheetLaw
  rw [lintegral_map_equiv]
  exact mul_le_mul_right ((lintegral_mono (ballChartFiber_le_slice (by linarith) q v)).trans hs) 2

end BoltzmannNonuniqueness.SheetGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ChartPointLift
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The normalized gain as a measure on chart coordinates

This measure retains the incoming velocity and both plane coordinates. Its
restriction equals the chart gain, so countable shell
estimates concern the full normalized kernel of the manuscript.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.ChartKernel

theorem measurable_H (q : ℝ) : Measurable (H q) := by
  unfold H singularity
  fun_prop

theorem measurable_W (q : ℝ) : Measurable (W q) := by
  unfold W singularity
  fun_prop

theorem measurable_density {h : Velocity → ℝ≥0∞} (hh : Measurable h) (v : Velocity) :
    Measurable (density h v) := by
  have hn : Measurable (fun y : Coordinates => normal v y.1) :=
    measurable_transverse.comp (measurable_const.sub measurable_fst)
  exact (measurable_const.mul hn.norm.inv.ennreal_ofReal).mul
    (hh.comp (measurable_point v))

theorem region_eq_measure (c : Measure Velocity) {h : Velocity → ℝ≥0∞}
    (hh : Measurable h) (v : Velocity) {S : Set Coordinates} (hS : MeasurableSet S) :
    chartRegionGain c h v S = measure c h v S := by
  classical
  rw [measure, withDensity_apply _ hS, ← lintegral_indicator hS]
  rw [lintegral_prod _ ((measurable_density hh v).indicator hS).aemeasurable]
  have hi (p : Velocity) :
      (∫⁻ zs : ℝ × ℝ, S.indicator (density h v) (p, zs) ∂(volume.prod volume)) =
        ∫⁻ z : ℝ, ∫⁻ s : ℝ, S.indicator (density h v) (p, (z, s)) :=
    lintegral_prod _ (((measurable_density hh v).indicator hS).comp
      measurable_prodMk_left).aemeasurable
  simp_rw [hi]
  have he : ∀ p z s, S.indicator (density h v) (p, (z, s)) =
      2 * (ENNReal.ofReal (‖normal v p‖⁻¹) *
        S.indicator (fun y => h (chart v y.1 y.2.1 y.2.2)) (p, (z, s))) := by
    intro p z s
    by_cases hm : (p, (z, s)) ∈ S
    · simp only [indicator_of_mem hm, density, mul_assoc]
    · simp only [indicator_of_notMem hm, mul_zero]
  simp_rw [he, lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

theorem total_eq (c : Measure Velocity) {h : Velocity → ℝ≥0∞}
    (hh : Measurable h) (v : Velocity) :
    chartGain c h v = measure c h v univ := by
  simpa only [chartRegionGain, indicator_univ, chartGain] using
    region_eq_measure c hh v MeasurableSet.univ

theorem normalized_total_eq (c : Measure Velocity) (q : ℝ) (v : Velocity) :
    normalizedChartGain c q v = normalizedMeasure c q v univ :=
  total_eq c ((measurable_H q).div_const _ |>.ennreal_ofReal) v

theorem measure_mono_incoming {c d : Measure Velocity} (hcd : c ≤ d)
    (h : Velocity → ℝ≥0∞) (v : Velocity) : measure c h v ≤ measure d h v := by
  apply Measure.le_iff.mpr
  intro S hS
  simp only [measure, withDensity_apply _ hS]
  exact lintegral_mono' (Measure.restrict_mono_measure
    (Measure.prod_mono hcd le_rfl) S) (fun _ => le_rfl)

theorem measure_smul (a : ℝ≥0∞) (c : Measure Velocity)
    (h : Velocity → ℝ≥0∞) (v : Velocity) :
    measure (a • c) h v = a • measure c h v := by
  rw [measure, Measure.prod_smul_left, withDensity_smul_measure]
  rfl

theorem measure_add (c d : Measure Velocity) [SFinite c] [SFinite d]
    (h : Velocity → ℝ≥0∞) (v : Velocity) :
    measure (c + d) h v = measure c h v + measure d h v := by
  rw [measure, Measure.add_prod, withDensity_add_measure]
  rfl

theorem measure_withDensity (c : Measure Velocity) {w h : Velocity → ℝ≥0∞}
    (hw : Measurable w) (hh : Measurable h) (v : Velocity) :
    measure (c.withDensity w) h v =
      (c.prod (volume.prod volume)).withDensity (fun y => w y.1 * density h v y) := by
  rw [measure, prod_withDensity_left hw]
  exact (withDensity_mul _ (hw.comp measurable_fst) (measurable_density hh v)).symm

/-- A pointwise comparison, integrated without losing the coordinate restriction. -/
theorem restriction_comparison (c : Measure Velocity) {w h k : Velocity → ℝ≥0∞}
    (hw : Measurable w) (hk : Measurable k) (v : Velocity) (a : ℝ≥0∞)
    {S T : Set Coordinates} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hp : ∀ y, S.indicator (density h v) y ≤
      a * (w y.1 * T.indicator (density k v) y)) :
    measure c h v S ≤ a * measure (c.withDensity w) k v T := by
  rw [measure_withDensity c hw hk v]
  rw [measure, withDensity_apply _ hS, withDensity_apply _ hT,
    ← lintegral_indicator hS, ← lintegral_indicator hT]
  simp only [indicator_mul_right]
  have hm : Measurable (fun y : Coordinates => w y.1 * T.indicator (density k v) y) :=
    (hw.comp measurable_fst).mul ((measurable_density hk v).indicator hT)
  rw [← lintegral_const_mul a hm]
  apply lintegral_mono
  intro y
  exact hp y

theorem measure_restrict_incoming (c : Measure Velocity) [SFinite c]
    (h : Velocity → ℝ≥0∞) (v : Velocity) {A : Set Velocity} (hA : MeasurableSet A) :
    measure (c.restrict A) h v = (measure c h v).restrict (A ×ˢ univ) := by
  rw [measure, Measure.restrict_prod_eq_prod_univ, ← restrict_withDensity (hA.prod .univ)]
  rfl

theorem normalized_restrict_incoming (c : Measure Velocity) [SFinite c]
    (q : ℝ) (v : Velocity) {A : Set Velocity} (hA : MeasurableSet A) :
    normalizedMeasure (c.restrict A) q v = (normalizedMeasure c q v).restrict (A ×ˢ univ) :=
  measure_restrict_incoming c _ v hA

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Uniform elementary-sheet gain estimates

The incoming exponential tilt and the Gaussian in the companion velocity
are kept separate. All regions below refer to the complete normalized
kernel, including its singular velocity weight.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.UniformGain

theorem measurable_exponentialTilt : Measurable exponentialTilt := by
  unfold exponentialTilt
  fun_prop

theorem measurable_weightRatio (q : ℝ) (v : Velocity) : Measurable (weightRatio q v) :=
  ((measurable_W q).div_const _).ennreal_ofReal

theorem ratio_bound {B : ℝ} (q : ℝ) (v p : Velocity) (z s : ℝ)
    (hn : normal v p ≠ 0)
    (hb : Real.exp (-‖companionVelocity p (chart v p z s) v‖ ^ 2) ≤ B) :
    H q (chart v p z s) / H q v ≤
      (tiltConstant * B) * Real.exp (2 * ‖p‖ ^ 2) *
        (W q (chart v p z s) / W q v) := by
  apply (chart_weight_ratio_le q v p z s hn).trans
  rw [sub_eq_add_neg, Real.exp_add]
  have hw : 0 ≤ W q (chart v p z s) / W q v :=
    div_nonneg (W_pos _ _).le (W_pos _ _).le
  calc
    _ ≤ tiltConstant * (Real.exp (2 * ‖p‖ ^ 2) * B) *
        (W q (chart v p z s) / W q v) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)) tiltConstant_pos.le) hw
    _ = _ := by ring

/-- The weight transfer can be applied on any measurable portion of the chart. -/
theorem normalized_restriction_le (c : Measure Velocity) (q : ℝ) (v : Velocity)
    {S T : Set Coordinates} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hST : S ⊆ T) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ y ∈ S,
      Real.exp (-‖companionVelocity y.1 (chart v y.1 y.2.1 y.2.2) v‖ ^ 2) ≤ B) :
    normalizedMeasure c q v S ≤ ENNReal.ofReal (tiltConstant * B) *
      ChartKernel.measure (c.withDensity exponentialTilt) (weightRatio q v) v T := by
  apply restriction_comparison c measurable_exponentialTilt (measurable_weightRatio q v)
    v _ hS hT
  intro y
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy, indicator_of_mem (hST hy)]
    by_cases hn : normal v y.1 = 0
    · simp [density, hn]
    · have hr := ENNReal.ofReal_le_ofReal
        (ratio_bound q v y.1 y.2.1 y.2.2 hn (hb y hy))
      have hc : 0 ≤ tiltConstant * B := mul_nonneg tiltConstant_pos.le hB
      rw [ENNReal.ofReal_mul (mul_nonneg hc (Real.exp_nonneg _)),
        ENNReal.ofReal_mul hc] at hr
      change 2 * ENNReal.ofReal _ * ENNReal.ofReal _ ≤
        ENNReal.ofReal (tiltConstant * B) *
          (exponentialTilt y.1 * (2 * ENNReal.ofReal _ * weightRatio q v _))
      have he := mul_le_mul_left hr (2 * ENNReal.ofReal (‖normal v y.1‖⁻¹))
      simpa only [exponentialTilt, weightRatio, mul_assoc, mul_left_comm, mul_comm] using he
  · rw [indicator_of_notMem hy]
    exact bot_le

theorem measurableSet_ballRegion (v : Velocity) (R : ℝ) : MeasurableSet (ballRegion v R) :=
  measurableSet_le ((measurable_point v).sub_const v).norm measurable_const

theorem weight_ball_measure_bound {q d R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hR : 1 ≤ R) {v : Velocity} (hv : transverse v ≠ 0)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ChartKernel.measure (sheetLaw d ρ) (weightRatio q v) v (ballRegion v R) ≤
      2 * ENNReal.ofReal (GeometricSlice.geometricTotalConstant q * R ^ 2) := by
  rw [← region_eq_measure _ (measurable_weightRatio q v) v (measurableSet_ballRegion v R)]
  exact weight_ball_sheet_bound hq₁ hq₂ hd hR hv ρ

theorem tilted_ball_bound {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    ChartKernel.measure (tiltedSheet d ρ) (weightRatio q v) v (ballRegion v R) ≤
      ENNReal.ofReal (4 * L) * ballBound q R := by
  have h := (measure_mono_incoming (tiltedSheet_le_probability hd hdmax hρ)
    (weightRatio q v) v) (ballRegion v R)
  rw [measure_smul, Measure.smul_apply, smul_eq_mul] at h
  exact h.trans (mul_le_mul' le_rfl
    (weight_ball_measure_bound hq₁ hq₂ (by positivity) hR hv (axialProbability ρ hρ)))

theorem tilted_tail_ball_bound {q d R L u : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R) (hu : 0 ≤ u)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    ChartKernel.measure ((tiltedSheet d ρ).restrict {p : Velocity | u < ‖p‖})
      (weightRatio q v) v (ballRegion v R) ≤
        tailCoefficient L u * (ballBound q R + ballBound q R) := by
  have := sheetLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
    (axialProbability ρ hρ : Measure ℝ)
  have := sheetLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
    (axialTailProbability ρ hρ (by positivity : 0 ≤ u / 2) : Measure ℝ)
  have h := (measure_mono_incoming (tiltedSheet_tail_le hd hdmax hρ hu)
    (weightRatio q v) v) (ballRegion v R)
  rw [measure_smul, measure_add, Measure.smul_apply, Measure.add_apply, smul_eq_mul] at h
  exact h.trans (mul_le_mul' le_rfl (add_le_add
    (weight_ball_measure_bound hq₁ hq₂ (by positivity) hR hv (axialProbability ρ hρ))
    (weight_ball_measure_bound hq₁ hq₂ (by positivity) hR hv
      (axialTailProbability ρ hρ (by positivity : 0 ≤ u / 2)))))

theorem normalized_ball_bound {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (ballRegion v R) ≤
      ENNReal.ofReal tiltConstant * ENNReal.ofReal (4 * L) * ballBound q R := by
  have h := normalized_restriction_le (sheetLaw d ρ) q v
    (measurableSet_ballRegion v R) (measurableSet_ballRegion v R) (Subset.refl _)
    (B := 1) (by norm_num) (fun _ _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  simp only [mul_one] at h
  exact h.trans ((mul_le_mul' le_rfl (tilted_ball_bound hq₁ hq₂ hd hdmax hR hv hρ)).trans_eq
    (mul_assoc _ _ _).symm)

theorem measurable_radius (v : Velocity) : Measurable (radius v) :=
  measurable_fst.norm.add (((measurable_point v).sub_const v).norm)

theorem measurableSet_shell (v : Velocity) (R : ℝ) : MeasurableSet (shell v R) :=
  (measurableSet_lt measurable_const (measurable_radius v)).inter
    (measurableSet_le (measurable_radius v) measurable_const)

theorem measurableSet_incomingTail (u : ℝ) : MeasurableSet (incomingTail u) :=
  measurableSet_lt measurable_const measurable_norm

theorem measurableSet_companionTail (v : Velocity) (u : ℝ) :
    MeasurableSet (companionTail v u) := by
  unfold companionTail companionVelocity
  exact measurableSet_lt measurable_const
    ((measurable_fst.add (measurable_point v)).sub_const v).norm

theorem shell_subset_ball (v : Velocity) (R : ℝ) : shell v R ⊆ ballRegion v (2 * R) := by
  intro y hy
  have hp := norm_nonneg y.1
  exact le_trans (le_add_of_nonneg_left hp) hy.2

theorem shell_subset_union (v : Velocity) (R : ℝ) :
    shell v R ⊆ (shell v R ∩ (incomingTail (R / 4) ×ˢ univ)) ∪
      (shell v R ∩ companionTail v (R / 2)) := by
  intro y hy
  rcases shell_alternative y.1 (chart v y.1 y.2.1 y.2.2 - v) hy.1 with hp | hw
  · exact Or.inl ⟨hy, hp, mem_univ _⟩
  · exact Or.inr ⟨hy, by simpa only [companionTail, mem_ofPred_eq,
      companionVelocity, add_sub_assoc] using hw⟩

theorem normalized_cold_shell_bound {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v
      (shell v R ∩ (incomingTail (R / 4) ×ˢ univ)) ≤
      ENNReal.ofReal tiltConstant * tailCoefficient L (R / 4) *
        (ballBound q (2 * R) + ballBound q (2 * R)) := by
  have := sheetLaw_isProbabilityMeasure hd ρ
  rw [← Measure.restrict_apply (measurableSet_shell v R),
    ← normalized_restrict_incoming _ q v (measurableSet_incomingTail (R / 4))]
  have h := normalized_restriction_le ((sheetLaw d ρ).restrict (incomingTail (R / 4))) q v
    (measurableSet_shell v R) (measurableSet_ballRegion v (2 * R))
    (shell_subset_ball v R) (B := 1) (by norm_num)
    (fun _ _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  simp only [mul_one] at h
  rw [← restrict_withDensity (measurableSet_incomingTail (R / 4))] at h
  exact h.trans ((mul_le_mul' le_rfl
    (tilted_tail_ball_bound hq₁ hq₂ hd hdmax (by linarith) (by positivity) hv hρ)).trans_eq
      (mul_assoc _ _ _).symm)

theorem normalized_hot_shell_bound {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (shell v R ∩ companionTail v (R / 2)) ≤
      ENNReal.ofReal (tiltConstant * Real.exp (-R ^ 2 / 4)) *
        ENNReal.ofReal (4 * L) * ballBound q (2 * R) := by
  have h := normalized_restriction_le (sheetLaw d ρ) q v
    ((measurableSet_shell v R).inter (measurableSet_companionTail v (R / 2)))
    (measurableSet_ballRegion v (2 * R))
    (fun y hy => shell_subset_ball v R hy.1) (Real.exp_nonneg (-R ^ 2 / 4))
    (fun y hy => gaussian_shell_decay (by linarith : 0 ≤ R) hy.2.le)
  exact h.trans ((mul_le_mul' le_rfl
    (tilted_ball_bound hq₁ hq₂ hd hdmax (by linarith) hv hρ)).trans_eq
      (mul_assoc _ _ _).symm)

theorem normalized_shell_bound_raw {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (shell v R) ≤
      ENNReal.ofReal tiltConstant * tailCoefficient L (R / 4) *
        (ballBound q (2 * R) + ballBound q (2 * R)) +
      ENNReal.ofReal (tiltConstant * Real.exp (-R ^ 2 / 4)) *
        ENNReal.ofReal (4 * L) * ballBound q (2 * R) := by
  calc
    _ ≤ normalizedMeasure (sheetLaw d ρ) q v
        ((shell v R ∩ (incomingTail (R / 4) ×ˢ univ)) ∪
          (shell v R ∩ companionTail v (R / 2))) := measure_mono (shell_subset_union v R)
    _ ≤ _ := (measure_union_le _ _).trans (add_le_add
      (normalized_cold_shell_bound hq₁ hq₂ hd hdmax hR hv hρ)
      (normalized_hot_shell_bound hq₁ hq₂ hd hdmax hR hv hρ))

theorem geometricTotalConstant_nonneg {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    0 ≤ GeometricSlice.geometricTotalConstant q := by
  unfold GeometricSlice.geometricTotalConstant
  exact mul_nonneg (by positivity) (GeometricSlice.geometricConstant_pos hq₁ hq₂).le

theorem shell_coefficient_bound {q L R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hL : 0 ≤ L) :
    ENNReal.ofReal tiltConstant * tailCoefficient L (R / 4) *
        (ballBound q (2 * R) + ballBound q (2 * R)) +
      ENNReal.ofReal (tiltConstant * Real.exp (-R ^ 2 / 4)) *
        ENNReal.ofReal (4 * L) * ballBound q (2 * R) ≤
      ENNReal.ofReal (shellConstant q L * R ^ 2 * Real.exp (-(3 / 32) * R ^ 2)) := by
  have hC := geometricTotalConstant_nonneg hq₁ hq₂
  have ht := tiltConstant_pos.le
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  unfold ballBound tailCoefficient
  rw [← htwo]
  repeat first
    | rw [← ENNReal.ofReal_mul (by positivity)]
    | rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-R ^ 2 / 4) ≤ Real.exp (-(3 / 32) * R ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg R]
  rw [show -(3 / 2) * (R / 4) ^ 2 = -(3 / 32) * R ^ 2 by ring]
  calc
    _ = (64 * tiltConstant * GeometricSlice.geometricTotalConstant q * L * R ^ 2) *
          Real.exp (-(3 / 32) * R ^ 2) +
        (32 * tiltConstant * GeometricSlice.geometricTotalConstant q * L * R ^ 2) *
          Real.exp (-R ^ 2 / 4) := by ring
    _ ≤ (64 * tiltConstant * GeometricSlice.geometricTotalConstant q * L * R ^ 2) *
          Real.exp (-(3 / 32) * R ^ 2) +
        (32 * tiltConstant * GeometricSlice.geometricTotalConstant q * L * R ^ 2) *
          Real.exp (-(3 / 32) * R ^ 2) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left he
        (by positivity : 0 ≤ 32 * tiltConstant *
          GeometricSlice.geometricTotalConstant q * L * R ^ 2))
    _ = _ := by unfold shellConstant; ring

/-- The full normalized kernel has a uniform Gaussian bound on every shell. -/
theorem normalized_shell_bound {q d R L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : AxialMoment ρ L) :
    normalizedMeasure (sheetLaw d ρ) q v (shell v R) ≤
      ENNReal.ofReal (shellConstant q L * R ^ 2 * Real.exp (-(3 / 32) * R ^ 2)) :=
  (normalized_shell_bound_raw hq₁ hq₂ hd hdmax hR hv hρ).trans
    (shell_coefficient_bound hq₁ hq₂ hρ.nonneg)

end BoltzmannNonuniqueness.UniformGain

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SheetIntervals
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Summing the normalized sheet kernel

The Gaussian shell estimate yields a finite constant independent of the
transverse width, the axial law, and the output velocity off the axis.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.SheetTotal

theorem summable_shellTerm : Summable shellTerm := by
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ) ^ 2 * Real.exp (-(3 / 32) * (n : ℝ) ^ 2)) := by
    apply (Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num : (0 : ℝ) < 3 / 32)).of_nonneg_of_le
    · intro n
      positivity
    · intro n
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply Real.exp_le_exp.mpr
      have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
        exact_mod_cast (show n ≤ n ^ 2 by simpa only [pow_two] using Nat.le_mul_self n)
      nlinarith
  convert! hbase.comp_injective Nat.succ_injective using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  simp only [Function.comp_def, Nat.cast_succ]
  rfl

theorem bound_lt_top (q L : ℝ) : bound q L < ∞ := by
  unfold bound ballBound
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
  · exact (summable_shellTerm.mul_left (shellConstant q L)).tsum_ofReal_lt_top

theorem cover_by_shells (v : Velocity) :
    (univ : Set Coordinates) ⊆ ballRegion v 2 ∪ ⋃ n : ℕ, shell v ((n : ℝ) + 1) := by
  intro y _
  by_cases hr : radius v y ≤ 2
  · apply Or.inl
    exact le_trans (le_add_of_nonneg_left (norm_nonneg y.1)) hr
  · apply Or.inr
    have hr₂ : 2 < radius v y := lt_of_not_ge hr
    let n := Nat.floor (radius v y / 2)
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    have hn : (n : ℝ) ≤ radius v y / 2 := Nat.floor_le (by linarith)
    have hn' : radius v y / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    constructor <;> linarith

/-- Uniform finiteness and the complete gain bound for an elementary sheet. -/
theorem normalized_total_bound {q d L : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8) {v : Velocity} (hv : transverse v ≠ 0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (hρ : AxialMoment ρ L) :
    normalizedChartGain (sheetLaw d ρ) q v ≤ bound q L := by
  rw [normalized_total_eq]
  calc
    _ ≤ normalizedMeasure (sheetLaw d ρ) q v
        (ballRegion v 2 ∪ ⋃ n : ℕ, shell v ((n : ℝ) + 1)) :=
      measure_mono (cover_by_shells v)
    _ ≤ normalizedMeasure (sheetLaw d ρ) q v (ballRegion v 2) +
        ∑' n : ℕ, normalizedMeasure (sheetLaw d ρ) q v (shell v ((n : ℝ) + 1)) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
    _ ≤ bound q L := by
      apply add_le_add (normalized_ball_bound hq₁ hq₂ hd hdmax (by norm_num) hv hρ)
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [shellTerm, mul_assoc] using
        normalized_shell_bound hq₁ hq₂ hd hdmax
          (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith [Nat.cast_nonneg (α := ℝ) n]) hv hρ

end BoltzmannNonuniqueness.SheetTotal

end

end

section

/-!
# Probability mixtures and domination by sheets

Elementary sheets are the actual Gaussian/atomic transverse product laws.
The uniform estimate survives probability mixing and measure domination.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.SheetClass

theorem elementary_bound {L q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    {c : Measure Velocity} (hc : IsElementary L c)
    {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain c q v ≤ SheetTotal.bound q L := by
  obtain ⟨d, ρ, hd, hdmax, hprob, hρ, rfl⟩ := hc
  exact SheetTotal.normalized_total_bound hq₁ hq₂ hd hdmax hv hρ

end BoltzmannNonuniqueness.SheetClass

end

end

section

/-!
# Transfer of the sheet estimate to the original gain

The only external hypothesis is the precisely stated published Carleman
identity. The sheet estimate itself has been proved from the geometric
slice and Gaussian-tail bounds.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.SheetClass

namespace BoltzmannNonuniqueness.SheetApplication

theorem gain_const_mul_right (c : Measure Velocity) (h : Velocity → ℝ≥0∞)
    (v : Velocity) {a : ℝ≥0∞} (ha : a ≠ ∞) :
    chartGain c (fun ξ => a * h ξ) v = a * chartGain c h v := by
  unfold chartGain
  simp_rw [lintegral_const_mul' a _ ha]
  have he : ∀ p : Velocity,
      ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹) *
          (a * ∫⁻ z : ℝ, ∫⁻ s : ℝ, h (PlaneChart.chart v p z s)) =
        a * (ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹) *
          ∫⁻ z : ℝ, ∫⁻ s : ℝ, h (PlaneChart.chart v p z s)) := by
    intro p
    ac_rfl
  simp_rw [he]
  rw [lintegral_const_mul' a _ ha]
  ac_rfl

theorem gain_H_eq (c : Measure Velocity) (q : ℝ) (v : Velocity) :
    chartGain c (fun ξ => ENNReal.ofReal (H q ξ)) v =
      ENNReal.ofReal (H q v) * normalizedChartGain c q v := by
  have he : (fun ξ => ENNReal.ofReal (H q ξ)) =
      (fun ξ => ENNReal.ofReal (H q v) * ENNReal.ofReal (H q ξ / H q v)) := by
    funext ξ
    rw [← ENNReal.ofReal_mul (H_nonneg q v)]
    congr 1
    field_simp [(H_pos q v).ne']
  rw [he, gain_const_mul_right c _ v ENNReal.ofReal_ne_top]
  rfl

theorem ae_transverse_ne_zero : ∀ᵐ v : Velocity ∂volume, transverse v ≠ 0 := by
  rw [ae_iff]
  simp only [not_not]
  have he : {v : Velocity | transverse v = 0} =
      split ⁻¹' ((univ : Set ℝ) ×ˢ ({0} : Set Transverse)) := by
    ext v
    simp only [mem_preimage, split_apply, mem_prod, mem_univ, mem_singleton_iff, true_and]
    rfl
  rw [he, split_measurePreserving.measure_preimage
    (MeasurableSet.univ.prod (measurableSet_singleton 0)).nullMeasurableSet]
  rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod]
  simp

end BoltzmannNonuniqueness.SheetApplication

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotQuadraticGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The truncated hot rectangle in physical velocity coordinates -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.HotDiskEstimate
open BoltzmannNonuniqueness.HotChartBalls

namespace BoltzmannNonuniqueness.HotRectangleDensity

theorem join_measurePreserving :
    MeasurePreserving join ((volume : Measure Transverse).prod volume) volume := by
  have hs : MeasurePreserving split.symm
      ((volume : Measure ℝ).prod (volume : Measure Transverse)) volume := by
    simpa only [Measure.volume_eq_prod] using
      (MeasurePreserving.symm split split_measurePreserving)
  exact (Measure.measurePreserving_swap (μ := volume (α := Transverse))
    (ν := volume (α := ℝ))).trans hs

end BoltzmannNonuniqueness.HotRectangleDensity

end

end

section

/-!
# The quadratic hot-gain bound

The geometric shell estimates and their summation transfer through the
Carleman identity to the original hard-sphere collision variables.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.HotMixedGain

namespace BoltzmannNonuniqueness.HotApplication

theorem realBound_pos (q : ℝ) : 0 < realBound q := by
  unfold realBound
  positivity

end BoltzmannNonuniqueness.HotApplication

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MixedRealGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Real symmetric mixed gain and its nonnegative bounds -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.MixedRealGain

theorem integrand_nonneg {f g : Velocity → ℝ}
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w) (v : Velocity) (p : Velocity × Sphere) :
    0 ≤ integrand f g v p :=
  mul_nonneg (div_nonneg (collisionKernel_nonneg _ _ _) (by norm_num))
    (add_nonneg (mul_nonneg (hf _) (hg _)) (mul_nonneg (hg _) (hf _)))

theorem integrand_measurable {f g : Velocity → ℝ} (hf : Measurable f) (hg : Measurable g)
    (v : Velocity) : Measurable (integrand f g v) := by
  have hl : Measurable (fun p : Velocity × Sphere => scatterLeft v p.1 p.2) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hr : Measurable (fun p : Velocity × Sphere => scatterRight v p.1 p.2) := by
    unfold scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : Velocity × Sphere => collisionKernel v p.1 p.2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact (hk.div_const 2).mul (((hf.comp hl).mul (hg.comp hr)).add ((hg.comp hl).mul (hf.comp hr)))

theorem nonnegative_eq_lintegral {f g : Velocity → ℝ}
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w) (v : Velocity) :
    nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (g w)) v =
      ∫⁻ p, ENNReal.ofReal (integrand f g v p) ∂gainPairMeasure := by
  unfold nonnegativeGain
  apply lintegral_congr
  intro p
  have he : ENNReal.ofReal (collisionKernel v p.1 p.2) / 2 =
      ENNReal.ofReal (collisionKernel v p.1 p.2 / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [← ENNReal.ofReal_mul (hf _), ← ENNReal.ofReal_mul (hg _),
    ← ENNReal.ofReal_add (mul_nonneg (hf _) (hg _)) (mul_nonneg (hg _) (hf _)), he,
    ← ENNReal.ofReal_mul (div_nonneg (collisionKernel_nonneg _ _ _) (by norm_num))]
  rfl

theorem integrable_of_bound {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w) {B : ℝ} (v : Velocity)
    (hb : nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (g w)) v ≤
      ENNReal.ofReal B) : Integrable (integrand f g v) gainPairMeasure := by
  refine ⟨(integrand_measurable hfm hgm v).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (integrand_nonneg hf hg v)),
    ← nonnegative_eq_lintegral hf hg v]
  exact hb.trans_lt ENNReal.ofReal_lt_top

theorem gain_le_of_bound {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w) {B : ℝ} (hB : 0 ≤ B) (v : Velocity)
    (hb : nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (g w)) v ≤
      ENNReal.ofReal B) : gain f g v ≤ B := by
  have hi := integrable_of_bound hfm hgm hf hg v hb
  have he : gain f g v =
      (nonnegativeGain (fun w => ENNReal.ofReal (f w)) (fun w => ENNReal.ofReal (g w)) v).toReal := by
    rw [nonnegative_eq_lintegral hf hg]
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (integrand_nonneg hf hg v)) hi.aestronglyMeasurable
  rw [he]
  simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

theorem integrand_mono {f g F G : Velocity → ℝ}
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfF : ∀ w, f w ≤ F w) (hgG : ∀ w, g w ≤ G w) (v : Velocity) (p : Velocity × Sphere) :
    integrand f g v p ≤ integrand F G v p := by
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (collisionKernel_nonneg _ _ _) (by norm_num))
  exact add_le_add (mul_le_mul (hfF _) (hgG _) (hg _) ((hf _).trans (hfF _)))
    (mul_le_mul (hgG _) (hfF _) (hf _) ((hg _).trans (hgG _)))

theorem integrable_of_le {f g F G : Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfF : ∀ w, f w ≤ F w) (hgG : ∀ w, g w ≤ G w) (v : Velocity)
    (hi : Integrable (integrand F G v) gainPairMeasure) :
    Integrable (integrand f g v) gainPairMeasure := by
  apply hi.mono' (integrand_measurable hfm hgm v).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg hf hg v p)]
  exact integrand_mono hf hg hfF hgG v p

theorem gain_mono {f g F G : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfF : ∀ w, f w ≤ F w) (hgG : ∀ w, g w ≤ G w) (v : Velocity)
    (hi : Integrable (integrand F G v) gainPairMeasure) : gain f g v ≤ gain F G v :=
  integral_mono (integrable_of_le hfm hgm hf hg hfF hgG v hi) hi (integrand_mono hf hg hfF hgG v)

end BoltzmannNonuniqueness.MixedRealGain

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarriers
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual unshifted cold-jet density and its mass bound -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetMaskMeasure
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetPrototype

theorem axialAmplitude_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (γ z : ℝ) :
    0 ≤ axialAmplitude K γ s z := by
  apply indicator_nonneg
  intro z _
  exact mul_nonneg (div_nonneg hK hs) (S_pos _).le

theorem spatial_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (η γ : ℝ) (a : Bool) (x : Space) :
    0 ≤ spatial η K γ s a x :=
  mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
    (axialAmplitude_nonneg hK hs γ _)

theorem density_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (η α γ : ℝ) (a : Bool) (p : Phase) : 0 ≤ density η K α γ s d a p :=
  mul_nonneg (spatial_nonneg hK hs η γ a _)
    (JetThermalLaw.density_nonneg hd _ _)

theorem measurable_spatial (η K γ s : ℝ) (a : Bool) : Measurable (spatial η K γ s a) := by
  unfold spatial axialAmplitude
  exact (((measurable_const.indicator (measurableSet_mask η s a)).comp measurable_fst).mul
    (((continuous_const.mul (continuous_S.comp
      ((continuous_const.mul continuous_id).div_const s))).measurable.indicator measurableSet_Ioo).comp
      measurable_snd))

theorem measurable_center (α γ s : ℝ) (a : Bool) : Measurable (center α γ s a) := by
  change Measurable (fun z => SheetMeasures.join (0, AxialFlow.profile (sign a) α γ s z))
  exact SheetMeasures.join.measurable.comp
    (measurable_const.prodMk (AxialFlow.continuous_profile _ _ _ _).measurable)

theorem measurable_density (η K α γ s d : ℝ) (a : Bool) :
    Measurable (density η K α γ s d a) := by
  unfold density JetThermalLaw.density JetThermalLaw.scaled
  have hc : Measurable (fun p : Phase => center α γ s a p.1.2) :=
    (measurable_center α γ s a).comp (measurable_snd.comp measurable_fst)
  have hv : Measurable (fun p : Phase => d⁻¹ • (p.2 - center α γ s a p.1.2)) :=
    (measurable_const : Measurable (fun _ : Phase => d⁻¹)).smul (measurable_snd.sub hc)
  exact ((measurable_spatial η K γ s a).comp measurable_fst).mul
    (measurable_const.mul (JetThermalKernel.J_smooth.continuous.measurable.comp
      hv))

end BoltzmannNonuniqueness.JetPrototype

end

end

section

/-! # The actual Gaussian barrier and free-core domination -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetAxialWeight
open BoltzmannNonuniqueness.JetCoreFlight

namespace BoltzmannNonuniqueness.JetBarrier

theorem barrier_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (η α γ t : ℝ) (a : Bool) (p : JetPrototype.Phase) : 0 ≤ barrier η K α γ s d t a p := by
  unfold barrier
  have := JetThermalKernel.bound_pos
  positivity

end BoltzmannNonuniqueness.JetBarrier

end

end

section

/-! # Self-collision and the uniform loss-frequency bound of the actual barrier -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetBarrierCollision

theorem massScale_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s)
    (η α γ d t : ℝ) (a : Bool) (x : Space) : 0 ≤ massScale η K α γ s d t a x := by
  unfold massScale
  have := JetThermalKernel.bound_pos
  positivity

theorem barrier_eq_density {d : ℝ} (hd : 0 < d)
    (η K α γ s t : ℝ) (a : Bool) (x : Space) (v : Velocity) :
    barrier η K α γ s d t a (x, v) =
      GaussianFrequency.density (massScale η K α γ s d t a x) (2 - t) d
        (centerVelocity α γ s t a x) v := by
  rw [GaussianFrequency.density_eq_gaussian hd]
  unfold barrier exponent gaussian massScale
  have he : t - (2 - t) * ‖v - centerVelocity α γ s t a x‖ ^ 2 / d ^ 2 -
      (1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t) =
      (t - (1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t)) +
      (-( (2 - t) / d ^ 2) * ‖v - centerVelocity α γ s t a x‖ ^ 2) := by ring
  dsimp only
  rw [he, Real.exp_add]
  ring

theorem measurable_velocity {d : ℝ} (hd : 0 < d)
    (η K α γ s t : ℝ) (a : Bool) (x : Space) :
    Measurable (fun v => barrier η K α γ s d t a (x, v)) := by
  simp_rw [barrier_eq_density hd, GaussianFrequency.density_eq_gaussian hd]
  unfold gaussian
  fun_prop

theorem massScale_le {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space) :
    massScale η K α γ s d t a x ≤ Real.exp 4 * JetThermalKernel.bound * (K / s) := by
  have hD : 0 ≤ distanceSquared η α γ s t a x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he : t - (1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t) ≤ 1 := by
    have : 0 ≤ (1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t) := by positivity
    linarith
  have hc : 0 ≤ Real.exp 3 * JetThermalKernel.bound * (K / s) := by
    have := JetThermalKernel.bound_pos
    positivity
  calc
    _ ≤ (Real.exp 3 * JetThermalKernel.bound) * (K / s) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hc
    _ = _ := by
      have he4 : Real.exp (3 : ℝ) * Real.exp 1 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
      calc
        _ = (Real.exp 3 * Real.exp 1) * JetThermalKernel.bound * (K / s) := by ring
        _ = _ := by rw [he4]

theorem frequencyConstant_nonneg : 0 ≤ frequencyConstant := by
  unfold frequencyConstant
  have := JetGaussianMoments.mass_nonneg
  have := JetGaussianMoments.moment_nonneg
  have := JetThermalKernel.bound_pos
  positivity

end BoltzmannNonuniqueness.JetBarrierCollision

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetPeriodicDatum
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The free cold core in Eulerian coordinates -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetFreeTransport

theorem free_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (η α γ t : ℝ) (a : Bool) (p : JetPrototype.Phase) : 0 ≤ free η K α γ s d t a p :=
  density_nonneg hK hs hd η α γ a _

theorem measurable_free (η K α γ s d t : ℝ) (a : Bool) :
    Measurable (free η K α γ s d t a) := by
  apply (measurable_density η K α γ s d a).comp
  unfold flight transverse axial
  fun_prop

end BoltzmannNonuniqueness.JetFreeTransport

end

end

section

/-! # A uniform, explicit coefficient for cold-color comparison -/

noncomputable section

open BoltzmannNonuniqueness.JetBarrierCollision

namespace BoltzmannNonuniqueness.JetComparisonCoefficient

theorem coefficient_ge_one {K : ℝ} (hK : 0 ≤ K) : 1 ≤ coefficient K := by
  unfold coefficient
  nlinarith [mul_nonneg frequencyConstant_nonneg hK]

end BoltzmannNonuniqueness.JetComparisonCoefficient

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetSupersolutions
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual free-core plus Gaussian supersolution -/

noncomputable section

open MeasureTheory Filter
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetFreeTransport
open BoltzmannNonuniqueness.JetBarrierCollision
open BoltzmannNonuniqueness.JetComparisonCoefficient

namespace BoltzmannNonuniqueness.JetSupersolution

theorem epsilon_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d) :
    0 ≤ epsilon K s d :=
  div_nonneg (mul_nonneg (zero_le_one.trans (coefficient_ge_one hK)) hd.le) hs.le

theorem nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (η α γ t : ℝ) (a : Bool) (p : JetPrototype.Phase) : 0 ≤ U η K α γ s d t a p :=
  add_nonneg (free_nonneg hK hs.le hd.le η α γ t a p)
    (mul_nonneg (epsilon_nonneg hK hs hd) (barrier_nonneg hK hs.le hd.le η α γ t a p))

theorem measurable_velocity {d : ℝ} (hd : 0 < d) (η K α γ s t : ℝ) (a : Bool) (x : Space) :
    Measurable (fun v => U η K α γ s d t a (x, v)) := by
  exact ((measurable_free η K α γ s d t a).comp (measurable_const.prodMk measurable_id)).add
    (measurable_const.mul (JetBarrierCollision.measurable_velocity hd η K α γ s t a x))

end BoltzmannNonuniqueness.JetSupersolution

end

end

section

/-! # The full velocity measure under the thermal-coordinate map -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.AxialDerivative
open BoltzmannNonuniqueness.JetCoreMap
open BoltzmannNonuniqueness.JetCoreJacobian

namespace BoltzmannNonuniqueness.JetCoreMeasure

theorem jacobian_measurable {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (σ d z : ℝ) : Measurable (jacobian σ α γ s d t z) := by
  have hf : Measurable (foot σ α γ s t) := (foot_lipschitzWith hα hγ hs ht).continuous.measurable
  have hS := JetAxialWeight.continuous_S.measurable
  unfold jacobian A sourceFoot
  fun_prop

theorem axial_measurePreserving {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z : ℝ) :
    MeasurePreserving (axialMap σ α γ s d t z)
      (volume.withDensity (fun w => ENNReal.ofReal (jacobian σ α γ s d t z w))) volume := by
  let hhome := axialHomeomorph hα hγ hs ht hd.ne' σ z
  have hm := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure ℝ)
    (s := univ) MeasurableSet.univ.nullMeasurableSet
    (fun w _ => (axialMap_derivative hα hγ hs ht σ d z w).hasDerivWithinAt.hasFDerivWithinAt)
    hhome.injective.injOn
  have hr : axialMap σ α γ s d t z '' univ = univ := Set.image_univ ▸ hhome.surjective.range_eq
  rw [hr, Measure.restrict_univ] at hm
  simp only [ContinuousLinearMap.det_toSpanSingleton] at hm
  change Measure.map (axialMap σ α γ s d t z)
    (volume.withDensity (fun w => ENNReal.ofReal (|jacobian σ α γ s d t z w|))) = volume at hm
  simp only [abs_of_pos (jacobian_pos hα hγ hs hd ht σ z _)] at hm
  exact ⟨hhome.continuous.measurable, hm⟩

theorem transverse_measurePreserving {d : ℝ} (hd : 0 < d) :
    MeasurePreserving (fun w : Transverse => d • w)
      (ENNReal.ofReal (d ^ 2) • (volume : Measure Transverse)) volume := by
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_smul, Measure.map_addHaar_smul volume hd.ne', smul_smul]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  rw [← ENNReal.ofReal_mul (sq_nonneg d), abs_of_pos (inv_pos.mpr (sq_pos_of_pos hd)),
    mul_inv_cancel₀ (ne_of_gt (sq_pos_of_pos hd)), ENNReal.ofReal_one, one_smul]

theorem velocity_measurePreserving {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z : ℝ) :
    MeasurePreserving (velocityMap σ α γ s d t z) (parameterMeasure σ α γ s d t z) volume := by
  change MeasurePreserving (SheetMeasures.join ∘
    Prod.map (fun w : Transverse => d • w) (axialMap σ α γ s d t z)) _ _
  exact HotRectangleDensity.join_measurePreserving.comp
    ((transverse_measurePreserving hd).prod (axial_measurePreserving hα hγ hs hd ht σ z))

theorem parameterMeasure_eq {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (σ d z : ℝ) :
    parameterMeasure σ α γ s d t z =
      ((volume : Measure Transverse).prod volume).withDensity
        (fun w => ENNReal.ofReal (d ^ 2 * jacobian σ α γ s d t z w.2)) := by
  unfold parameterMeasure
  rw [← withDensity_const, prod_withDensity measurable_const (jacobian_measurable hα hγ hs ht σ d z).ennreal_ofReal]
  congr 1
  funext w
  rw [ENNReal.ofReal_mul (sq_nonneg d)]


theorem map_withDensity {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z : ℝ) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    ((parameterMeasure σ α γ s d t z).withDensity
      (fun w => f (velocityMap σ α γ s d t z w))).map (velocityMap σ α γ s d t z) =
      volume.withDensity f := by
  have h := velocity_measurePreserving hα hγ hs hd ht σ z
  ext B hB
  rw [Measure.map_apply h.measurable hB,
    withDensity_apply _ (hB.preimage h.measurable), withDensity_apply _ hB,
    ← lintegral_indicator (hB.preimage h.measurable), ← lintegral_indicator hB]
  convert h.lintegral_comp (hf.indicator hB) using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr
  intro w
  rfl

end BoltzmannNonuniqueness.JetCoreMeasure

end

end

section

/-! # The exact compressed density of a transported cold core -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetCoreMap
open BoltzmannNonuniqueness.JetCoreJacobian
open BoltzmannNonuniqueness.JetCoreMeasure
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermal_argument {α d : ℝ} (hα : 0 ≤ α) (hd : d ≠ 0)
    (γ s t : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    d⁻¹ • (velocityMap (sign a) α γ s d t x.2 w -
      center α γ s a (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2)) =
      SheetMeasures.join w := by
  have ha := axialMap_spec hα (sign a) γ s d t x.2 w.2
  apply split.injective
  rw [split_apply, split_apply]
  apply Prod.ext
  · change d⁻¹ * (axial (velocityMap (sign a) α γ s d t x.2 w) -
        axial (center α γ s a (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2))) =
        axial (SheetMeasures.join w)
    simp only [velocityMap, JetPrototype.center, PlaneChart.axial_join]
    change d⁻¹ * (axialMap (sign a) α γ s d t x.2 w.2 -
        AxialFlow.profile (sign a) α γ s (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2)) = w.2
    have hz : axialMap (sign a) α γ s d t x.2 w.2 -
        AxialFlow.profile (sign a) α γ s (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) =
        d * w.2 := by linarith
    rw [hz]
    field_simp
  · have ht : ∀ (c : ℝ) (v : Velocity), transverse (c • v) = c • transverse v := by
      intro c v
      apply (WithLp.ext_iff 2).mpr
      rfl
    rw [ht, PlaneChart.transverse_sub]
    simp only [velocityMap, JetPrototype.center, PlaneChart.transverse_join, sub_zero, smul_smul,
      inv_mul_cancel₀ hd, one_smul]
    exact (PlaneChart.transverse_join w.1 w.2).symm

theorem density_identity {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (η K : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    (d ^ 2 * jacobian (sign a) α γ s d t x.2 w.2) *
      JetFreeTransport.free η K α γ s d t a (x, velocityMap (sign a) α γ s d t x.2 w) =
      weight η K α γ s d t a x w := by
  have hthermal := thermal_argument hα hd.ne' γ s t a x w
  have hfoot := sourceFoot_eq (sign a) α γ s d t x.2 w.2
  have hf : JetFreeTransport.free η K α γ s d t a
        (x, velocityMap (sign a) α γ s d t x.2 w) =
      spatial η K γ s a (x.1 - t • (d • w.1),
        x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) *
        ((d ^ 3)⁻¹ * JetThermalKernel.J (SheetMeasures.join w)) := by
    unfold JetFreeTransport.free density JetThermalLaw.density JetThermalLaw.scaled
    simp only [JetBarrier.flight, velocityMap, PlaneChart.transverse_join, PlaneChart.axial_join,
      neg_smul, neg_mul, ← sub_eq_add_neg]
    unfold velocityMap at hthermal
    rw [hthermal]
  rw [hf]
  unfold spatial axialAmplitude weight
  rw [hfoot]
  by_cases hy : x.1 - t • (d • w.1) ∈ JetGeometry.mask η s a
  · by_cases hz : x.2 - t * axialMap (sign a) α γ s d t x.2 w.2 ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
    · simp only [indicator_of_mem hy, indicator_of_mem hz, one_mul]
      have hc : d ^ 2 * jacobian (sign a) α γ s d t x.2 w.2 *
          ((K / s) * S (γ * (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) / s) * (d ^ 3)⁻¹) =
          compressed K α γ s t (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) := by
        have ha := AxialDerivative.A_nonneg hα hγ hs.le
          (sourceFoot (sign a) α γ s d t x.2 w.2)
        have hden : 1 + t * AxialDerivative.A α γ s
            (sourceFoot (sign a) α γ s d t x.2 w.2) ≠ 0 := by positivity
        have hden' : s + t * α * γ * S
            (γ * (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) / s) ≠ 0 := by
          have := S_pos (γ * (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) / s)
          positivity
        unfold jacobian AxialDerivative.A at hden ⊢
        rw [hfoot] at hden ⊢
        unfold compressed
        field_simp
      calc
        _ = (d ^ 2 * jacobian (sign a) α γ s d t x.2 w.2 *
          ((K / s) * S (γ * (x.2 - t * axialMap (sign a) α γ s d t x.2 w.2) / s) * (d ^ 3)⁻¹)) *
          JetThermalKernel.J (SheetMeasures.join w) := by ring
        _ = _ := by rw [hc]
    · simp only [indicator_of_notMem hz, mul_zero, zero_mul]
  · simp only [indicator_of_notMem hy, mul_zero, zero_mul]


theorem weight_bound {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η d : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    weight η K α γ s d t a x w ≤
      ((K * max 1 (α * γ)⁻¹) / (s + t)) * JetThermalKernel.J (SheetMeasures.join w) := by
  have hc := compressed_bound hK hα hγ hs ht
    (sourceFoot (sign a) α γ s d t x.2 w.2)
  have hj := JetThermalKernel.J_nonneg (SheetMeasures.join w)
  unfold weight
  by_cases hy : x.1 - t • (d • w.1) ∈ JetGeometry.mask η s a
  · by_cases hz : sourceFoot (sign a) α γ s d t x.2 w.2 ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
    · simp only [indicator_of_mem hy, indicator_of_mem hz, one_mul]
      exact mul_le_mul_of_nonneg_right hc hj
    · simp only [indicator_of_notMem hz, mul_zero, zero_mul]
      positivity
  · simp only [indicator_of_notMem hy, zero_mul]
    positivity

theorem measure_identity {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (η K : ℝ) (a : Bool) (x : Space) :
    (((volume : Measure Transverse).prod volume).withDensity
      (fun w => ENNReal.ofReal (weight η K α γ s d t a x w))).map
        (velocityMap (sign a) α γ s d t x.2) =
      volume.withDensity (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, v))) := by
  have hf : Measurable (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, v))) :=
    ((JetFreeTransport.measurable_free η K α γ s d t a).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hmap := JetCoreMeasure.map_withDensity hα hγ hs hd ht (sign a) x.2 hf
  have hmeas := (velocity_measurePreserving hα hγ hs hd ht (sign a) x.2).measurable
  have heq : (parameterMeasure (sign a) α γ s d t x.2).withDensity
      (fun w => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a
        (x, velocityMap (sign a) α γ s d t x.2 w))) =
      ((volume : Measure Transverse).prod volume).withDensity
        (fun w => ENNReal.ofReal (weight η K α γ s d t a x w)) := by
    rw [parameterMeasure_eq hα hγ hs ht]
    have hjm : Measurable (fun w : Transverse × ℝ =>
        ENNReal.ofReal (d ^ 2 * jacobian (sign a) α γ s d t x.2 w.2)) :=
      (measurable_const.mul ((jacobian_measurable hα hγ hs ht (sign a) d x.2).comp
        measurable_snd)).ennreal_ofReal
    have hfg : Measurable (fun w => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a
        (x, velocityMap (sign a) α γ s d t x.2 w))) := hf.comp hmeas
    rw [← withDensity_mul _ hjm hfg]
    congr 1
    funext w
    change ENNReal.ofReal (d ^ 2 * jacobian (sign a) α γ s d t x.2 w.2) * _ = _
    rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg d)
      (jacobian_pos hα hγ hs hd ht (sign a) x.2 w.2).le),
      density_identity hα hγ hs hd ht]
  rw [heq] at hmap
  exact hmap

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Gaussian parameter laws for the actual axial core map -/

noncomputable section

open MeasureTheory
open scoped NNReal
open BoltzmannNonuniqueness.AxialFlow
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetAxialLaw

theorem axialMap_abs_le {α d : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d)
    (σ γ s t z w : ℝ) : |axialMap σ α γ s d t z w| ≤ (|σ| + α) + d * |w| := by
  have hv := AxialTransport.velocity_abs_le (σ := σ) (γ := γ) (s := s)
    (t := t) (z := z - t * d * w) hα
  have h := abs_add_le (d * w) (velocity σ α γ s t (z - t * d * w))
  rw [abs_mul, abs_of_nonneg hd] at h
  unfold axialMap
  linarith

theorem probability (σ α γ s d t z : ℝ) : IsProbabilityMeasure (law σ α γ s d t z) := by
  unfold law
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem moment {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (hdmax : d ≤ 1 / 16) (ht : 0 ≤ t) (σ z : ℝ) :
    SheetMeasures.AxialMoment (law σ α γ s d t z)
      (2 * Real.exp (16 * (|σ| + α) ^ 2)) := by
  have hm : Measurable (axialMap σ α γ s d t z) :=
    (axialHomeomorph hα hγ hs ht hd.ne' σ z).continuous.measurable
  have hb := axialMap_abs_le hα hd.le σ γ s t z
  exact ⟨GaussianSheets.integrable_axialLaw_exp (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)
      (by norm_num) (by positivity) hd.le hdmax hm hb,
    GaussianSheets.integral_axialLaw_exp_le (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)
      (by norm_num) (by positivity) hd.le hdmax hm hb⟩

end BoltzmannNonuniqueness.JetAxialLaw

end

end

section

/-! # Gaussian product domination in the actual core coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture
open BoltzmannNonuniqueness.JetCoreMap
open BoltzmannNonuniqueness.JetCoreMeasure

namespace BoltzmannNonuniqueness.JetGaussianProduct

theorem density_eq (w : Transverse × ℝ) :
    density w = (Real.pi * Real.sqrt Real.pi)⁻¹ * Real.exp (-‖SheetMeasures.join w‖ ^ 2) := by
  unfold density
  rw [GaussianSheets.original_gaussian_density]
  simp only [gaussianDensity, one_pow, mul_one, div_one]
  rw [SheetMeasures.norm_join_sq]
  rw [show -(‖w.1‖ ^ 2 + w.2 ^ 2) = -‖w.1‖ ^ 2 + -w.2 ^ 2 by ring, Real.exp_add]
  field_simp

theorem density_nonneg (w : Transverse × ℝ) : 0 ≤ density w := by
  rw [density_eq]
  positivity

theorem kernel_bound (w : Transverse × ℝ) :
    JetThermalKernel.J (SheetMeasures.join w) ≤ coefficient * density w := by
  have hC : 0 ≤ coefficient := by
    unfold coefficient
    have := JetThermalKernel.bound_pos
    positivity
  by_cases hw : 1 ≤ ‖SheetMeasures.join w‖
  · rw [JetThermalKernel.J_zero hw]
    exact mul_nonneg hC (density_nonneg w)
  · have hnorm : ‖SheetMeasures.join w‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (SheetMeasures.join w)]
    have he : 1 ≤ Real.exp (1 - ‖SheetMeasures.join w‖ ^ 2) :=
      Real.one_le_exp_iff.mpr (by linarith)
    calc
      _ ≤ JetThermalKernel.bound := JetThermalKernel.J_le _
      _ ≤ JetThermalKernel.bound * Real.exp (1 - ‖SheetMeasures.join w‖ ^ 2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he JetThermalKernel.bound_pos.le
      _ = coefficient * density w := by
        rw [density_eq, sub_eq_add_neg, Real.exp_add]
        unfold coefficient
        field_simp

theorem gaussian_scaling {d : ℝ} (hd : 0 < d) (w : Transverse) :
    d ^ 2 * gaussianDensity d (d • w) = gaussianDensity 1 w := by
  unfold gaussianDensity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd]
  have he : -(d * ‖w‖) ^ 2 / d ^ 2 = -‖w‖ ^ 2 := by field_simp
  rw [he]
  simp only [one_pow, mul_one, div_one]
  field_simp

theorem gaussianLaw_map_smul {d : ℝ} (hd : 0 < d) :
    (gaussianLaw 1).map (fun w => d • w) = gaussianLaw d := by
  have hm := transverse_measurePreserving hd
  have hf : Measurable (fun w => ENNReal.ofReal (gaussianDensity d w)) := by
    unfold gaussianDensity
    fun_prop
  have hfg : Measurable (fun w => ENNReal.ofReal (gaussianDensity d (d • w))) :=
    hf.comp hm.measurable
  have heq : gaussianLaw 1 =
      (ENNReal.ofReal (d ^ 2) • (volume : Measure Transverse)).withDensity
        (fun w => ENNReal.ofReal (gaussianDensity d (d • w))) := by
    rw [withDensity_smul_measure, ← withDensity_smul _ hfg]
    unfold gaussianLaw
    congr 1
    funext w
    change ENNReal.ofReal (gaussianDensity 1 w) = ENNReal.ofReal (d ^ 2) * _
    rw [← ENNReal.ofReal_mul (sq_nonneg d), gaussian_scaling hd]
  rw [heq]
  ext B hB
  rw [Measure.map_apply hm.measurable hB,
    withDensity_apply _ (hB.preimage hm.measurable), gaussianLaw, withDensity_apply _ hB,
    ← lintegral_indicator (hB.preimage hm.measurable), ← lintegral_indicator hB]
  convert hm.lintegral_comp (hf.indicator hB) using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr
  intro w
  rfl

theorem parameterLaw_density : parameterLaw =
    ((volume : Measure Transverse).prod volume).withDensity (fun w => ENNReal.ofReal (density w)) := by
  unfold parameterLaw gaussianLaw
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)]
  rw [prod_withDensity (by unfold gaussianDensity; fun_prop) (measurable_gaussianPDF 0 (1 / 2))]
  congr 1
  funext w
  rw [density, ENNReal.ofReal_mul (gaussianDensity_nonneg _ _)]
  rfl

theorem parameterLaw_map {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 ≤ t) (σ z : ℝ) :
    parameterLaw.map (velocityMap σ α γ s d t z) =
      SheetMeasures.sheetLaw d (JetAxialLaw.law σ α γ s d t z) := by
  have hm : Measurable (axialMap σ α γ s d t z) := (axialHomeomorph hα hγ hs ht hd.ne' σ z).continuous.measurable
  let : IsProbabilityMeasure (gaussianLaw 1) := gaussianLaw_isProbabilityMeasure (by norm_num)
  unfold parameterLaw SheetMeasures.sheetLaw SheetMeasures.transverseLaw JetAxialLaw.law
    GaussianSheets.axialLaw
  rw [if_pos hm.aemeasurable]
  rw [ite_eq_right hd.ne', ← gaussianLaw_map_smul hd, Measure.map_prod_map _ _ (by fun_prop) hm,
    Measure.map_map SheetMeasures.join.measurable (by fun_prop)]
  rfl

end BoltzmannNonuniqueness.JetGaussianProduct

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetEnvelopeTimeIntegral
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The transported core is dominated by an admissible Gaussian sheet -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetCoreMeasure
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem amplitude_nonneg {K s t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (ht : 0 ≤ t) (α γ : ℝ) :
    0 ≤ amplitude K α γ s t := by
  have := JetThermalKernel.bound_pos
  unfold amplitude JetGaussianProduct.coefficient
  positivity

theorem parameter_bound {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η d : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    JetCoreDensity.weight η K α γ s d t a x w ≤
      amplitude K α γ s t * JetGaussianProduct.density w := by
  apply (JetCoreDensity.weight_bound hK hα hγ hs ht η d a x w).trans
  calc
    _ ≤ ((K * max 1 (α * γ)⁻¹) / (s + t)) *
        (JetGaussianProduct.coefficient * JetGaussianProduct.density w) :=
      mul_le_mul_of_nonneg_left (JetGaussianProduct.kernel_bound w) (by positivity)
    _ = _ := by unfold amplitude; ring

theorem measure_domination {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (η : ℝ) (a : Bool) (x : Space) :
    volume.withDensity (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, v))) ≤
      ENNReal.ofReal (amplitude K α γ s t) •
        SheetMeasures.sheetLaw d (JetAxialLaw.law (sign a) α γ s d t x.2) := by
  rw [← JetCoreDensity.measure_identity hα.le hγ.le hs hd ht,
    ← JetGaussianProduct.parameterLaw_map hα.le hγ.le hs hd ht]
  have hm := (velocity_measurePreserving hα.le hγ.le hs hd ht (sign a) x.2).measurable
  rw [← Measure.map_smul]
  apply Measure.map_mono _ hm
  rw [JetGaussianProduct.parameterLaw_density]
  have hg : Measurable (fun w => ENNReal.ofReal (JetGaussianProduct.density w)) := by
    unfold JetGaussianProduct.density GaussianDiskMixture.gaussianDensity
    fun_prop
  rw [← withDensity_smul _ hg]
  apply withDensity_mono
  filter_upwards [] with w
  change ENNReal.ofReal (JetCoreDensity.weight η K α γ s d t a x w) ≤
    ENNReal.ofReal (amplitude K α γ s t) * ENNReal.ofReal (JetGaussianProduct.density w)
  rw [← ENNReal.ofReal_mul (amplitude_nonneg hK hs ht α γ)]
  exact ENNReal.ofReal_le_ofReal (parameter_bound hK hα hγ hs ht η d a x w)

theorem normalized_gain_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1 / 16) (ht : 0 ≤ t)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool) (x : Space)
    {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain
      (volume.withDensity (fun p => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, p)))) q v ≤
      ENNReal.ofReal (amplitude K α γ s t) *
        SheetTotal.bound q (2 * Real.exp (16 * (|sign a| + α) ^ 2)) := by
  have hp := JetAxialLaw.probability (sign a) α γ s d t x.2
  have he : SheetClass.IsElementary (2 * Real.exp (16 * (|sign a| + α) ^ 2))
      (SheetMeasures.sheetLaw d (JetAxialLaw.law (sign a) α γ s d t x.2)) :=
    ⟨d, JetAxialLaw.law (sign a) α γ s d t x.2, hd.le, by linarith, hp,
      JetAxialLaw.moment hα.le hγ.le hs hd hdmax ht (sign a) x.2, rfl⟩
  apply (chartGain_mono_measure (measure_domination hK hα hγ hs hd ht η a x) _ v).trans
  rw [chartGain_smul_measure]
  exact mul_le_mul' le_rfl (SheetClass.elementary_bound hq₁ hq₂ he hv)


end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetCoreConvergence
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A centered thermal Gaussian as an admissible product sheet -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreMeasure
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetAffineSheet

theorem affineMap_eq (d u : ℝ) : affineMap d u = velocityMap u 0 0 1 d 0 0 := by
  funext w
  have hv := AxialFlow.velocity_spec (σ := u) (γ := (0 : ℝ)) (s := (1 : ℝ))
    (t := (0 : ℝ)) (z := (0 : ℝ) - 0 * d * w.2) (by norm_num : (0 : ℝ) ≤ 0)
  simp only [AxialFlow.profile, zero_mul, add_zero] at hv
  unfold affineMap velocityMap axialMap
  simp only [zero_mul]
  rw [hv]
  congr 1
  ring

theorem scaled_argument {d : ℝ} (hd : d ≠ 0) (u : ℝ) (w : Transverse × ℝ) :
    d⁻¹ • (affineMap d u w - center u) = SheetMeasures.join w := by
  have ht : ∀ (c : ℝ) (v : Velocity), transverse (c • v) = c • transverse v := by
    intro c v
    apply (WithLp.ext_iff 2).mpr
    rfl
  apply split.injective
  rw [split_apply, split_apply]
  apply Prod.ext
  · change d⁻¹ * (axial (affineMap d u w) - axial (center u)) = axial (SheetMeasures.join w)
    simp only [affineMap, center, PlaneChart.axial_join]
    change d⁻¹ * (u + d * w.2 - u) = w.2
    field_simp
    ring
  · rw [ht, PlaneChart.transverse_sub]
    simp only [affineMap, center, PlaneChart.transverse_join, sub_zero, smul_smul,
      inv_mul_cancel₀ hd, one_smul]
    exact (PlaneChart.transverse_join w.1 w.2).symm

theorem gaussian_coordinate {d : ℝ} (hd : 0 < d) (c b u : ℝ) (w : Transverse × ℝ) :
    d ^ 3 * GaussianFrequency.density c b d (center u) (affineMap d u w) =
      c * Real.exp (-b * ‖SheetMeasures.join w‖ ^ 2) := by
  unfold GaussianFrequency.density JetThermalLaw.scaled JetGaussianMoments.kernel
  rw [scaled_argument hd.ne']
  field_simp

theorem gaussian_parameter_bound {c b : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b)
    (w : Transverse × ℝ) :
    c * Real.exp (-b * ‖SheetMeasures.join w‖ ^ 2) ≤
      (c * (Real.pi * Real.sqrt Real.pi)) * JetGaussianProduct.density w := by
  have he : Real.exp (-b * ‖SheetMeasures.join w‖ ^ 2) ≤
      Real.exp (-‖SheetMeasures.join w‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ‖SheetMeasures.join w‖]
  calc
    _ ≤ c * Real.exp (-‖SheetMeasures.join w‖ ^ 2) := mul_le_mul_of_nonneg_left he hc
    _ = _ := by rw [JetGaussianProduct.density_eq]; field_simp

theorem measure_domination {c b d : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b) (hd : 0 < d) (u : ℝ) :
    volume.withDensity (fun v => ENNReal.ofReal (GaussianFrequency.density c b d (center u) v)) ≤
      ENNReal.ofReal (c * (Real.pi * Real.sqrt Real.pi)) •
        SheetMeasures.sheetLaw d (JetAxialLaw.law u 0 0 1 d 0 0) := by
  have hf : Measurable (fun v => ENNReal.ofReal (GaussianFrequency.density c b d (center u) v)) := by
    unfold GaussianFrequency.density JetThermalLaw.scaled JetGaussianMoments.kernel
    fun_prop
  have hmap := JetCoreMeasure.map_withDensity (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) hd
    (by norm_num : (0 : ℝ) ≤ 0) u 0 hf
  have hmeas := (velocity_measurePreserving (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) hd
    (by norm_num : (0 : ℝ) ≤ 0) u 0).measurable
  rw [← hmap, ← JetGaussianProduct.parameterLaw_map (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) hd (by norm_num : (0 : ℝ) ≤ 0),
    ← Measure.map_smul]
  apply Measure.map_mono _ hmeas
  rw [parameterMeasure_eq (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 0)]
  have hj : (fun w : Transverse × ℝ => ENNReal.ofReal
      (d ^ 2 * JetCoreJacobian.jacobian u 0 0 1 d 0 0 w.2)) =
      (fun _ => ENNReal.ofReal (d ^ 3)) := by
    funext w
    simp only [JetCoreJacobian.jacobian, zero_mul, add_zero, div_one]
    congr 1
  rw [hj]
  have hfg : Measurable (fun w => ENNReal.ofReal
      (GaussianFrequency.density c b d (center u) (velocityMap u 0 0 1 d 0 0 w))) := hf.comp hmeas
  rw [← withDensity_mul _ measurable_const hfg, JetGaussianProduct.parameterLaw_density]
  have hg : Measurable (fun w => ENNReal.ofReal (JetGaussianProduct.density w)) := by
    unfold JetGaussianProduct.density GaussianDiskMixture.gaussianDensity
    fun_prop
  rw [← withDensity_smul _ hg]
  apply withDensity_mono
  filter_upwards [] with w
  change ENNReal.ofReal (d ^ 3) * _ ≤ ENNReal.ofReal (c * (Real.pi * Real.sqrt Real.pi)) * _
  rw [← ENNReal.ofReal_mul (pow_nonneg hd.le _),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ c * (Real.pi * Real.sqrt Real.pi)),
    ← affineMap_eq, gaussian_coordinate hd]
  exact ENNReal.ofReal_le_ofReal (gaussian_parameter_bound hc hb w)

end BoltzmannNonuniqueness.JetAffineSheet

end

end

section

/-! # The Gaussian remainder has the smaller sheet amplitude d/s² -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetSupersolution
open BoltzmannNonuniqueness.JetBarrierCollision
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetRemainderSheet

theorem remainder_eq {d : ℝ} (hd : 0 < d) (η K α γ s t : ℝ)
    (a : Bool) (x : Space) (v : Velocity) :
    remainder η K α γ s d t a x v =
      GaussianFrequency.density (epsilon K s d * massScale η K α γ s d t a x) (2 - t) d
        (JetAffineSheet.center (AxialFlow.velocity (sign a) α γ s t x.2)) v := by
  rw [remainder, barrier_eq_density hd]
  unfold GaussianFrequency.density centerVelocity JetAffineSheet.center
  ring

theorem measure_domination {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space) :
    volume.withDensity (fun v => ENNReal.ofReal (remainder η K α γ s d t a x v)) ≤
      ENNReal.ofReal (amplitude η K α γ s d t a x) •
        SheetMeasures.sheetLaw d
          (JetAxialLaw.law (AxialFlow.velocity (sign a) α γ s t x.2) 0 0 1 d 0 0) := by
  simp_rw [remainder_eq hd]
  exact JetAffineSheet.measure_domination
    (mul_nonneg (epsilon_nonneg hK hs hd) (massScale_nonneg hK hs η α γ d t a x))
    (by linarith) hd _

theorem amplitude_bound {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space) :
    amplitude η K α γ s d t a x ≤ uniformConstant K * (d / s ^ 2) := by
  have hm := massScale_le hK hs hd ht htmax η α γ a x
  have he := epsilon_nonneg hK hs hd
  calc
    _ ≤ (epsilon K s d * (Real.exp 4 * JetThermalKernel.bound * (K / s))) *
        (Real.pi * Real.sqrt Real.pi) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm he) (by positivity)
    _ = _ := by unfold epsilon uniformConstant; field_simp

theorem axial_moment {α d : ℝ} (hα : 0 ≤ α) (hd : 0 < d) (hdmax : d ≤ 1 / 16)
    (γ s t z : ℝ) (a : Bool) :
    SheetMeasures.AxialMoment (JetAxialLaw.law (AxialFlow.velocity (sign a) α γ s t z) 0 0 1 d 0 0)
      (2 * Real.exp (16 * (1 + α) ^ 2)) := by
  have hm := JetAxialLaw.moment (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) < 1) hd hdmax (by norm_num : (0 : ℝ) ≤ 0)
    (AxialFlow.velocity (sign a) α γ s t z) 0
  refine ⟨hm.integrable, hm.bound.trans ?_⟩
  have hsiga : |sign a| = 1 := by cases a <;> norm_num [sign]
  have hu := AxialTransport.velocity_abs_le (σ := sign a) (γ := γ) (s := s) (t := t) (z := z) hα
  rw [hsiga] at hu
  simp only [add_zero]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
  nlinarith [abs_nonneg (AxialFlow.velocity (sign a) α γ s t z), sq_abs (AxialFlow.velocity (sign a) α γ s t z)]

theorem normalized_gain_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1 / 16) (htmax : t ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool) (x : Space)
    {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain
      (volume.withDensity (fun p => ENNReal.ofReal (remainder η K α γ s d t a x p))) q v ≤
      ENNReal.ofReal (amplitude η K α γ s d t a x) *
        SheetTotal.bound q (2 * Real.exp (16 * (1 + α) ^ 2)) := by
  have hp := JetAxialLaw.probability (AxialFlow.velocity (sign a) α γ s t x.2) 0 0 1 d 0 0
  have he : SheetClass.IsElementary (2 * Real.exp (16 * (1 + α) ^ 2))
      (SheetMeasures.sheetLaw d
        (JetAxialLaw.law (AxialFlow.velocity (sign a) α γ s t x.2) 0 0 1 d 0 0)) :=
    ⟨d, _, hd.le, by linarith, hp, axial_moment hα hd hdmax γ s t x.2 a, rfl⟩
  apply (chartGain_mono_measure (measure_domination hK hs hd htmax η α γ a x) _ v).trans
  rw [chartGain_smul_measure]
  exact mul_le_mul' le_rfl (SheetClass.elementary_bound hq₁ hq₂ he hv)

end BoltzmannNonuniqueness.JetRemainderSheet

end

end

section

/-! # Mixed gain of the complete cold supersolution -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetEnvelopeGain

theorem measure_eq {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (η α γ t : ℝ) (a : Bool) (x : Space) :
    volume.withDensity (fun v => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x, v))) =
      volume.withDensity (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, v))) +
      volume.withDensity (fun v => ENNReal.ofReal (JetRemainderSheet.remainder η K α γ s d t a x v)) := by
  have heq : (fun v => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x, v))) =
      (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, v))) +
      (fun v => ENNReal.ofReal (JetRemainderSheet.remainder η K α γ s d t a x v)) := by
    funext v
    exact ENNReal.ofReal_add (JetFreeTransport.free_nonneg hK hs.le hd.le η α γ t a (x, v))
      (mul_nonneg (JetSupersolution.epsilon_nonneg hK hs hd)
        (JetBarrier.barrier_nonneg hK hs.le hd.le η α γ t a (x, v)))
  rw [heq, withDensity_add_left]
  exact ((JetFreeTransport.measurable_free η K α γ s d t a).comp
    (measurable_const.prodMk measurable_id)).ennreal_ofReal

theorem normalized_gain_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1 / 16)
    (ht : 0 ≤ t) (htmax : t ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2)
    (η : ℝ) (a : Bool) (x : Space) {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain
      (volume.withDensity (fun p => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x, p)))) q v ≤
      ENNReal.ofReal (amplitude η K α γ s d t a x) *
        SheetTotal.bound q (2 * Real.exp (16 * (1 + α) ^ 2)) := by
  have hc := JetCoreSheet.normalized_gain_bound hK hα hγ hs hd hdmax ht hq₁ hq₂ η a x hv
  have hr := JetRemainderSheet.normalized_gain_bound (γ := γ) hK hα.le hs hd hdmax htmax hq₁ hq₂ η a x hv
  have hsiga : |sign a| = 1 := by cases a <;> norm_num [sign]
  rw [hsiga] at hc
  have ha := JetCoreSheet.amplitude_nonneg hK hs ht α γ
  have hb : 0 ≤ JetRemainderSheet.amplitude η K α γ s d t a x := by
    unfold JetRemainderSheet.amplitude
    have := JetSupersolution.epsilon_nonneg hK hs hd
    have := JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x
    positivity
  unfold normalizedChartGain
  rw [measure_eq hK hs hd, chartGain_add_measure]
  exact (add_le_add hc hr).trans_eq (by rw [← add_mul, ← ENNReal.ofReal_add ha hb]; rfl)

theorem amplitude_bound {K α γ s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (hsmall : d * (s + t) ≤ s ^ 2)
    (η : ℝ) (a : Bool) (x : Space) :
    amplitude η K α γ s d t a x ≤
      (K * max 1 (α * γ)⁻¹ * JetGaussianProduct.coefficient + JetRemainderSheet.uniformConstant K) /
        (s + t) := by
  have hr := JetRemainderSheet.amplitude_bound hK hs hd ht htmax η α γ a x
  have hscale : d / s ^ 2 ≤ 1 / (s + t) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hs) (by positivity : 0 < s + t)).mpr
    simpa only [one_mul] using hsmall
  have hC : 0 ≤ JetRemainderSheet.uniformConstant K := by
    unfold JetRemainderSheet.uniformConstant
    have := JetComparisonCoefficient.coefficient_ge_one hK
    have := JetThermalKernel.bound_pos
    positivity
  have hrs : JetRemainderSheet.amplitude η K α γ s d t a x ≤
      JetRemainderSheet.uniformConstant K / (s + t) := hr.trans (by
    simpa only [div_eq_mul_inv, one_mul] using (mul_le_mul_of_nonneg_left hscale hC))
  calc
    _ ≤ JetCoreSheet.amplitude K α γ s t + JetRemainderSheet.uniformConstant K / (s + t) :=
      add_le_add le_rfl hrs
    _ = _ := by unfold JetCoreSheet.amplitude; ring


theorem gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s)
    (hd : 0 < d) (hdmax : d ≤ 1 / 16) (ht : 0 ≤ t) (htmax : t ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool) (x : Space) :
    ∀ᵐ v : Velocity, nonnegativeGain
      (fun p => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x, p)))
      (fun p => ENNReal.ofReal (H q p)) v ≤
      ENNReal.ofReal (H q v) * (ENNReal.ofReal (amplitude η K α γ s d t a x) *
        SheetTotal.bound q (2 * Real.exp (16 * (1 + α) ^ 2))) := by
  have hf : Measurable (fun p => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x, p))) :=
    (JetSupersolution.measurable_velocity hd η K α γ s t a x).ennreal_ofReal
  apply nonnegativeGain_le_of_chartGain hcarleman hf ((measurable_H q).ennreal_ofReal)
  filter_upwards [SheetApplication.ae_transverse_ne_zero] with v hv
  rw [SheetApplication.gain_H_eq]
  exact mul_le_mul' le_rfl (normalized_gain_bound hK hα hγ hs hd hdmax ht htmax hq₁ hq₂ η a x hv)

theorem thermal_width_le {d₀ s : ℝ} (hd₀max : d₀ ≤ 1) (hs : 0 ≤ s) (hsmax : s ≤ 1 / 8) :
    d₀ * s ^ 10 ≤ 1 / 16 := by
  calc
    _ ≤ 1 * (1 / 8 : ℝ) ^ 10 := mul_le_mul hd₀max (pow_le_pow_left₀ hs hsmax 10)
      (pow_nonneg hs _) (by norm_num)
    _ ≤ _ := by norm_num

theorem thermal_scale_small {d₀ s t : ℝ} (hd₀max : d₀ ≤ 1)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) :
    (d₀ * s ^ 10) * (s + t) ≤ s ^ 2 := by
  have hp : s ^ 8 ≤ 1 := pow_le_one₀ hs.le (by linarith)
  have hprod : d₀ * s ^ 8 ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hd₀max hp (pow_nonneg hs.le _) (by norm_num)
      _ = _ := one_mul 1
  have hprod' : d₀ * s ^ 8 * (s + t) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hprod (by linarith) (by positivity) (by norm_num)
      _ = _ := one_mul 1
  calc
    _ = s ^ 2 * (d₀ * s ^ 8 * (s + t)) := by ring
    _ ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left hprod' (sq_nonneg s)
    _ = _ := mul_one _

end BoltzmannNonuniqueness.JetEnvelopeGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetCoreMomentBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Arbitrary-power bounds for the complete escaped-barrier sum -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetLatticeTail

namespace BoltzmannNonuniqueness.JetEscapedTotal

theorem scale_bound {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η) (j : ℕ) :
    jetScale s₀ η j ≤ s₀ := by
  have h := scale_antitone hs₀.le hη.le (show 0 ≤ j + 1 by omega)
  simpa only [jetScale, DatumBounds.scale, Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, mul_one] using h

end BoltzmannNonuniqueness.JetEscapedTotal

end

end

section

/-! # The real mixed-gain estimate for the main cold color -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetMainGain

theorem sheetConstant_pos (α q : ℝ) : 0 < sheetConstant α q := by
  unfold sheetConstant
  positivity

theorem sheet_bound (α q : ℝ) :
    SheetTotal.bound q (2 * Real.exp (16 * (1 + α) ^ 2)) ≤ ENNReal.ofReal (sheetConstant α q) := by
  rw [sheetConstant, ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num),
    ENNReal.ofReal_toReal (SheetTotal.bound_lt_top _ _).ne]
  exact le_add_of_nonneg_right bot_le

theorem numerator_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ : ℝ) :
    0 ≤ K * max 1 (α * γ)⁻¹ * JetGaussianProduct.coefficient + JetRemainderSheet.uniformConstant K := by
  have hm : 0 ≤ max 1 (α * γ)⁻¹ := zero_le_one.trans (le_max_left _ _)
  have hJ := JetThermalKernel.bound_pos
  have hL := JetComparisonCoefficient.coefficient_ge_one hK
  unfold JetGaussianProduct.coefficient JetRemainderSheet.uniformConstant
  positivity

theorem coefficient_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ q : ℝ) : 0 ≤ coefficient K α γ q :=
  mul_nonneg (numerator_nonneg hK α γ) (sheetConstant_pos α q).le

theorem nonnegative_gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d₀ t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (ht : 0 < t) (htmax : t ≤ 1 / 32) (hq₁ : 1 < q) (hq₂ : q < 2)
    (η : ℝ) (a : Bool) (x : Space) :
    ∀ᵐ v : Velocity, nonnegativeGain
      (fun w => ENNReal.ofReal (JetSupersolution.U η K α γ s (d₀ * s ^ 10) t a (x, w)))
      (fun w => ENNReal.ofReal (H q w)) v ≤ ENNReal.ofReal (coefficient K α γ q / (s + t) * H q v) := by
  have hd : 0 < d₀ * s ^ 10 := by positivity
  have ht1 : t ≤ 1 := htmax.trans (by norm_num)
  have hA := JetEnvelopeGain.amplitude_bound (α := α) (γ := γ) hK hs hd ht ht1
    (JetEnvelopeGain.thermal_scale_small hd₀max hs hsmax ht.le htmax) η a x
  filter_upwards [JetEnvelopeGain.gain_bound hcarleman hK hα hγ hs hd
    (JetEnvelopeGain.thermal_width_le hd₀max hs.le hsmax) ht.le ht1 hq₁ hq₂ η a x] with v hv
  apply hv.trans
  calc
    _ ≤ ENNReal.ofReal (H q v) * (ENNReal.ofReal
        ((K * max 1 (α * γ)⁻¹ * JetGaussianProduct.coefficient + JetRemainderSheet.uniformConstant K) /
          (s + t)) * ENNReal.ofReal (sheetConstant α q)) :=
      mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hA) (sheet_bound α q))
    _ = _ := by
      rw [← ENNReal.ofReal_mul (div_nonneg (numerator_nonneg hK α γ) (by positivity)),
        ← ENNReal.ofReal_mul (H_nonneg q v)]
      congr 1
      unfold coefficient
      ring

theorem gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d₀ t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (ht : 0 < t) (htmax : t ≤ 1 / 32) (hq₁ : 1 < q) (hq₂ : q < 2)
    (η : ℝ) (a : Bool) (x : Space) :
    ∀ᵐ v : Velocity,
      Integrable (MixedRealGain.integrand
        (fun w => JetSupersolution.U η K α γ s (d₀ * s ^ 10) t a (x, w)) (H q) v) gainPairMeasure ∧
      MixedRealGain.gain (fun w => JetSupersolution.U η K α γ s (d₀ * s ^ 10) t a (x, w)) (H q) v ≤
        coefficient K α γ q / (s + t) * H q v := by
  have hd : 0 < d₀ * s ^ 10 := by positivity
  have hfm := JetSupersolution.measurable_velocity hd η K α γ s t a x
  have hf := fun w => JetSupersolution.nonneg hK hs hd η α γ t a (x, w)
  filter_upwards [nonnegative_gain_bound hcarleman hK hα hγ hs hsmax hd₀ hd₀max ht htmax hq₁ hq₂ η a x]
    with v hv
  exact ⟨MixedRealGain.integrable_of_bound hfm (ChartKernel.measurable_H q) hf (H_nonneg q) v hv,
    MixedRealGain.gain_le_of_bound hfm (ChartKernel.measurable_H q) hf (H_nonneg q)
      (mul_nonneg (div_nonneg (coefficient_nonneg hK α γ q) (by positivity)) (H_nonneg q v)) v hv⟩

end BoltzmannNonuniqueness.JetMainGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CutoffLipschitz
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local weighted Lipschitz bounds for the finite-cutoff equation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CutoffLipschitz

theorem frequency_nonneg {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w) (b : ℝ) (v : Velocity) :
    0 ≤ CollisionCutoff.frequency b f v := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun w => mul_nonneg (CollisionCutoff.rate_nonneg b v w) (hf w))

end BoltzmannNonuniqueness.CutoffLipschitz

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotPhysicalSource
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A fixed negligible velocity set for the weighted local construction

The exceptional set depends only on H and its proved quadratic gain bound,
not on a solution or an iterate. Setting the gain to zero there preserves
its almost-everywhere collision meaning and gives pointwise bounded sources.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.HotRepresentative

theorem integrable_H_gain {q : ℝ} {v : Velocity} (hv : v ∈ good q) :
    Integrable (GainOrder.integrand (H q) v) ((volume : Measure Velocity).prod sphereArea) :=
  GainNonnegative.integrable_of_bound (measurable_H q) (H_nonneg q) v hv

theorem H_gain_bound {q : ℝ} {v : Velocity} (hv : v ∈ good q) :
    BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v ≤ HotApplication.realBound q * H q v :=
  GainNonnegative.gain_le_of_bound (measurable_H q) (H_nonneg q)
    (mul_nonneg (HotApplication.realBound_pos q).le (H_nonneg q v)) v 0 hv

variable {X : Type*} [MeasurableSpace X]

theorem measurable_density {f : X × Velocity → ℝ} (hf : Measurable f) (q : ℝ) :
    Measurable (density q f) := ((measurable_H q).comp measurable_snd).mul hf

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Pointwise weighted gain bounds off the fixed exceptional set -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem gain_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (q b : ℝ) (p : X × Velocity) :
    0 ≤ gain q b f p := by
  unfold gain
  split_ifs
  · apply div_nonneg _ (H_nonneg _ _)
    apply integral_nonneg
    intro w
    exact mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _)
      (mul_nonneg (H_nonneg _ _) (hf _))) (mul_nonneg (H_nonneg _ _) (hf _))
  · exact le_rfl

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Loss estimates and the collision meaning of weighted representatives -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem density_bounds {q A : ℝ} {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (p : X × Velocity) :
    0 ≤ density q f p ∧ density q f p ≤ A * H q p.2 :=
  ⟨mul_nonneg (H_nonneg _ _) (hf p).1,
    (mul_le_mul_of_nonneg_left (hf p).2 (H_nonneg _ _)).trans_eq (mul_comm _ _)⟩

omit [MeasurableSpace X] in
theorem frequency_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (q b : ℝ) (p : X × Velocity) : 0 ≤ frequency q b f p :=
  CutoffLipschitz.frequency_nonneg (fun _ => mul_nonneg (H_nonneg _ _) (hf _)) b p.2

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Gain created outside one distinguished cold color -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotGainRemainder

/-- The loss-free gain of the remainder uses the mixed cold estimate, rather
than the much larger pointwise norm of the cold color. -/
theorem gain_difference_le {q R D M : ℝ} {v : Velocity}
    (hv : v ∈ HotRepresentative.good q) (hD : 0 ≤ D)
    {f c : Velocity → ℝ} (hfm : Measurable f) (hcm : Measurable c)
    (hc : ∀ w, 0 ≤ c w) (hcf : ∀ w, c w ≤ f w)
    (hf : ∀ w, f w ≤ R * H q w) (hrem : ∀ w, f w - c w ≤ D * H q w)
    (hci : Integrable (MixedRealGain.integrand c (H q) v) gainPairMeasure)
    (hcM : MixedRealGain.gain c (H q) v ≤ M * H q v) (b : ℝ) :
    CollisionCutoff.gain b f v - CollisionCutoff.gain b c v ≤
      (2 * D * M + D^2 * HotApplication.realBound q) * H q v := by
  have hfn (w) : 0 ≤ f w := (hc w).trans (hcf w)
  have hcn (w) : c w ≤ R * H q w := (hcf w).trans (hf w)
  have hbase := HotRepresentative.integrable_H_gain hv
  have hfi := GainOrder.integrable_of_le hfm hfn hf v (GainOrder.integrable_const_mul R v hbase)
  have hcii := GainOrder.integrable_of_le hcm hc hcn v (GainOrder.integrable_const_mul R v hbase)
  have hfc := CollisionCutoff.integrable_gain b hfm hfn v hfi
  have hcc := CollisionCutoff.integrable_gain b hcm hc v hcii
  have hpoint (p : Velocity × Sphere) :
      CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b c v p ≤
        (2*D) * MixedRealGain.integrand c (H q) v p +
          D^2 * GainOrder.integrand (H q) v p := by
    let l := scatterLeft v p.1 p.2
    let r := scatterRight v p.1 p.2
    have hl : 0 ≤ f l - c l := sub_nonneg.mpr (hcf l)
    have hr : 0 ≤ f r - c r := sub_nonneg.mpr (hcf r)
    have h₁ := mul_le_mul (hrem l) (hrem r) hr (mul_nonneg hD (H_nonneg q l))
    have h₂ := mul_le_mul_of_nonneg_left (hrem r) (hc l)
    have h₃ := mul_le_mul_of_nonneg_right (hrem l) (hc r)
    have hd : f l * f r - c l * c r ≤
        D * (c l * H q r + H q l * c r) + D^2 * (H q l * H q r) := by
      nlinarith
    have hdn : 0 ≤ f l * f r - c l * c r :=
      sub_nonneg.mpr (mul_le_mul (hcf l) (hcf r) (hc r) (hfn l))
    have hk := mul_le_mul_of_nonneg_right (CollisionCutoff.kernel_le b v p.1 p.2) hdn
    have hh := mul_le_mul_of_nonneg_left hd (collisionKernel_nonneg v p.1 p.2)
    unfold CollisionCutoff.integrand MixedRealGain.integrand GainOrder.integrand
    dsimp [l,r] at *
    nlinarith
  calc
    _ = ∫ p, CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b c v p
        ∂gainPairMeasure := (integral_sub hfc hcc).symm
    _ ≤ ∫ p, (2*D) * MixedRealGain.integrand c (H q) v p +
        D^2 * GainOrder.integrand (H q) v p ∂gainPairMeasure :=
      integral_mono (hfc.sub hcc) ((hci.const_mul _).add (hbase.const_mul _)) hpoint
    _ = (2*D) * MixedRealGain.gain c (H q) v +
        D^2 * BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v := by
      rw [integral_add (hci.const_mul _) (hbase.const_mul _), integral_const_mul, integral_const_mul]
      rfl
    _ ≤ (2*D) * (M * H q v) + D^2 * (HotApplication.realBound q * H q v) :=
      add_le_add (mul_le_mul_of_nonneg_left hcM (by positivity))
        (mul_le_mul_of_nonneg_left (HotRepresentative.H_gain_bound hv) (sq_nonneg D))
    _ = _ := by ring

end BoltzmannNonuniqueness.HotGainRemainder

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetSolutions
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Monotone and dominated limits for the weighted representative gain -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem integrable_cutoff {q R : ℝ} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R)
    (b : ℝ) (p : X × Velocity) (hp : p.2 ∈ good q) :
    Integrable (CollisionCutoff.integrand b (fun v => density q f (p.1,v)) p.2)
      ((volume : Measure Velocity).prod sphereArea) := by
  have hm : Measurable (fun v => density q f (p.1,v)) := (measurable_density hfm q).comp (measurable_const.prodMk measurable_id)
  have hn : ∀ v, 0 ≤ density q f (p.1,v) := fun v => (density_bounds (q := q) hf (p.1,v)).1
  exact CollisionCutoff.integrable_gain b hm hn p.2
    (GainOrder.integrable_of_le hm hn (fun v => (density_bounds (q := q) hf (p.1,v)).2) p.2
      (GainOrder.integrable_const_mul R p.2 (integrable_H_gain hp)))

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Finite-color domination for the H-weighted collision gain -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem finite_sum_gain_le {q R : ℝ} (s : Finset I)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i ∈ s, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R)
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ p, ∑ i ∈ s, c i p ≤ F p) (b : ℝ) (p : X × Velocity) :
    ∑ i ∈ s, gain q b (c i) p ≤ gain q b F p := by
  classical
  by_cases hp : p.2 ∈ good q
  · have hci (i) (hi : i ∈ s) := integrable_cutoff (hcm i hi) (hc i hi) b p hp
    have hFi := integrable_cutoff hFm hF b p hp
    have hsumD (v : Velocity) : ∑ i ∈ s, density q (c i) (p.1,v) ≤ density q F (p.1,v) := by
      unfold density
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hSum _) (VelocityWeight.H_nonneg _ _)
    have hcn (i) (hi : i ∈ s) (v : Velocity) : 0 ≤ density q (c i) (p.1,v) :=
      (density_bounds (q := q) (hc i hi) (p.1,v)).1
    have hFn (v : Velocity) : 0 ≤ density q F (p.1,v) := (density_bounds (q := q) hF (p.1,v)).1
    simp only [gain,ite_eq_left hp]
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (VelocityWeight.H_nonneg q p.2)
    change (∑ i ∈ s, ∫ w, CollisionCutoff.integrand b
      (fun v => density q (c i) (p.1,v)) p.2 w ∂((volume : Measure Velocity).prod sphereArea)) ≤ _
    rw [← integral_finsetSum _ hci]
    apply integral_mono (integrable_finsetSum s hci) hFi
    intro w
    have hdiag : (∑ i ∈ s, density q (c i) (p.1,scatterLeft p.2 w.1 w.2) *
        density q (c i) (p.1,scatterRight p.2 w.1 w.2)) ≤
        density q F (p.1,scatterLeft p.2 w.1 w.2) * density q F (p.1,scatterRight p.2 w.1 w.2) := by
      calc
        _ ≤ ∑ i ∈ s, density q (c i) (p.1,scatterLeft p.2 w.1 w.2) *
            (∑ j ∈ s, density q (c j) (p.1,scatterRight p.2 w.1 w.2)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j hj => hcn j hj _) hi) (hcn i hi _)
        _ = (∑ i ∈ s, density q (c i) (p.1,scatterLeft p.2 w.1 w.2)) *
            (∑ j ∈ s, density q (c j) (p.1,scatterRight p.2 w.1 w.2)) := by rw [Finset.sum_mul]
        _ ≤ _ := mul_le_mul (hsumD _) (hsumD _) (Finset.sum_nonneg (fun i hi => hcn i hi _)) (hFn _)
    unfold CollisionCutoff.integrand
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hdiag (CollisionCutoff.kernel_nonneg _ _ _ _)
  · simp only [gain,ite_eq_right hp,Finset.sum_const_zero,le_refl]

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedHotRegularity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Countable cold gain sums and the exact hot-source identity -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem gain_family_summable {β b R : ℝ}
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    Summable (fun i => gain β b (c i) p) ∧
      (∑' i, gain β b (c i) p) ≤ gain β b F p := by
  have hn (i) : 0 ≤ gain β b (c i) p :=
    gain_nonneg (fun q => (hc i q).1) β b p
  have hs (s : Finset I) : (∑ i ∈ s, gain β b (c i) p) ≤ gain β b F p :=
    finite_sum_gain_le s (fun i _ => hcm i) hFm
      (fun i _ q => hc i q) hF (hSum s) b p
  exact ⟨summable_of_sum_le hn hs, Real.tsum_le_of_sum_le hn hs⟩

theorem tsum_coldSource {β b R : ℝ}
    (L : ℝ) {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    (∑' i, coldSource β b L F (c i) p) =
      (∑' i, gain β b (c i) p) + (L - frequency β b F p) * (∑' i, c i p) := by
  have hg := (gain_family_summable (β := β) (b := b) hcm hFm hc hF hSum p).1
  have hcs : Summable (fun i => c i p) :=
    summable_of_sum_le (fun i => (hc i p).1) (fun s => hSum s p)
  unfold coldSource
  rw [hg.tsum_add (hcs.mul_left _), tsum_mul_left]

theorem hot_source_identity {β b R : ℝ}
    (L : ℝ) {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    source β b L F p - (∑' i, coldSource β b L F (c i) p) =
      (gain β b F p - ∑' i, gain β b (c i) p) +
      (L - frequency β b F p) * (F p - ∑' i, c i p) := by
  rw [tsum_coldSource L hcm hFm hc hF hSum]
  unfold source
  ring


/-- Dropping the common loss and all but one of the subtracted cold gains. -/
theorem hot_source_le_single {β b R : ℝ} (L : ℝ)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p)
    (i : I) (p : X × Velocity) :
    source β b L F p - (∑' j, coldSource β b L F (c j) p) -
        L * (F p - ∑' j, c j p) ≤ gain β b F p - gain β b (c i) p := by
  have hgs := (gain_family_summable (β := β) (b := b) hcm hFm hc hF hSum p).1
  have hsingle : gain β b (c i) p ≤ ∑' j, gain β b (c j) p :=
    hgs.le_tsum i (fun j _ => gain_nonneg (fun v => (hc j v).1) β b p)
  have hcs : (∑' j, c j p) ≤ F p :=
    Real.tsum_le_of_sum_le (fun j => (hc j p).1) (fun s => hSum s p)
  have hloss := mul_nonneg (frequency_nonneg (fun v => (hF v).1) β b p)
    (sub_nonneg.mpr hcs)
  rw [hot_source_identity L hcm hFm hc hF hSum]
  nlinarith

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_PeriodicJetFamilies
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform hot gain from one main cold jet and a weighted remainder -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetHotGain

theorem remainder_bound (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d₀ t q R D : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (ht : 0 < t) (htmax : t ≤ 1 / 32) (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 ≤ D)
    (η : ℝ) (a : Bool) (x : Space) {f c : Velocity → ℝ}
    (hfm : Measurable f) (hcm : Measurable c)
    (hc : ∀ w, 0 ≤ c w) (hcf : ∀ w, c w ≤ f w)
    (hf : ∀ w, f w ≤ R * H q w)
    (hcU : ∀ w, c w ≤ JetSupersolution.U η K α γ s (d₀*s^10) t a (x,w))
    (hrem : ∀ w, f w - c w ≤ D * H q w) (b : ℝ) :
    ∀ᵐ v : Velocity, CollisionCutoff.gain b f v - CollisionCutoff.gain b c v ≤
      (2*D*JetMainGain.coefficient K α γ q / (s+t) +
        D^2*HotApplication.realBound q) * H q v := by
  filter_upwards [HotRepresentative.ae_good_q80 hcarleman hq₁ hq₂,
    JetMainGain.gain_bound hcarleman hK hα hγ hs hsmax hd₀ hd₀max ht htmax hq₁ hq₂ η a x]
      with v hv hjet
  have hci := MixedRealGain.integrable_of_le hcm (ChartKernel.measurable_H q)
    hc (H_nonneg q) hcU (fun _ => le_rfl) v hjet.1
  have hcmix := (MixedRealGain.gain_mono hcm (ChartKernel.measurable_H q)
    hc (H_nonneg q) hcU (fun _ => le_rfl) v hjet.1).trans hjet.2
  have h := HotGainRemainder.gain_difference_le hv hD hfm hcm hc hcf hf hrem hci hcmix b
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end BoltzmannNonuniqueness.JetHotGain

end

end

section

/-! # Selection of the unique possible main color in the periodic family -/

noncomputable section

open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem outside_iff_not_mem (s₀ η t : ℝ) (x : Velocity) (i : Label) :
    JetLatticeTail.outside η (jetScale s₀ η i.annulus) t i.positive x i.lattice ↔
      x ∉ spatialEnlargement s₀ η t i := Iff.rfl

theorem main_or_outside {s₀ η t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (htmax : t ≤ 1/32) (N : ℕ) (x : Velocity) :
    (∃ i : Label, i.annulus < N ∧ x ∈ spatialEnlargement s₀ η t i ∧
      ∀ j : Label, j.annulus < N → j ≠ i →
        JetLatticeTail.outside η (jetScale s₀ η j.annulus) t j.positive x j.lattice) ∨
    (∀ i : Label, i.annulus < N →
      JetLatticeTail.outside η (jetScale s₀ η i.annulus) t i.positive x i.lattice) := by
  classical
  by_cases h : ∃ i : Label, i.annulus < N ∧ x ∈ spatialEnlargement s₀ η t i
  · obtain ⟨i,hi,hx⟩ := h
    refine Or.inl ⟨i,hi,hx,?_⟩
    intro j _ hji
    rw [outside_iff_not_mem]
    intro hj
    exact hji (common_point_label hs₀ hsmax hη hηmax htmax hj hx)
  · right
    intro i hi
    rw [outside_iff_not_mem]
    exact fun hx => h ⟨i,hi,hx⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Removing the unique main color leaves precisely the escaped family -/

noncomputable section

open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem sum_sub_main {s₀ η t : ℝ} {N : ℕ} {x : Velocity} {f : Label → ℝ}
    (hfs : Summable f) (hzero : ∀ j : Label, ¬j.annulus < N → f j = 0)
    (i : Label) (hi : x ∈ spatialEnlargement s₀ η t i)
    (hout : ∀ j : Label, j.annulus < N → j ≠ i →
      JetLatticeTail.outside η (jetScale s₀ η j.annulus) t j.positive x j.lattice) :
    (∑' j, f j)-f i = ∑' j, escaped s₀ η t N x f j := by
  classical
  have he (j : Label) : (if j=i then 0 else f j) = escaped s₀ η t N x f j := by
    by_cases hji : j=i
    · subst j
      have hn : ¬JetLatticeTail.outside η (jetScale s₀ η i.annulus) t i.positive x i.lattice :=
        fun h => (outside_iff_not_mem s₀ η t x i).mp h hi
      simp [escaped,hn]
    · by_cases hj : j.annulus < N
      · simp [escaped,hji,hj,hout j hj hji]
      · simp only [ite_eq_right hji,hzero j hj,escaped,hj,false_and,ite_false, if_false]
  rw [hfs.tsum_eq_add_tsum_ite i]
  simp_rw [he]
  ring

theorem sum_all_escaped {s₀ η t : ℝ} {N : ℕ} {x : Velocity} {f : Label → ℝ}
    (hzero : ∀ j : Label, ¬j.annulus < N → f j = 0)
    (hout : ∀ j : Label, j.annulus < N →
      JetLatticeTail.outside η (jetScale s₀ η j.annulus) t j.positive x j.lattice) :
    (∑' j, f j) = ∑' j, escaped s₀ η t N x f j := by
  apply tsum_congr
  intro j
  by_cases hj : j.annulus < N
  · simp [escaped,hj,hout j hj]
  · simp only [escaped,hj,false_and,ite_false, if_false,hzero j hj]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotSeedCoreLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform scalar majorant after separating the escaped cold tail -/

namespace BoltzmannNonuniqueness.HotScalarBound

theorem remainder_majorant {M C z e s δ t : ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hz : 0 ≤ z) (he : 0 ≤ e) (he₁ : e ≤ 1)
    (hδ : 0 < δ) (hδs : δ ≤ s) (ht : 0 < t) (ht₁ : t ≤ 1) :
    2*(z+e)*M/(s+t)+(z+e)^2*C ≤
      (2*M/(δ+t))*z+2*C*z^2+(2*M+2*C)*(e/t) := by
  have hst : 0 < s+t := by linarith
  have hδt : 0 < δ+t := by positivity
  have hzpart : (2*M*z)/(s+t) ≤ (2*M*z)/(δ+t) :=
    div_le_div_of_nonneg_left (by positivity) hδt (by linarith)
  have hepart : (2*M*e)/(s+t) ≤ (2*M*e)/t :=
    div_le_div_of_nonneg_left (by positivity) ht (by linarith)
  have hlinear : 2*(z+e)*M/(s+t) ≤ (2*M/(δ+t))*z+(2*M)*(e/t) := by
    calc
      _ = (2*M*z)/(s+t)+(2*M*e)/(s+t) := by ring
      _ ≤ (2*M*z)/(δ+t)+(2*M*e)/t := add_le_add hzpart hepart
      _ = _ := by ring
  have het : e ≤ e/t := (le_div_iff₀ ht).mpr (by nlinarith)
  have hsquare : (z+e)^2 ≤ 2*z^2+2*e := by
    nlinarith [sq_nonneg (z-e),mul_nonneg he (sub_nonneg.mpr he₁)]
  have hquad : (z+e)^2*C ≤ 2*C*z^2+2*C*(e/t) := by
    have h₁ := mul_le_mul_of_nonneg_right hsquare hC
    have h₂ := mul_le_mul_of_nonneg_left het (show 0 ≤ 2*C by positivity)
    nlinarith only [h₁,h₂]
  calc
    _ ≤ ((2*M/(δ+t))*z+(2*M)*(e/t))+(2*C*z^2+2*C*(e/t)) := add_le_add hlinear hquad
    _ = _ := by ring

end BoltzmannNonuniqueness.HotScalarBound


end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedHotGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The normalized hot source retains the uniform geometric estimate -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem jet_gain_difference (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d₀ t q R D : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (ht : 0 < t) (htmax : t ≤ 1 / 32) (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 ≤ D)
    (η : ℝ) (a : Bool) (x : Space) {F c : X × Velocity → ℝ}
    (hFm : Measurable F) (hcm : Measurable c)
    (hc : ∀ p, 0 ≤ c p) (hcF : ∀ p, c p ≤ F p) (hF : ∀ p, F p ≤ R)
    (y : X)
    (hcU : ∀ w, H q w * c (y,w) ≤ JetSupersolution.U η K α γ s (d₀*s^10) t a (x,w))
    (hrem : ∀ w, F (y,w) - c (y,w) ≤ D) (b : ℝ) :
    ∀ᵐ v : Velocity, gain q b F (y,v) - gain q b c (y,v) ≤
      2*D*JetMainGain.coefficient K α γ q / (s+t) + D^2*HotApplication.realBound q := by
  have hbound := JetHotGain.remainder_bound hcarleman hK hα hγ hs hsmax hd₀ hd₀max
    ht htmax hq₁ hq₂ hD η a x
    ((measurable_density hFm q).comp (measurable_const.prodMk measurable_id))
    ((measurable_density hcm q).comp (measurable_const.prodMk measurable_id))
    (fun w => mul_nonneg (H_nonneg q w) (hc (y,w)))
    (fun w => mul_le_mul_of_nonneg_left (hcF (y,w)) (H_nonneg q w))
    (fun w => (mul_le_mul_of_nonneg_left (hF (y,w)) (H_nonneg q w)).trans_eq (mul_comm _ _))
    hcU (fun w => by
      change H q w * F (y,w) - H q w * c (y,w) ≤ D * H q w
      rw [← mul_sub]
      exact (mul_le_mul_of_nonneg_left (hrem w) (H_nonneg q w)).trans_eq (mul_comm _ _)) b
  filter_upwards [ae_good_q80 hcarleman hq₁ hq₂, hbound] with v hv hg
  simp only [gain, ite_eq_left hv]
  rw [← sub_div]
  exact (div_le_iff₀ (H_pos q v)).mpr hg

theorem jet_hot_source_le (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d₀ t q R D : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (ht : 0 < t) (htmax : t ≤ 1 / 32) (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 ≤ D)
    (η : ℝ) (a : Bool) (x : Space) {F : X × Velocity → ℝ} {c : I → X × Velocity → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ u : Finset I, ∀ p, ∑ i ∈ u, c i p ≤ F p)
    (i : I) (y : X)
    (hcU : ∀ w, H q w * c i (y,w) ≤ JetSupersolution.U η K α γ s (d₀*s^10) t a (x,w))
    (hrem : ∀ w, F (y,w) - c i (y,w) ≤ D) (b L : ℝ) :
    ∀ᵐ v : Velocity,
      source q b L F (y,v) - (∑' j, coldSource q b L F (c j) (y,v)) -
          L * (F (y,v) - ∑' j, c j (y,v)) ≤
        2*D*JetMainGain.coefficient K α γ q / (s+t) + D^2*HotApplication.realBound q := by
  classical
  have hciF (p) : c i p ≤ F p := by simpa only [Finset.sum_singleton] using hSum {i} p
  filter_upwards [jet_gain_difference hcarleman hK hα hγ hs hsmax hd₀ hd₀max ht htmax
    hq₁ hq₂ hD η a x hFm (hcm i) (fun p => (hc i p).1) hciF (fun p => (hF p).2) y hcU hrem b]
      with v hv
  exact (hot_source_le_single L hcm hFm hc hF hSum i (y,v)).trans hv

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetFamilyBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform hot-source control from the periodic cold decomposition -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem scale_antitone {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    {i j : ℕ} (hij : i ≤ j) : jetScale s₀ η j ≤ jetScale s₀ η i := by
  unfold jetScale DatumBounds.scale
  apply mul_le_mul_of_nonneg_left _ hs₀
  apply Real.exp_le_exp.mpr
  have h : ((i+1 : ℕ) : ℝ) ≤ ((j+1 : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_right hij 1
  nlinarith

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem select_remainder {s₀ η t z e : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (htmax : t ≤ 1/32)
    (N : ℕ) (x : Velocity) (y : X) (F : X × Velocity → ℝ) (c : Label → X × Velocity → ℝ)
    (hcs : ∀ w, Summable (fun i => c i (y,w)))
    (hzero : ∀ i, ¬i.annulus < N → ∀ w, c i (y,w) = 0)
    (hhot : ∀ w, F (y,w)-(∑' i, c i (y,w)) ≤ z)
    (htail : ∀ w, (∑' i, escaped s₀ η t N x (fun j => c j (y,w)) i) ≤ e) :
    ∃ i : Label, i.annulus ≤ N ∧ ∀ w, F (y,w)-c i (y,w) ≤ z+e := by
  obtain ⟨i,hi,hcore,hout⟩ | hout := main_or_outside hs₀ hsmax hη hηmax htmax N x
  · refine ⟨i,hi.le,?_⟩
    intro w
    have he := sum_sub_main (hcs w) (fun j hj => hzero j hj w) i hcore hout
    have hh := hhot w
    have ht := htail w
    linarith
  · let i : Label := ⟨N,false,0⟩
    refine ⟨i,le_refl N,?_⟩
    intro w
    have hi : c i (y,w) = 0 := hzero i (lt_irrefl N) w
    have he := sum_all_escaped (fun j hj => hzero j hj w) hout
    have hh := hhot w
    have ht := htail w
    rw [hi]
    linarith

theorem uniform_hot_source_q80_oai (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q t R z e : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hz : 0 ≤ z) (he : 0 ≤ e) (he₁ : e ≤ 1)
    (N : ℕ) (x : Velocity) (y : X)
    {F : X × Velocity → ℝ} {c : Label → X × Velocity → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R)
    (hSum : ∀ u : Finset Label, ∀ p, ∑ i ∈ u, c i p ≤ F p)
    (hzero : ∀ i, ¬i.annulus < N → ∀ w, c i (y,w) = 0)
    (hhot : ∀ w, F (y,w)-(∑' i, c i (y,w)) ≤ z)
    (htail : ∀ w, (∑' i, escaped s₀ η t N x (fun j => c j (y,w)) i) ≤ e)
    (hcU : ∀ i w, VelocityWeight.H q w*c i (y,w) ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,w)) (b L : ℝ) :
    ∀ᵐ v : Velocity,
      HotRepresentative.source q b L F (y,v) -
        (∑' i, HotRepresentative.coldSource q b L F (c i) (y,v)) -
        L*(F (y,v)-(∑' i, c i (y,v))) ≤
      (2*JetMainGain.coefficient K α γ q/(jetScale s₀ η N+t))*z +
        2*HotApplication.realBound q*z^2 +
        (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*(e/t) := by
  have hcs (w) : Summable (fun i => c i (y,w)) :=
    summable_of_sum_le (fun i => (hc i (y,w)).1) (fun u => hSum u (y,w))
  obtain ⟨i,hi,hrem⟩ := select_remainder hs₀ hsmax hη hηmax htmax N x y F c hcs hzero hhot htail
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
  have hsn := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hss := JetEscapedTotal.scale_bound hs₀ hη i.annulus
  filter_upwards [HotRepresentative.jet_hot_source_le hcarleman hK hα hγ hs
    (hss.trans hsmax) hd₀ hd₀max ht htmax hq₁ hq₂ (add_nonneg hz he) η i.positive
    (JetSpatialBox.shifted x i.lattice) hFm hcm hc hF hSum i y (hcU i) hrem b L] with v hv
  exact hv.trans (HotScalarBound.remainder_majorant (JetMainGain.coefficient_nonneg hK α γ q)
    (HotApplication.realBound_pos q).le hz he he₁ hsn (scale_antitone hs₀.le hη.le hi)
    ht (htmax.trans (by norm_num)))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.uniform_hot_source_q80_oai.{u_1} := @OAI.BoltzmannNonuniqueness.JetCopyDatum.uniform_hot_source_q80_oai.{u_1}
