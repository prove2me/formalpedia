-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.HotRepresentative.ae_good_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:07:31.148074+00:00
-- url     : https://prove2.me/submissions/942426a0-c747-40b3-b222-ebf18e3cabf3

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianEstimates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
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

theorem diskDensity_nonneg (a : ℝ) (p : Transverse) : 0 ≤ diskDensity a p := by
  unfold diskDensity
  apply indicator_nonneg _ p
  intro x hx
  positivity

theorem diskDensity_eq_ite (a : ℝ) (p : Transverse) :
    diskDensity a p = if ‖p‖ < a then (Real.pi * a ^ 2)⁻¹ else 0 := by
  simp [diskDensity, indicator]

theorem measurable_diskDensity : Measurable (fun ap : ℝ × Transverse => diskDensity ap.1 ap.2) := by
  simp only [diskDensity_eq_ite]
  apply Measurable.ite (measurableSet_lt measurable_snd.norm measurable_fst) <;> fun_prop

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

theorem uniformDiskLaw_lintegral {a : ℝ} (ha : 0 < a)
    (φ : Transverse → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ p, φ p ∂uniformDiskLaw a) =
      (ENNReal.ofReal (Real.pi * a ^ 2))⁻¹ * ∫⁻ p in ball (0 : Transverse) a, φ p := by
  have hmk : Measurable (fun p : Transverse => (a, p)) :=
    measurable_const.prodMk measurable_id
  have hda : Measurable (diskDensity a) := by
    simpa only [Function.comp_def] using measurable_diskDensity.comp hmk
  rw [uniformDiskLaw, lintegral_withDensity_eq_lintegral_mul volume hda.ennreal_ofReal hφ]
  exact lintegral_diskDensity_mul φ a ha

end BoltzmannNonuniqueness.GaussianDiskMixture

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

theorem ae_regularTransverse_uniformDisk {v : Transverse} (hv : v ≠ 0) (d : ℝ) :
    ∀ᵐ p ∂uniformDiskLaw d, RegularTransverse v p :=
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

theorem uniformDisk_extendedKernel_lintegral_le {q d : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hd : 0 < d) {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, extendedKernel q v p ∂uniformDiskLaw d) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  rw [lintegral_congr_ae (extendedKernel_ae_eq (ae_regularTransverse_uniformDisk hv d) q)]
  have hm : Measurable (fun p => ENNReal.ofReal (kernel q (direction v) (v - p))) := by
    unfold kernel
    fun_prop
  rw [uniformDiskLaw_lintegral hd _ hm]
  have hi := integrableOn_kernel_translatedDisk hq₂ hd (direction v) (norm_direction hv) v
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (fun p => kernel_nonneg q (direction v) (v - p)))]
  rw [mul_comm, ← div_eq_mul_inv]
  rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < Real.pi * d ^ 2)]
  exact ENNReal.ofReal_le_ofReal (uniformDisk_expectation_le hq₁ hq₂ hd hv)

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem measure_smul (a : ℝ≥0∞) (c : Measure Velocity)
    (h : Velocity → ℝ≥0∞) (v : Velocity) :
    measure (a • c) h v = a • measure c h v := by
  rw [measure, Measure.prod_smul_left, withDensity_smul_measure]
  rfl

theorem measure_withDensity (c : Measure Velocity) {w h : Velocity → ℝ≥0∞}
    (hw : Measurable w) (hh : Measurable h) (v : Velocity) :
    measure (c.withDensity w) h v =
      (c.prod (volume.prod volume)).withDensity (fun y => w y.1 * density h v y) := by
  rw [measure, prod_withDensity_left hw]
  exact (withDensity_mul _ (hw.comp measurable_fst) (measurable_density hh v)).symm

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

theorem measurable_weightRatio (q : ℝ) (v : Velocity) : Measurable (weightRatio q v) :=
  ((measurable_W q).div_const _).ennreal_ofReal

theorem measurableSet_ballRegion (v : Velocity) (R : ℝ) : MeasurableSet (ballRegion v R) :=
  measurableSet_le ((measurable_point v).sub_const v).norm measurable_const

theorem measurable_radius (v : Velocity) : Measurable (radius v) :=
  measurable_fst.norm.add (((measurable_point v).sub_const v).norm)

theorem measurableSet_shell (v : Velocity) (R : ℝ) : MeasurableSet (shell v R) :=
  (measurableSet_lt measurable_const (measurable_radius v)).inter
    (measurableSet_le (measurable_radius v) measurable_const)

theorem shell_subset_ball (v : Velocity) (R : ℝ) : shell v R ⊆ ballRegion v (2 * R) := by
  intro y hy
  have hp := norm_nonneg y.1
  exact le_trans (le_add_of_nonneg_left hp) hy.2

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotGainReduction
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Algebraic reduction of the quadratic hot gain

Symmetry allows the output polynomial weight to be assigned to either
incoming velocity. The resulting mixed gain has only one polynomial factor,
while its two Gaussian factors cancel by collision energy conservation.
-/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotWeight

theorem G_pos (q : ℝ) (v : Velocity) : 0 < G q v :=
  mul_pos (Real.exp_pos _) (W_pos q v)

theorem polynomial_pos (v : Velocity) : 0 < polynomial v := by
  unfold polynomial
  positivity

theorem H_mul_polynomial (q : ℝ) (v : Velocity) : H q v * polynomial v = G q v := by
  unfold H polynomial G
  change Real.exp (-‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (-50 : ℝ) * W q v *
    (1 + ‖v‖ ^ 2) ^ (50 : ℕ) = _
  rw [show (-50 : ℝ) = -(50 : ℕ) by norm_num,
    Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hp : (1 + ‖v‖ ^ 2) ^ (50 : ℕ) ≠ 0 := by positivity
  field_simp

theorem H_eq_G_div (q : ℝ) (v : Velocity) : H q v = G q v / polynomial v :=
  (eq_div_iff (polynomial_pos v).ne').mpr (H_mul_polynomial q v)

theorem measurable_G (q : ℝ) : Measurable (G q) := by
  unfold G
  have he : Measurable (fun v : Velocity => Real.exp (-‖v‖ ^ 2)) := by fun_prop
  exact he.mul (ChartKernel.measurable_W q)

/-- The fixed manuscript exponent `m = 100` needs only this two-input estimate. -/
theorem polynomial_pair_bound (p ξ v : Velocity)
    (hv : ‖v‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖ξ‖ ^ 2) :
    polynomial v ≤ (2 : ℝ) ^ (50 : ℕ) * (polynomial p + polynomial ξ) := by
  by_cases h : ‖ξ‖ ^ 2 ≤ ‖p‖ ^ 2
  · have hb : 1 + ‖v‖ ^ 2 ≤ 2 * (1 + ‖p‖ ^ 2) := by linarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖v‖ ^ 2) hb 50
    rw [mul_pow] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (polynomial_pos ξ).le) (by positivity))
  · have hb : 1 + ‖v‖ ^ 2 ≤ 2 * (1 + ‖ξ‖ ^ 2) := by linarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖v‖ ^ 2) hb 50
    rw [mul_pow] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (polynomial_pos p).le) (by positivity))

/-- The quadratic integrand is bounded by a symmetric mixed integrand. -/
theorem quadratic_ratio_bound (q : ℝ) (p ξ v : Velocity)
    (hv : ‖v‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖ξ‖ ^ 2) :
    H q p * H q ξ / H q v ≤ (2 : ℝ) ^ (50 : ℕ) *
      ((H q p * G q ξ + G q p * H q ξ) / G q v) := by
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (H_pos q v) (G_pos q v)).mpr
  have h := mul_le_mul_of_nonneg_left (polynomial_pair_bound p ξ v hv)
    (mul_nonneg (mul_nonneg (H_nonneg q p) (H_nonneg q ξ)) (H_nonneg q v))
  rw [← H_mul_polynomial q p, ← H_mul_polynomial q ξ, ← H_mul_polynomial q v]
  convert h using 1 <;> ring

theorem quadratic_product_bound (q : ℝ) (p ξ v : Velocity)
    (hv : ‖v‖ ^ 2 ≤ ‖p‖ ^ 2 + ‖ξ‖ ^ 2) :
    H q p * H q ξ ≤ (2 : ℝ) ^ (50 : ℕ) * (H q v / G q v) *
      (H q p * G q ξ + G q p * H q ξ) := by
  calc
    _ ≤ ((2 : ℝ) ^ (50 : ℕ) *
        ((H q p * G q ξ + G q p * H q ξ) / G q v)) * H q v :=
      (div_le_iff₀ (H_pos q v)).mp (quadratic_ratio_bound q p ξ v hv)
    _ = _ := by ring

/-- Both Gaussian factors cancel against the output Gaussian on the collision plane. -/
theorem mixed_plane_weight (q : ℝ) (p ξ v : Velocity)
    (h : inner ℝ (v - p) (ξ - v) = 0) :
    H q p * (G q ξ / G q v) =
      Real.exp (-‖companionVelocity p ξ v‖ ^ 2) * (polynomial p)⁻¹ *
        (W q p * W q ξ / W q v) := by
  have hr : G q ξ / G q v =
      Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) * (W q ξ / W q v) := by
    unfold G
    rw [mul_div_mul_comm, carleman_gaussian_ratio p ξ v h]
  rw [H_eq_G_div q p, hr]
  unfold G
  have he : Real.exp (-‖p‖ ^ 2) *
      Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2) =
      Real.exp (-‖companionVelocity p ξ v‖ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-‖p‖ ^ 2) *
          Real.exp (‖p‖ ^ 2 - ‖companionVelocity p ξ v‖ ^ 2)) *
        (polynomial p)⁻¹ * (W q p * W q ξ / W q v) := by ring
    _ = _ := by rw [he]

end BoltzmannNonuniqueness.HotWeight

end

end

section

/-! # Polynomial decay on collision shells

Eight powers suffice after the five-dimensional geometric estimate;
the manuscript's fixed polynomial exponent fifty supplies these powers.
-/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight

namespace BoltzmannNonuniqueness.HotShellWeight

theorem constant_pos : 0 < constant := by norm_num [constant]

theorem polynomial_eighth_bound (p : Velocity) {u : ℝ}
    (hu : 0 ≤ u) (hp : u ≤ ‖p‖) : u ^ 8 ≤ polynomial p := by
  have h₂ : u ^ 2 ≤ 1 + ‖p‖ ^ 2 := by nlinarith [norm_nonneg p]
  have h₄ := pow_le_pow_left₀ (sq_nonneg u) h₂ 4
  have h₅₀ : (1 + ‖p‖ ^ 2) ^ (4 : ℕ) ≤ (1 + ‖p‖ ^ 2) ^ (50 : ℕ) :=
    pow_le_pow_right₀ (by nlinarith [sq_nonneg ‖p‖]) (by norm_num)
  calc
    u ^ 8 = (u ^ 2) ^ 4 := by ring
    _ ≤ (1 + ‖p‖ ^ 2) ^ (4 : ℕ) := h₄
    _ ≤ polynomial p := h₅₀

theorem polynomial_inv_le_one (p : Velocity) : (polynomial p)⁻¹ ≤ 1 := by
  apply inv_le_one_of_one_le₀
  exact one_le_pow₀ (by nlinarith [sq_nonneg ‖p‖])

theorem gaussian_eighth_bound (R : ℝ) :
    R ^ 8 * Real.exp (-R ^ 2 / 4) ≤ 4 ^ (4 : ℕ) * Nat.factorial 4 := by
  have h := Real.pow_div_factorial_le_exp (R ^ 2 / 4) (by positivity) 4
  have he : Real.exp (R ^ 2 / 4) * Real.exp (-R ^ 2 / 4) = 1 := by
    rw [← Real.exp_add, show R ^ 2 / 4 + -R ^ 2 / 4 = 0 by ring, Real.exp_zero]
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (-R ^ 2 / 4)).le
  rw [he] at hh
  norm_num [Nat.factorial] at hh ⊢
  nlinarith

theorem decay {R : ℝ} (hR : 0 < R) (p w : Velocity)
    (h : R / 4 < ‖p‖ ∨ R / 2 < ‖w‖) :
    Real.exp (-‖w‖ ^ 2) * (polynomial p)⁻¹ ≤ constant / R ^ 8 := by
  have hpow : 0 < R ^ 8 := pow_pos hR _
  have hP := polynomial_pos p
  have he : Real.exp (-‖w‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  rcases h with hp | hw
  · have hb := polynomial_eighth_bound p (by positivity : 0 ≤ R / 4) hp.le
    have hi : (polynomial p)⁻¹ ≤ 4 ^ (8 : ℕ) / R ^ 8 := by
      apply (le_div_iff₀ hpow).mpr
      apply (inv_mul_le_iff₀ hP).mpr
      norm_num [div_pow] at hb ⊢
      nlinarith
    calc
      _ ≤ (polynomial p)⁻¹ := mul_le_of_le_one_left (inv_nonneg.mpr hP.le) he
      _ ≤ 4 ^ (8 : ℕ) / R ^ 8 := hi
      _ ≤ constant / R ^ 8 := by
        apply div_le_div_of_nonneg_right _ hpow.le
        norm_num [constant]
  · have hg := gaussian_shell_decay hR.le hw.le
    have ht : Real.exp (-R ^ 2 / 4) ≤
        (4 ^ (4 : ℕ) * Nat.factorial 4 : ℝ) / R ^ 8 := by
      apply (le_div_iff₀ hpow).mpr
      simpa only [mul_comm] using gaussian_eighth_bound R
    calc
      _ ≤ Real.exp (-‖w‖ ^ 2) :=
        mul_le_of_le_one_right (Real.exp_pos _).le (polynomial_inv_le_one p)
      _ ≤ Real.exp (-R ^ 2 / 4) := hg
      _ ≤ (4 ^ (4 : ℕ) * Nat.factorial 4 : ℝ) / R ^ 8 := ht
      _ ≤ constant / R ^ 8 := by
        apply div_le_div_of_nonneg_right _ hpow.le
        norm_num [constant]

end BoltzmannNonuniqueness.HotShellWeight

end

end

section

/-!
# Reduction of the original quadratic gain to a mixed gain

The reduction is proved in the original collision variables and uses no
additional change-of-variables hypothesis. This retains the bilinear form
covered by the published Carleman identity.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight

namespace BoltzmannNonuniqueness.HotGainReduction

theorem coefficient_nonneg (q : ℝ) (v : Velocity) : 0 ≤ coefficient q v := by
  unfold coefficient
  exact mul_nonneg (by positivity) (div_nonneg (H_nonneg q v) (G_pos q v).le)

theorem pair_bound (q : ℝ) (v w : Velocity) (ω : Sphere) :
    ENNReal.ofReal (H q (scatterLeft v w ω)) * ENNReal.ofReal (H q (scatterRight v w ω)) +
      ENNReal.ofReal (H q (scatterLeft v w ω)) * ENNReal.ofReal (H q (scatterRight v w ω)) ≤
    ENNReal.ofReal (coefficient q v) *
      (ENNReal.ofReal (H q (scatterLeft v w ω)) * ENNReal.ofReal (G q (scatterRight v w ω)) +
       ENNReal.ofReal (G q (scatterLeft v w ω)) * ENNReal.ofReal (H q (scatterRight v w ω))) := by
  have hω : ‖(ω : Velocity)‖ = 1 := by
    simpa only [Sphere, Metric.mem_sphere, dist_zero_right] using ω.property
  have he := scatter_energy v w ω hω
  have hv : ‖v‖ ^ 2 ≤ ‖scatterLeft v w ω‖ ^ 2 + ‖scatterRight v w ω‖ ^ 2 := by
    linarith [sq_nonneg ‖w‖]
  have hb := mul_le_mul_of_nonneg_left
    (quadratic_product_bound q (scatterLeft v w ω) (scatterRight v w ω) v hv)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hr : H q (scatterLeft v w ω) * H q (scatterRight v w ω) +
      H q (scatterLeft v w ω) * H q (scatterRight v w ω) ≤
      coefficient q v *
        (H q (scatterLeft v w ω) * G q (scatterRight v w ω) +
          G q (scatterLeft v w ω) * H q (scatterRight v w ω)) := by
    unfold coefficient
    rw [show (51 : ℕ) = 50 + 1 by rfl, pow_succ]
    linarith [hb]
  have hn := ENNReal.ofReal_le_ofReal hr
  simpa only [ENNReal.ofReal_add (mul_nonneg (H_nonneg _ _) (H_nonneg _ _))
      (mul_nonneg (H_nonneg _ _) (H_nonneg _ _)),
    ENNReal.ofReal_mul (coefficient_nonneg q v),
    ENNReal.ofReal_add (mul_nonneg (H_nonneg _ _) (G_pos _ _).le)
      (mul_nonneg (G_pos _ _).le (H_nonneg _ _)),
    ENNReal.ofReal_mul (H_nonneg _ _), ENNReal.ofReal_mul (G_pos _ _).le] using hn

/-- The factor `H(v)/G(v)` is essential: division by `H(v)` leaves a uniform
mixed-gain problem normalized by `G(v)`. -/
theorem quadratic_gain_le_mixed (q : ℝ) (v : Velocity) :
    nonnegativeGain (fun ξ => ENNReal.ofReal (H q ξ))
      (fun ξ => ENNReal.ofReal (H q ξ)) v ≤
    ENNReal.ofReal (coefficient q v) *
      nonnegativeGain (fun ξ => ENNReal.ofReal (H q ξ))
        (fun ξ => ENNReal.ofReal (G q ξ)) v := by
  unfold nonnegativeGain
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro p
  have h := mul_le_mul' (le_rfl : ENNReal.ofReal (collisionKernel v p.1 p.2) / 2 ≤ _)
    (pair_bound q v p.1 p.2)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ac_rfl

end BoltzmannNonuniqueness.HotGainReduction

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PowerDiskMixture
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The positive disk mixture for the truncated transverse power

The hot-gain estimate uses the finite measure with density
`(1 + ‖p‖⁻ᑫ) 1_{‖p‖ < D}`. Its singular part is a positive radius mixture
of centered disks. Values at the origin are irrelevant for this identity.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GaussianDiskMixture

namespace BoltzmannNonuniqueness.PowerDiskMixture

theorem integral_power_tail {q r D : ℝ} (hq : 0 < q) (hr : 0 < r) (hrD : r ≤ D) :
    (∫ a in Ioc r D, q * a ^ (-q - 1)) = r ^ (-q) - D ^ (-q) := by
  have hz : (0 : ℝ) ∉ uIcc r D := by
    rw [uIcc_of_le hrD]
    simp only [mem_Icc, not_and_or, not_le]
    exact Or.inl hr
  rw [← intervalIntegral.integral_of_le hrD, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inr ⟨by linarith, hz⟩)]
  rw [show -q - 1 + 1 = -q by ring]
  field_simp
  ring

theorem mixingDensity_nonneg {q a : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) :
    0 ≤ mixingDensity q a := by
  unfold mixingDensity
  exact mul_nonneg (mul_nonneg Real.pi_pos.le hq) (Real.rpow_nonneg ha _)

theorem measurable_mixingDensity (q : ℝ) : Measurable (mixingDensity q) := by
  unfold mixingDensity
  fun_prop

theorem integrableOn_mixingDensity {q D : ℝ} (hq : q < 2) (hD : 0 ≤ D) :
    IntegrableOn (mixingDensity q) (Ioc 0 D) := by
  have hi : IntervalIntegrable (fun a : ℝ => a ^ (1 - q)) volume 0 D :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hD).mp hi).const_mul (Real.pi * q)

theorem integral_mixingDensity {q D : ℝ} (hq : q < 2) (hD : 0 ≤ D) :
    (∫ a in Ioc 0 D, mixingDensity q a) =
      Real.pi * q / (2 - q) * D ^ (2 - q) := by
  unfold mixingDensity
  rw [← intervalIntegral.integral_of_le hD, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < 1 - q))]
  rw [show 1 - q + 1 = 2 - q by ring, Real.zero_rpow (by linarith : 2 - q ≠ 0)]
  ring

theorem layerCake_integrand (q : ℝ) (p : Transverse) {a : ℝ} (ha : 0 < a) :
    mixingDensity q a * diskDensity a p =
      (Ioi ‖p‖).indicator (fun a => q * a ^ (-q - 1)) a := by
  have hp : a ^ (1 - q) = a ^ (-q - 1) * a ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha]
    congr 1
    ring
  by_cases hm : ‖p‖ < a
  · rw [diskDensity_eq_ite, ite_eq_left hm, indicator_of_mem (show a ∈ Ioi ‖p‖ from hm)]
    unfold mixingDensity
    rw [hp]
    field_simp
  · rw [diskDensity_eq_ite, ite_eq_right hm, mul_zero,
      indicator_of_notMem (show a ∉ Ioi ‖p‖ from hm)]

/-- The singular radial density is a positive mixture of disks, away from its null origin. -/
theorem density_layerCake {q D : ℝ} (hq : 0 < q) (_hD : 0 < D)
    {p : Transverse} (hp : p ≠ 0) :
    cutoffDensity q D p =
      (1 + D ^ (-q)) * (ball (0 : Transverse) D).indicator (fun _ => 1) p +
        ∫ a in Ioc 0 D, mixingDensity q a * diskDensity a p := by
  have hr : 0 < ‖p‖ := norm_pos_iff.mpr hp
  by_cases hpd : ‖p‖ < D
  · have hi : Ioi ‖p‖ ∩ Ioc (0 : ℝ) D = Ioc ‖p‖ D := by
      ext a
      simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · tauto
      · intro ha
        exact ⟨ha.1, lt_trans hr ha.1, ha.2⟩
    rw [setIntegral_congr_fun measurableSet_Ioc
      (fun a ha => layerCake_integrand q p ha.1),
      integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
      hi, integral_power_tail hq hr hpd.le]
    simp only [cutoffDensity, indicator_of_mem (mem_ball_zero_iff.mpr hpd), mul_one]
    ring
  · have he : (∫ a in Ioc (0 : ℝ) D, mixingDensity q a * diskDensity a p) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      have hpa : ¬‖p‖ < a := not_lt.mpr (ha.2.trans (le_of_not_gt hpd))
      rw [diskDensity_eq_ite, ite_eq_right hpa, mul_zero]
      rfl
    rw [he]
    simp only [cutoffDensity, indicator_of_notMem (show p ∉ ball (0 : Transverse) D from
      fun h => hpd (mem_ball_zero_iff.mp h)), mul_zero, add_zero]

theorem layerCake_indicator (q D : ℝ) (p : Transverse) :
    (Ioc (0 : ℝ) D).indicator (fun a => mixingDensity q a * diskDensity a p) =
      (Ioc ‖p‖ D).indicator (fun a => q * a ^ (-q - 1)) := by
  funext a
  by_cases ha : a ∈ Ioc (0 : ℝ) D
  · rw [indicator_of_mem ha, layerCake_integrand q p ha.1]
    by_cases hp : ‖p‖ < a
    · rw [indicator_of_mem (show a ∈ Ioi ‖p‖ from hp),
        indicator_of_mem (show a ∈ Ioc ‖p‖ D from ⟨hp, ha.2⟩)]
    · rw [indicator_of_notMem (show a ∉ Ioi ‖p‖ from hp),
        indicator_of_notMem (show a ∉ Ioc ‖p‖ D from fun h => hp h.1)]
  · rw [indicator_of_notMem ha,
      indicator_of_notMem (show a ∉ Ioc ‖p‖ D from fun h =>
        ha ⟨lt_of_le_of_lt (norm_nonneg p) h.1, h.2⟩)]

theorem integrableOn_layerCake (q D : ℝ) {p : Transverse} (hp : p ≠ 0) :
    IntegrableOn (fun a => mixingDensity q a * diskDensity a p) (Ioc 0 D) := by
  rw [← integrable_indicator_iff measurableSet_Ioc, layerCake_indicator,
    integrable_indicator_iff measurableSet_Ioc]
  have hc : ContinuousOn (fun a : ℝ => q * a ^ (-q - 1)) (Icc ‖p‖ D) := by
    apply continuousOn_const.mul
    apply continuousOn_id.rpow_const
    intro a ha
    exact Or.inl (ne_of_gt (lt_of_lt_of_le (norm_pos_iff.mpr hp) ha.1))
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem boundaryMass_nonneg (q : ℝ) {D : ℝ} (hD : 0 ≤ D) : 0 ≤ boundaryMass q D := by
  unfold boundaryMass
  exact mul_nonneg (add_nonneg zero_le_one (Real.rpow_nonneg hD _))
    (mul_nonneg Real.pi_pos.le (sq_nonneg D))

theorem lintegral_density_layerCake {q D : ℝ} (hq : 0 < q) (hD : 0 < D)
    {p : Transverse} (hp : p ≠ 0) :
    ENNReal.ofReal (cutoffDensity q D p) =
      ENNReal.ofReal (boundaryMass q D) * ENNReal.ofReal (diskDensity D p) +
        ∫⁻ a in Ioc 0 D, ENNReal.ofReal (mixingDensity q a * diskDensity a p) := by
  have hn : ∀ᵐ a ∂volume.restrict (Ioc (0 : ℝ) D),
      0 ≤ mixingDensity q a * diskDensity a p := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    exact mul_nonneg (mixingDensity_nonneg hq.le ha.1.le) (diskDensity_nonneg a p)
  have hi := ofReal_integral_eq_lintegral_ofReal (integrableOn_layerCake q D hp) hn
  have hb : 0 ≤ (1 + D ^ (-q)) * (ball (0 : Transverse) D).indicator (fun _ => (1 : ℝ)) p :=
    mul_nonneg (by positivity) (indicator_nonneg (fun _ _ => by norm_num) p)
  rw [density_layerCake hq hD hp, ENNReal.ofReal_add hb
    (integral_nonneg_of_ae hn), hi]
  congr 1
  rw [← ENNReal.ofReal_mul (boundaryMass_nonneg q hD.le)]
  apply congrArg ENNReal.ofReal
  by_cases hm : p ∈ ball (0 : Transverse) D
  · rw [indicator_of_mem hm, diskDensity, indicator_of_mem hm]
    unfold boundaryMass
    field_simp
  · rw [indicator_of_notMem hm, diskDensity, indicator_of_notMem hm, mul_zero, mul_zero]

theorem measurable_diskDensity_fixed (a : ℝ) : Measurable (diskDensity a) := by
  have hm : Measurable (fun p : Transverse => (a, p)) := measurable_const.prodMk measurable_id
  simpa only [Function.comp_def] using measurable_diskDensity.comp hm

/-- Tonelli's theorem turns the density identity into a positive mixture for
every nonnegative measurable test, including singular kernel tests. -/
theorem lintegral_cutoff_mixture {q D : ℝ} (hq : 0 < q) (hD : 0 < D)
    (φ : Transverse → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ p, ENNReal.ofReal (cutoffDensity q D p) * φ p) =
      ENNReal.ofReal (boundaryMass q D) *
        (∫⁻ p, ENNReal.ofReal (diskDensity D p) * φ p) +
      ∫⁻ a in Ioc 0 D, ENNReal.ofReal (mixingDensity q a) *
        (∫⁻ p, ENNReal.ofReal (diskDensity a p) * φ p) := by
  have hprod : Measurable (fun pa : Transverse × ℝ =>
      ENNReal.ofReal (mixingDensity q pa.2 * diskDensity pa.2 pa.1) * φ pa.1) := by
    exact (((measurable_mixingDensity q).comp measurable_snd).mul
      (measurable_diskDensity.comp measurable_swap)).ennreal_ofReal.mul
        (hφ.comp measurable_fst)
  have hbase : Measurable (fun p : Transverse =>
      ENNReal.ofReal (boundaryMass q D) * ENNReal.ofReal (diskDensity D p) * φ p) :=
    (measurable_const.mul (measurable_diskDensity_fixed D).ennreal_ofReal).mul hφ
  calc
    _ = ∫⁻ p, ENNReal.ofReal (boundaryMass q D) * ENNReal.ofReal (diskDensity D p) * φ p +
        ∫⁻ a in Ioc 0 D, ENNReal.ofReal (mixingDensity q a * diskDensity a p) * φ p := by
      apply lintegral_congr_ae
      filter_upwards [volume.ae_ne (0 : Transverse)] with p hp
      rw [lintegral_density_layerCake hq hD hp, add_mul]
      have hm : Measurable (fun a : ℝ => ENNReal.ofReal (mixingDensity q a * diskDensity a p)) :=
        ((measurable_mixingDensity q).mul
          (measurable_diskDensity.comp (measurable_id.prodMk measurable_const))).ennreal_ofReal
      rw [lintegral_mul_const (φ p) hm]
    _ = ENNReal.ofReal (boundaryMass q D) *
        (∫⁻ p, ENNReal.ofReal (diskDensity D p) * φ p) +
        ∫⁻ a in Ioc 0 D, ∫⁻ p,
          ENNReal.ofReal (mixingDensity q a * diskDensity a p) * φ p := by
      rw [lintegral_add_left hbase]
      have hb : Measurable (fun p => ENNReal.ofReal (diskDensity D p) * φ p) :=
        (measurable_diskDensity_fixed D).ennreal_ofReal.mul hφ
      rw [show (fun p => ENNReal.ofReal (boundaryMass q D) *
          ENNReal.ofReal (diskDensity D p) * φ p) =
        (fun p => ENNReal.ofReal (boundaryMass q D) *
          (ENNReal.ofReal (diskDensity D p) * φ p)) by funext p; rw [mul_assoc],
        lintegral_const_mul _ hb, lintegral_lintegral_swap hprod.aemeasurable]
    _ = _ := by
      congr 1
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      simp_rw [ENNReal.ofReal_mul (mixingDensity_nonneg hq.le ha.1.le), mul_assoc]
      exact lintegral_const_mul _ ((measurable_diskDensity_fixed a).ennreal_ofReal.mul hφ)

end BoltzmannNonuniqueness.PowerDiskMixture

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotQuadraticGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Normalized truncated transverse weights

The positive disk mixture transfers the existing disk kernel expectation
bound to the truncated singular density needed by the quadratic hot gain.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.TransverseAverage
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.GaussianDiskMixture
open BoltzmannNonuniqueness.PowerDiskMixture

namespace BoltzmannNonuniqueness.HotDiskEstimate

theorem radiusMass_nonneg {q D : ℝ} (hq₁ : 0 ≤ q) (hq₂ : q < 2) (hD : 0 ≤ D) :
    0 ≤ radiusMass q D := by
  unfold radiusMass
  positivity

theorem cutoffMass_pos {q D : ℝ} (hq₁ : 0 ≤ q) (hq₂ : q < 2) (hD : 0 < D) :
    0 < cutoffMass q D := by
  have hb : 0 < boundaryMass q D := by
    unfold boundaryMass
    positivity
  exact add_pos_of_pos_of_nonneg hb (radiusMass_nonneg hq₁ hq₂ hD.le)

theorem mixing_mass {q D : ℝ} (hq₁ : 0 ≤ q) (hq₂ : q < 2) (hD : 0 ≤ D) :
    (∫⁻ a in Ioc 0 D, ENNReal.ofReal (PowerDiskMixture.mixingDensity q a)) =
      ENNReal.ofReal (radiusMass q D) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (PowerDiskMixture.integrableOn_mixingDensity hq₂ hD),
    PowerDiskMixture.integral_mixingDensity hq₂ hD]
  · rfl
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    exact PowerDiskMixture.mixingDensity_nonneg hq₁ ha.1.le

theorem cutoff_kernel_bound {q D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D)
    {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, extendedKernel q v p ∂cutoffLaw q D) ≤
      ENNReal.ofReal (cutoffMass q D) * ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  have hd (a : ℝ) (ha : 0 < a) :
      (∫⁻ p, ENNReal.ofReal (diskDensity a p) * extendedKernel q v p) ≤
        ENNReal.ofReal (expectationConstant q / ‖v‖) := by
    have h := uniformDisk_extendedKernel_lintegral_le hq₁ hq₂ ha hv
    rw [uniformDiskLaw, lintegral_withDensity_eq_lintegral_mul volume
      (measurable_diskDensity_fixed a).ennreal_ofReal (measurable_extendedKernel q v)] at h
    exact h
  have hm : Measurable (fun p => ENNReal.ofReal (cutoffDensity q D p)) := by
    unfold cutoffDensity
    apply Measurable.ennreal_ofReal
    apply Measurable.indicator _ measurableSet_ball
    fun_prop
  rw [cutoffLaw, lintegral_withDensity_eq_lintegral_mul volume hm (measurable_extendedKernel q v)]
  change (∫⁻ p, ENNReal.ofReal (cutoffDensity q D p) * extendedKernel q v p) ≤ _
  rw [lintegral_cutoff_mixture (by linarith : 0 < q) hD _ (measurable_extendedKernel q v)]
  calc
    _ ≤ ENNReal.ofReal (boundaryMass q D) * ENNReal.ofReal (expectationConstant q / ‖v‖) +
        ∫⁻ a in Ioc 0 D, ENNReal.ofReal (PowerDiskMixture.mixingDensity q a) *
          ENNReal.ofReal (expectationConstant q / ‖v‖) := by
      apply add_le_add (mul_le_mul' le_rfl (hd D hD))
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      exact mul_le_mul' le_rfl (hd a ha.1)
    _ = _ := by
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
        mixing_mass (by linarith : 0 ≤ q) hq₂ hD.le, ← add_mul,
        ← ENNReal.ofReal_add (boundaryMass_nonneg q hD.le)
          (radiusMass_nonneg (by linarith) hq₂ hD.le)]
      rfl

theorem normalizedCutoff_absolutelyContinuous (q D : ℝ) :
    normalizedCutoff q D ≪ volume := by
  intro s hs
  rw [normalizedCutoff, Measure.smul_apply]
  have hc : cutoffLaw q D s = 0 := withDensity_absolutelyContinuous volume _ hs
  rw [hc, smul_zero]

theorem normalizedCutoff_kernel_bound {q D : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D) {v : Transverse} (hv : v ≠ 0) :
    (∫⁻ p, extendedKernel q v p ∂normalizedCutoff q D) ≤
      ENNReal.ofReal (expectationConstant q / ‖v‖) := by
  rw [normalizedCutoff, lintegral_smul_measure]
  simp only [smul_eq_mul]
  apply (mul_le_mul' le_rfl (cutoff_kernel_bound hq₁ hq₂ hD hv)).trans_eq
  rw [← mul_assoc, ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (cutoffMass_pos (by linarith) hq₂ hD)))
    ENNReal.ofReal_ne_top, one_mul]

/-- The geometric slice estimate applies uniformly to the normalized hot measure. -/
theorem normalizedCutoff_geometric_bound {q D R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D) (hR : 1 ≤ R)
    {v : Transverse} (hv : v ≠ 0) (t : ℝ) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (∫⁻ p, normalizedBallSlice q v t p.1 p.2 R (-R) R
      ∂(normalizedCutoff q D).prod ρ) ≤ ENNReal.ofReal (geometricTotalConstant q * R ^ 2) :=
  geometric_total_of_kernel_bound hq₁ hq₂ hR hv t (normalizedCutoff q D) ρ
    ((normalizedCutoff_absolutelyContinuous q D).ae_le (ae_regularTransverse_volume hv))
    (normalizedCutoff_kernel_bound hq₁ hq₂ hD hv)

end BoltzmannNonuniqueness.HotDiskEstimate

end

end

section

/-!
# Collision-chart bounds for truncated hot weights

The transverse singular density is normalized explicitly. The axial factor is
normalized Lebesgue measure on a bounded interval. This supplies the geometric
ball estimate used in the polynomial shell summation.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.HotDiskEstimate
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.HotChartBalls

theorem intervalLaw_mass (D : ℝ) :
    intervalLaw D univ = ENNReal.ofReal (2 * D) := by
  simp only [intervalLaw, Measure.restrict_apply_univ, Real.volume_Ioo]
  congr 1
  ring

theorem normalizedInterval_isProbabilityMeasure {D : ℝ} (hD : 0 < D) :
    IsProbabilityMeasure (normalizedInterval D) := by
  constructor
  rw [normalizedInterval, Measure.smul_apply, smul_eq_mul, intervalLaw_mass]
  exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top

theorem rectangle_eq_smul {q D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D) :
    rectangleLaw q D =
      (ENNReal.ofReal (cutoffMass q D) * ENNReal.ofReal (2 * D)) • normalizedRectangle q D := by
  have : IsFiniteMeasure (intervalLaw D) := by unfold intervalLaw; infer_instance
  have : IsProbabilityMeasure (normalizedInterval D) := normalizedInterval_isProbabilityMeasure hD
  have : SFinite ((ENNReal.ofReal (2 * D))⁻¹ • intervalLaw D) :=
    inferInstanceAs (SFinite (normalizedInterval D))
  unfold normalizedRectangle normalizedCutoff normalizedInterval
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.map_smul, smul_smul]
  have hc : ENNReal.ofReal (cutoffMass q D) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (cutoffMass_pos (by linarith) hq₂ hD))
  have hd : ENNReal.ofReal (2 * D) ≠ 0 := by positivity
  rw [mul_mul_mul_comm, ENNReal.mul_inv_cancel hc ENNReal.ofReal_ne_top,
    ENNReal.mul_inv_cancel hd ENNReal.ofReal_ne_top, mul_one, one_smul]
  rfl

theorem weight_ball_normalizedRectangle_bound {q D R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) :
    chartRegionGain (normalizedRectangle q D) (weightRatio q v) v (ballRegion v R) ≤
      2 * ENNReal.ofReal (geometricTotalConstant q * R ^ 2) := by
  have := normalizedInterval_isProbabilityMeasure hD
  have hs := normalizedCutoff_geometric_bound hq₁ hq₂ hD hR hv (axial v)
    (normalizedInterval D)
  unfold chartRegionGain
  change 2 * (∫⁻ p, ballChartFiber q v p R ∂normalizedRectangle q D) ≤ _
  unfold normalizedRectangle
  rw [lintegral_map_equiv]
  exact mul_le_mul_right ((lintegral_mono (ballChartFiber_le_slice (by linarith) q v)).trans hs) 2

theorem weight_ball_rectangle_bound {q D R : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 0 < D) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) :
    ChartKernel.measure (rectangleLaw q D) (weightRatio q v) v (ballRegion v R) ≤
      (ENNReal.ofReal (cutoffMass q D) * ENNReal.ofReal (2 * D)) *
        (2 * ENNReal.ofReal (geometricTotalConstant q * R ^ 2)) := by
  rw [rectangle_eq_smul hq₁ hq₂ hD, measure_smul, Measure.smul_apply, smul_eq_mul]
  apply mul_le_mul' le_rfl
  rw [← region_eq_measure _ (UniformGain.measurable_weightRatio q v) _
    (UniformGain.measurableSet_ballRegion v R)]
  exact weight_ball_normalizedRectangle_bound hq₁ hq₂ hD hR hv

theorem massConstant_pos {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    0 < massConstant q := by unfold massConstant; positivity

theorem cutoffMass_le {q D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hD : 1 ≤ D) :
    cutoffMass q D ≤ massConstant q * D ^ 2 := by
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hneg : D ^ (-q) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      (Real.rpow_le_rpow_of_exponent_le hD (by linarith : -q ≤ 0))
  have hsmall : D ^ (2 - q) ≤ D ^ (2 : ℕ) := by
    simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] using
      (Real.rpow_le_rpow_of_exponent_le hD (by linarith : 2 - q ≤ (2 : ℝ)))
  have hb : PowerDiskMixture.boundaryMass q D ≤ 2 * Real.pi * D ^ 2 := by
    unfold PowerDiskMixture.boundaryMass
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 1 + D ^ (-q) ≤ 2) Real.pi_pos.le)
      (sq_nonneg D)
  have hr : radiusMass q D ≤ (Real.pi * q / (2 - q)) * D ^ 2 := by
    unfold radiusMass
    exact mul_le_mul_of_nonneg_left hsmall (by positivity)
  unfold cutoffMass massConstant
  nlinarith

end BoltzmannNonuniqueness.HotChartBalls

end

end

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

theorem measurableSet_rectangle (D : ℝ) : MeasurableSet (rectangle D) :=
  (measurableSet_lt ChartKernel.measurable_transverse.norm measurable_const).inter
    (ChartKernel.measurable_axial measurableSet_Ioo)

theorem measurable_weight (q D : ℝ) : Measurable (weight q D) :=
  ((ChartKernel.measurable_W q).ennreal_ofReal).indicator (measurableSet_rectangle D)

theorem join_measurePreserving :
    MeasurePreserving join ((volume : Measure Transverse).prod volume) volume := by
  have hs : MeasurePreserving split.symm
      ((volume : Measure ℝ).prod (volume : Measure Transverse)) volume := by
    simpa only [Measure.volume_eq_prod] using
      (MeasurePreserving.symm split split_measurePreserving)
  exact (Measure.measurePreserving_swap (μ := volume (α := Transverse))
    (ν := volume (α := ℝ))).trans hs

theorem join_withDensity (w : Velocity → ℝ≥0∞) :
    (((volume : Measure Transverse).prod volume).withDensity (fun p => w (join p))).map join =
      volume.withDensity w := by
  ext s hs
  rw [Measure.map_apply join.measurable hs, withDensity_apply _ (hs.preimage join.measurable),
    withDensity_apply _ hs, ← lintegral_indicator (hs.preimage join.measurable),
    ← lintegral_indicator hs,
    MeasurePreserving.lintegral_map_equiv (s.indicator w) join join_measurePreserving]
  apply lintegral_congr
  intro p
  rfl

theorem rectangleLaw_eq_density (q D : ℝ) :
    rectangleLaw q D = volume.withDensity (weight q D) := by
  have hm : Measurable (fun p : Transverse =>
      ENNReal.ofReal (PowerDiskMixture.cutoffDensity q D p)) := by
    unfold PowerDiskMixture.cutoffDensity
    apply Measurable.ennreal_ofReal
    apply Measurable.indicator _ measurableSet_ball
    fun_prop
  have hprod : (cutoffLaw q D).prod (intervalLaw D) =
      ((volume : Measure Transverse).prod volume).withDensity (fun p => weight q D (join p)) := by
    unfold cutoffLaw intervalLaw
    have hi : Measurable ((Ioo (-D) D).indicator (1 : ℝ → ℝ≥0∞)) :=
      measurable_const.indicator measurableSet_Ioo
    rw [← withDensity_indicator_one measurableSet_Ioo, prod_withDensity hm hi]
    congr 1
    funext p
    have ht : transverse (join p) = p.1 := PlaneChart.transverse_join _ _
    have ha : axial (join p) = p.2 := PlaneChart.axial_join _ _
    simp only [PowerDiskMixture.cutoffDensity, weight, rectangle, indicator_apply,
      mem_ofPred_eq, ht, ha, W, singularity]
    split_ifs <;> simp_all
  rw [rectangleLaw, hprod, join_withDensity]

theorem norm_ball_subset_rectangle {D : ℝ} {p : Velocity} (hp : ‖p‖ < D) :
    p ∈ rectangle D := by
  have ht : ‖transverse p‖ ≤ ‖p‖ := by
    nlinarith [norm_sq_split p, sq_nonneg (axial p), norm_nonneg (transverse p), norm_nonneg p]
  have ha : |axial p| ≤ ‖p‖ := by
    nlinarith [norm_sq_split p, sq_nonneg ‖transverse p‖, sq_abs (axial p),
      abs_nonneg (axial p), norm_nonneg p]
  exact ⟨ht.trans_lt hp, abs_lt.mp (ha.trans_lt hp)⟩

end BoltzmannNonuniqueness.HotRectangleDensity

end

end

section

/-! # Restricting the mixed hot gain to polynomial shells -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight
open BoltzmannNonuniqueness.HotChartBalls
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.HotMixedGain

theorem pointwise_bound (q : ℝ) (v : Velocity) (y : Coordinates) {A : ℝ}
    (h : Real.exp (-‖companionVelocity y.1 (chart v y.1 y.2.1 y.2.2) v‖ ^ 2) *
        (polynomial y.1)⁻¹ ≤ A) :
    ENNReal.ofReal (H q y.1) *
      density (fun ξ => ENNReal.ofReal (G q ξ / G q v)) v y ≤
    ENNReal.ofReal A * (ENNReal.ofReal (W q y.1) * density (weightRatio q v) v y) := by
  by_cases hn : normal v y.1 = 0
  · simp [density, hn]
  · have hw₁ := (W_pos q y.1).le
    have hw₂ := (W_pos q (chart v y.1 y.2.1 y.2.2)).le
    have hwv := (W_pos q v).le
    have hr : H q y.1 * (G q (chart v y.1 y.2.1 y.2.2) / G q v) ≤
        A * (W q y.1 * (W q (chart v y.1 y.2.1 y.2.2) / W q v)) := by
      rw [mixed_plane_weight q _ _ _ (chart_on_plane _ _ _ _ hn)]
      have hw : 0 ≤ W q y.1 * W q (chart v y.1 y.2.1 y.2.2) / W q v := by
        positivity
      convert mul_le_mul_of_nonneg_right h hw using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have hp := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_mul (H_nonneg q y.1),
      ENNReal.ofReal_mul' (by positivity : 0 ≤ W q y.1 *
        (W q (chart v y.1 y.2.1 y.2.2) / W q v)),
      ENNReal.ofReal_mul (W_pos q y.1).le] at hp
    have he := mul_le_mul_left hp (2 * ENNReal.ofReal (‖normal v y.1‖⁻¹))
    simpa only [density, weightRatio, mul_assoc, mul_left_comm, mul_comm] using he

theorem restricted_bound (q D : ℝ) (v : Velocity) {S : Set Coordinates}
    (hS : MeasurableSet S) (hball : S ⊆ ballRegion v D)
    (hp : ∀ y ∈ S, ‖y.1‖ < D + 1) {A : ℝ}
    (hA : ∀ y ∈ S,
      Real.exp (-‖companionVelocity y.1 (chart v y.1 y.2.1 y.2.2) v‖ ^ 2) *
        (polynomial y.1)⁻¹ ≤ A) :
    mixedMeasure q v S ≤ ENNReal.ofReal A *
      ChartKernel.measure (rectangleLaw q (D + 1)) (weightRatio q v) v (ballRegion v D) := by
  have hG : Measurable (fun ξ => ENNReal.ofReal (G q ξ / G q v)) :=
    ((measurable_G q).div_const _).ennreal_ofReal
  rw [mixedMeasure, measure_withDensity volume (measurable_H q).ennreal_ofReal hG v,
    HotRectangleDensity.rectangleLaw_eq_density,
    measure_withDensity volume (HotRectangleDensity.measurable_weight q (D + 1))
      (measurable_weightRatio q v) v,
    withDensity_apply _ hS, withDensity_apply _ (measurableSet_ballRegion v D),
    ← lintegral_indicator hS, ← lintegral_indicator (measurableSet_ballRegion v D),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro y
  dsimp only
  by_cases hy : y ∈ S
  · rw [indicator_of_mem hy, indicator_of_mem (hball hy)]
    have hm := HotRectangleDensity.norm_ball_subset_rectangle (hp y hy)
    rw [HotRectangleDensity.weight, indicator_of_mem hm]
    exact pointwise_bound q v y (hA y hy)
  · rw [indicator_of_notMem hy]
    exact bot_le

theorem core_bound (q : ℝ) (v : Velocity) :
    mixedMeasure q v (core v) ≤
      ChartKernel.measure (rectangleLaw q 3) (weightRatio q v) v (ballRegion v 2) := by
  have h := restricted_bound q 2 v (measurableSet_le (measurable_radius v) measurable_const)
    (fun y hy => (le_add_of_nonneg_left (norm_nonneg y.1)).trans hy)
    (fun y hy => by
      have hk := norm_nonneg (chart v y.1 y.2.1 y.2.2 - v)
      change ‖y.1‖ + ‖chart v y.1 y.2.1 y.2.2 - v‖ ≤ 2 at hy
      linarith)
    (A := 1) (fun y _ => by
      calc
        _ ≤ (polynomial y.1)⁻¹ := mul_le_of_le_one_left
          (inv_nonneg.mpr (polynomial_pos y.1).le)
          (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
        _ ≤ 1 := HotShellWeight.polynomial_inv_le_one y.1)
  norm_num at h
  exact h

theorem shell_bound (q : ℝ) (v : Velocity) {R : ℝ} (hR : 0 < R) :
    mixedMeasure q v (shell v R) ≤ ENNReal.ofReal (HotShellWeight.constant / R ^ 8) *
      ChartKernel.measure (rectangleLaw q (2 * R + 1)) (weightRatio q v) v (ballRegion v (2 * R)) := by
  apply restricted_bound q (2 * R) v (measurableSet_shell v R) (shell_subset_ball v R)
  · intro y hy
    have hk := norm_nonneg (chart v y.1 y.2.1 y.2.2 - v)
    change _ ∧ ‖y.1‖ + ‖chart v y.1 y.2.1 y.2.2 - v‖ ≤ 2 * R at hy
    linarith [hy.2]
  · intro y hy
    apply HotShellWeight.decay hR
    have hs := shell_alternative y.1 (chart v y.1 y.2.1 y.2.2 - v) hy.1
    simpa only [companionVelocity, sub_eq_add_neg, add_assoc] using hs

end BoltzmannNonuniqueness.HotMixedGain

end

end

section

/-! # Summation of the mixed hot gain -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotWeight
open BoltzmannNonuniqueness.HotChartBalls
open BoltzmannNonuniqueness.HotDiskEstimate
open BoltzmannNonuniqueness.HotMixedGain
open BoltzmannNonuniqueness.GeometricSlice
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain

namespace BoltzmannNonuniqueness.HotTotal

theorem geometricTotalConstant_pos {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    0 < geometricTotalConstant q := by
  unfold geometricTotalConstant
  exact mul_pos (by positivity) (geometricConstant_pos hq₁ hq₂)

theorem shell_real_bound {q R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 1 ≤ R) :
    (HotShellWeight.constant / R ^ 8) *
        ((cutoffMass q (2 * R + 1) * (2 * (2 * R + 1))) *
          (2 * (geometricTotalConstant q * (2 * R) ^ 2))) ≤ shellConstant q / R ^ 3 := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hD : 1 ≤ 2 * R + 1 := by linarith
  have hM := massConstant_pos hq₁ hq₂
  have hG := geometricTotalConstant_pos hq₁ hq₂
  have hc := HotShellWeight.constant_pos
  have hb := cutoffMass_le hq₁ hq₂ hD
  have hs : cutoffMass q (2 * R + 1) ≤ massConstant q * (3 * R) ^ 2 := by
    apply hb.trans
    gcongr
    linarith
  calc
    _ ≤ (HotShellWeight.constant / R ^ 8) *
        ((massConstant q * (3 * R) ^ 2 * (2 * (3 * R))) *
          (2 * (geometricTotalConstant q * (2 * R) ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hs (by linarith) (by positivity) (by positivity)
    _ = shellConstant q / R ^ 3 := by
      unfold shellConstant
      field_simp
      ring

theorem mixed_shell_bound {q R : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hR : 1 ≤ R)
    {v : Velocity} (hv : transverse v ≠ 0) :
    mixedMeasure q v (shell v R) ≤ ENNReal.ofReal (shellConstant q / R ^ 3) := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hm := cutoffMass_pos (by linarith : 0 ≤ q) hq₂ (by linarith : 0 < 2 * R + 1)
  have hg := geometricTotalConstant_pos hq₁ hq₂
  have hc := HotShellWeight.constant_pos
  have h := (shell_bound q v hRp).trans (mul_le_mul' le_rfl
    (weight_ball_rectangle_bound hq₁ hq₂ (by linarith) (by linarith) hv))
  have hh := ENNReal.ofReal_le_ofReal (shell_real_bound hq₁ hq₂ hR)
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ HotShellWeight.constant / R ^ 8),
    ENNReal.ofReal_mul (by positivity : 0 ≤ cutoffMass q (2 * R + 1) * (2 * (2 * R + 1))),
    ENNReal.ofReal_mul hm.le, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat] at hh
  simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_ofNat] at h hh
  exact h.trans hh

theorem bound_lt_top (q : ℝ) : bound q < ∞ := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ (3 : ℕ)) := by
    have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3 : ℕ))).comp_injective
      Nat.succ_injective
    simpa only [Function.comp_def, Nat.cast_succ] using h
  have hc : Summable (fun n : ℕ => shellConstant q / ((n : ℝ) + 1) ^ (3 : ℕ)) := by
    simpa only [mul_one_div] using hs.mul_left (shellConstant q)
  unfold bound baseBound
  exact ENNReal.add_lt_top.mpr ⟨by finiteness, hc.tsum_ofReal_lt_top⟩

theorem cover (v : Velocity) :
    (univ : Set Coordinates) ⊆ core v ∪ ⋃ n : ℕ, shell v ((n : ℝ) + 1) := by
  intro y _
  by_cases hr : radius v y ≤ 2
  · exact Or.inl hr
  · apply Or.inr
    have hr₂ : 2 < radius v y := lt_of_not_ge hr
    let n := Nat.floor (radius v y / 2)
    apply mem_iUnion.mpr
    refine ⟨n, ?_⟩
    have hn : (n : ℝ) ≤ radius v y / 2 := Nat.floor_le (by linarith)
    have hn' : radius v y / 2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    constructor <;> linarith

theorem mixed_total_bound {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2)
    {v : Velocity} (hv : transverse v ≠ 0) :
    mixedMeasure q v univ ≤ bound q := by
  have hb := (core_bound q v).trans (weight_ball_rectangle_bound
    (q := q) (D := 3) (R := 2) hq₁ hq₂ (by norm_num) (by norm_num) hv)
  have hbase : mixedMeasure q v (core v) ≤ baseBound q := by
    simpa only [baseBound, show (2 : ℝ) * 3 = 6 by norm_num] using hb
  calc
    _ ≤ mixedMeasure q v (core v ∪ ⋃ n : ℕ, shell v ((n : ℝ) + 1)) :=
      measure_mono (cover v)
    _ ≤ mixedMeasure q v (core v) + ∑' n : ℕ,
        mixedMeasure q v (shell v ((n : ℝ) + 1)) :=
      (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
    _ ≤ bound q := by
      apply add_le_add hbase
      apply ENNReal.tsum_le_tsum
      intro n
      exact mixed_shell_bound hq₁ hq₂ (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hv

end BoltzmannNonuniqueness.HotTotal

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

theorem gain_G_eq (c : Measure Velocity) (q : ℝ) (v : Velocity) :
    chartGain c (fun ξ => ENNReal.ofReal (G q ξ)) v =
      ENNReal.ofReal (G q v) *
        chartGain c (fun ξ => ENNReal.ofReal (G q ξ / G q v)) v := by
  have he : (fun ξ => ENNReal.ofReal (G q ξ)) =
      (fun ξ => ENNReal.ofReal (G q v) * ENNReal.ofReal (G q ξ / G q v)) := by
    funext ξ
    rw [← ENNReal.ofReal_mul (G_pos q v).le]
    congr 1
    field_simp [(G_pos q v).ne']
  rw [he, SheetApplication.gain_const_mul_right c _ v ENNReal.ofReal_ne_top]

theorem quadratic_gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∀ᵐ v : Velocity ∂volume,
      nonnegativeGain (fun ξ => ENNReal.ofReal (H q ξ))
        (fun ξ => ENNReal.ofReal (H q ξ)) v ≤
      ENNReal.ofReal (H q v) * (ENNReal.ofReal ((2 : ℝ) ^ (51 : ℕ)) * HotTotal.bound q) := by
  filter_upwards [hcarleman _ _ (measurable_H q).ennreal_ofReal
    (measurable_G q).ennreal_ofReal, SheetApplication.ae_transverse_ne_zero] with v hcar hv
  have hm : nonnegativeGain (fun ξ => ENNReal.ofReal (H q ξ))
      (fun ξ => ENNReal.ofReal (G q ξ)) v ≤
      ENNReal.ofReal (G q v) * HotTotal.bound q := by
    rw [hcar, gain_G_eq, total_eq _ ((measurable_G q).div_const _ |>.ennreal_ofReal)]
    exact mul_le_mul' le_rfl (HotTotal.mixed_total_bound hq₁ hq₂ hv)
  have hc : ENNReal.ofReal (HotGainReduction.coefficient q v) * ENNReal.ofReal (G q v) =
      ENNReal.ofReal ((2 : ℝ) ^ (51 : ℕ)) * ENNReal.ofReal (H q v) := by
    rw [← ENNReal.ofReal_mul (HotGainReduction.coefficient_nonneg q v),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ (51 : ℕ))]
    apply congrArg ENNReal.ofReal
    unfold HotGainReduction.coefficient
    rw [mul_assoc, div_mul_cancel₀ _ (G_pos q v).ne']
  calc
    _ ≤ ENNReal.ofReal (HotGainReduction.coefficient q v) *
        (ENNReal.ofReal (G q v) * HotTotal.bound q) :=
      (HotGainReduction.quadratic_gain_le_mixed q v).trans (mul_le_mul' le_rfl hm)
    _ = _ := by rw [← mul_assoc, hc]; ac_rfl

/-- Manuscript Lemma `lem:hot-bound`, for the fixed weight exponent `m = 100`. -/
theorem quadratic_gain_le_constant (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∀ᵐ v : Velocity ∂volume,
      nonnegativeGain (fun ξ => ENNReal.ofReal (H q ξ))
        (fun ξ => ENNReal.ofReal (H q ξ)) v ≤ ENNReal.ofReal (realBound q * H q v) := by
  have ht : ENNReal.ofReal ((2 : ℝ) ^ (51 : ℕ)) * HotTotal.bound q ≠ ∞ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (HotTotal.bound_lt_top q)).ne
  have hb : ENNReal.ofReal ((2 : ℝ) ^ (51 : ℕ)) * HotTotal.bound q ≤
      ENNReal.ofReal (realBound q) := by
    rw [realBound, ENNReal.ofReal_add ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal ht]
    exact le_add_of_nonneg_right zero_le
  filter_upwards [quadratic_gain_bound hcarleman hq₁ hq₂] with v hv
  apply hv.trans
  rw [mul_comm (realBound q), ENNReal.ofReal_mul (H_nonneg q v)]
  exact mul_le_mul' le_rfl hb

end BoltzmannNonuniqueness.HotApplication

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotPhysicalSource
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
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

theorem ae_good_q80_oai (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) : ∀ᵐ v : Velocity, v ∈ good q :=
  HotApplication.quadratic_gain_le_constant hcarleman hq₁ hq₂

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.HotRepresentative.ae_good_q80_oai := @OAI.BoltzmannNonuniqueness.HotRepresentative.ae_good_q80_oai
