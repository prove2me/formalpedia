-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:36:21.947295+00:00
-- url     : https://prove2.me/submissions/c5e7b7b7-0f30-4777-a42f-6d83774fa35e

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_CapApproximation_escapedTotal_bound_global_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_CapApproximation_rescaled_cold_measure_majorant_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_selectedRemainder_gain_bound_q80

section
-- module Solutions.OAIQ080_BZ.Compat
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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.TransverseAverage.circleArea_isFiniteMeasure _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

/-- Gaussian decay retains transverse powers whenever their exponent exceeds `-2`. -/
theorem integrable_transverse_gaussian_rpow {β s : ℝ} (hβ : 0 < β) (hs : -2 < s) :
    Integrable (fun u : Transverse => ‖u‖ ^ s * Real.exp (-β * ‖u‖ ^ 2)) := by
  apply (integrable_fun_norm_addHaar (volume : Measure Transverse)
    (f := fun r : ℝ => r ^ s * Real.exp (-β * r ^ 2))).mpr
  have hi : IntegrableOn (fun r : ℝ => r ^ (s + 1) * Real.exp (-β * r ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hβ (by linarith)
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  have hr' : 0 < r := hr
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, pow_one, smul_eq_mul]
  rw [Real.rpow_add hr' s 1, Real.rpow_one]
  ring

theorem integrable_gaussianMajorant {β q : ℝ} (hβ : 0 < β) (hq : q < 2) :
    Integrable (gaussianMajorant β q) := by
  have hb₀ : Integrable (fun u : Transverse => Real.exp (-β * ‖u‖ ^ 2)) := by
    simpa only [Real.rpow_zero, one_mul] using
      integrable_transverse_gaussian_rpow (s := 0) hβ (by norm_num)
  have hb₁ := integrable_transverse_gaussian_rpow (s := -q) hβ (by linarith)
  have hb : Integrable (fun u : Transverse =>
      (1 + singularity q u) * Real.exp (-β * ‖u‖ ^ 2)) := by
    convert hb₀.add hb₁ using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    simp only [singularity, Pi.add_apply]
    ring
  have ha := integrable_exp_neg_mul_sq hβ
  have hp := ha.mul_prod hb
  have hc := split_measurePreserving.integrable_comp_of_integrable hp
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  simp only [gaussianMajorant, Function.comp_apply, split_apply]
  have he : Real.exp (-β * ‖v‖ ^ 2) =
      Real.exp (-β * ‖transverse v‖ ^ 2) * Real.exp (-β * (axial v) ^ 2) := by
    rw [norm_sq_split, mul_add, Real.exp_add]
  rw [he]
  ring

theorem H_nonneg (q : ℝ) (v : Velocity) : 0 ≤ H q v := by
  unfold H singularity
  positivity

theorem H_le_gaussianMajorant (q : ℝ) (v : Velocity) :
    H q v ≤ gaussianMajorant 1 q v := by
  have hp : (1 + ‖v‖ ^ 2) ^ (-50 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (sq_nonneg _)) (by norm_num)
  unfold H gaussianMajorant
  simp only [neg_mul, one_mul]
  have hw : 0 ≤ 1 + singularity q (transverse v) :=
    add_nonneg zero_le_one (singularity_nonneg q (transverse v))
  simpa only [mul_one] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)) hw

theorem integrable_H {q : ℝ} (hq : q < 2) : Integrable (H q) := by
  apply (integrable_gaussianMajorant zero_lt_one hq).mono'
  · unfold H singularity transverse
    fun_prop
  · filter_upwards [] with v
    rw [Real.norm_eq_abs, abs_of_nonneg (H_nonneg q v)]
    exact H_le_gaussianMajorant q v

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

theorem tiltConstant_pos : 0 < tiltConstant := by unfold tiltConstant; positivity

theorem polynomial_le_gaussian (p : Velocity) :
    (1 + ‖p‖ ^ 2) ^ (50 : ℕ) ≤ tiltConstant * Real.exp (‖p‖ ^ 2) := by
  have hf : 0 < (Nat.factorial 50 : ℝ) := by positivity
  have h := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (1 + ‖p‖ ^ 2) (by positivity) 50)
  calc
    _ ≤ Real.exp (1 + ‖p‖ ^ 2) * (Nat.factorial 50 : ℝ) := h
    _ = _ := by unfold tiltConstant; rw [Real.exp_add]; ring

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

theorem chartGain_mono_right {c : Measure Velocity} {h k : Velocity → ℝ≥0∞}
    (hkh : ∀ ξ, h ξ ≤ k ξ) (v : Velocity) : chartGain c h v ≤ chartGain c k v := by
  unfold chartGain
  gcongr
  exact hkh _

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

end BoltzmannNonuniqueness

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

theorem gain_mono {f g : Velocity → ℝ} (hm : Measurable f)
    (hf : ∀ w, 0 ≤ f w) (hfg : ∀ w, f w ≤ g w) (v : Velocity) (x : Position)
    (hg : Integrable (integrand g v) ((volume : Measure Velocity).prod sphereArea)) :
    gain (fun p => f p.2) x v ≤ gain (fun p => g p.2) x v :=
  integral_mono (integrable_of_le hm hf hfg v hg) hg (integrand_mono hf hfg v)

theorem gain_const_mul (c : ℝ) (f : Velocity → ℝ) (v : Velocity) (x : Position) :
    gain (fun p => c * f p.2) x v = c ^ 2 * gain (fun p => f p.2) x v := by
  unfold gain
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with p
  ring

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Measure preservation for a hard-sphere collision

For each fixed unit normal, the pre/post-collisional map is an orthogonal
involution on the six-dimensional velocity-pair space. Its Euclidean norm is
implemented with `WithLp 2`; the final measure statement uses the ordinary
product of the two three-dimensional Lebesgue measures.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

/-- Fixed-normal pre/post collision change of variables preserves product Lebesgue measure. -/
theorem scatterPair_measurePreserving (ω : Velocity) (hω : ‖ω‖ = 1) :
    MeasurePreserving (scatterPair ω)
      ((volume : Measure Velocity).prod volume)
      ((volume : Measure Velocity).prod volume) := by
  have h := (WithLp.volume_preserving_ofLp Velocity Velocity).comp
    ((scatterLinearIsometryEquiv ω hω).measurePreserving.comp
      (WithLp.volume_preserving_toLp Velocity Velocity))
  exact h

/-- The relative velocity is reflected in the plane normal to the collision normal. -/
theorem scatter_relative_velocity (v w ω : Velocity) :
    scatterLeft v w ω - scatterRight v w ω =
      (v - w) - (2 * normalComponent v w ω) • ω := by
  unfold scatterLeft scatterRight
  module

/-- A unit-normal collision preserves the relative speed. -/
theorem scatter_relative_speed (v w ω : Velocity) (hω : ‖ω‖ = 1) :
    ‖scatterLeft v w ω - scatterRight v w ω‖ = ‖v - w‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [scatter_relative_velocity, norm_sub_sq_real]
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, hω, mul_one, sq_abs]
  unfold normalComponent
  ring

end BoltzmannNonuniqueness

end

end

section

/-! # The relative-speed cutoff used in the finite approximations -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCutoff

theorem kernel_scatter (b : ℝ) (v w : Velocity) (ω : Sphere) :
    kernel b (scatterLeft v w ω) (scatterRight v w ω) ω = kernel b v w ω := by
  simp only [kernel, scatter_relative_speed v w ω (mem_sphere_zero_iff_norm.mp ω.property),
    collisionKernel_scatter v w ω (mem_sphere_zero_iff_norm.mp ω.property)]

theorem rate_nonneg (b : ℝ) (v w : Velocity) : 0 ≤ rate b v w := by
  unfold rate
  split_ifs <;> positivity

theorem rate_le {b : ℝ} (hb : 0 ≤ b) (v w : Velocity) : rate b v w ≤ b := by
  unfold rate
  split_ifs with h
  · exact h.le
  · exact hb

theorem measurable_rate (b : ℝ) (v : Velocity) : Measurable (rate b v) := by
  unfold rate
  exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) (by fun_prop) measurable_const

theorem integrable_frequency {b : ℝ} (hb : 0 ≤ b) {f : Velocity → ℝ} (hf : Integrable f)
    (v : Velocity) : Integrable (fun w => rate b v w * f w) := by
  apply (hf.norm.const_mul b).mono' ((measurable_rate b v).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [] with w
  dsimp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (rate_nonneg b v w)]
  exact mul_le_mul_of_nonneg_right (rate_le hb v w) (norm_nonneg _)

theorem abs_frequency_le {b : ℝ} (hb : 0 ≤ b) {f : Velocity → ℝ} (hf : Integrable f)
    (v : Velocity) : |frequency b f v| ≤ 2 * Real.pi * b * ∫ w, |f w| := by
  have hi := integrable_frequency hb hf v
  have hm : Integrable (fun w => b * |f w|) := by simpa only [Real.norm_eq_abs] using hf.norm.const_mul b
  have hpoint (w : Velocity) : |rate b v w * f w| ≤ b * |f w| := by
    rw [abs_mul, abs_of_nonneg (rate_nonneg b v w)]
    exact mul_le_mul_of_nonneg_right (rate_le hb v w) (abs_nonneg _)
  calc
    _ = 2 * Real.pi * |∫ w, rate b v w * f w| := by
      rw [frequency, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    _ ≤ 2 * Real.pi * ∫ w, |rate b v w * f w| :=
      mul_le_mul_of_nonneg_left abs_integral_le_integral_abs (by positivity)
    _ ≤ 2 * Real.pi * ∫ w, b * |f w| := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono (by simpa only [Real.norm_eq_abs] using hi.norm) hm hpoint
    _ = _ := by rw [integral_const_mul]; ring

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

theorem integrand_le (b : ℝ) {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (p : Velocity × Sphere) : integrand b f v p ≤ GainOrder.integrand f v p := by
  unfold integrand GainOrder.integrand
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (kernel_le b v p.1 p.2) (hf _)) (hf _)

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

theorem gain_le (b : ℝ) {f : Velocity → ℝ} (hm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (v : Velocity) (x : Position)
    (hi : Integrable (GainOrder.integrand f v) ((volume : Measure Velocity).prod sphereArea)) :
    gain b f v ≤ BoltzmannNonuniqueness.gain (fun p => f p.2) x v :=
  integral_mono (integrable_gain b hm hf v hi) hi (integrand_le b hf v)

end BoltzmannNonuniqueness.CollisionCutoff

end

end

section

/-! # Collision operators respect almost-everywhere representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.CollisionNullSets

theorem left_pair (ω : Sphere) : QuasiMeasurePreserving
    (fun p : Velocity × Velocity => scatterLeft p.1 p.2 ω)
    ((volume : Measure Velocity).prod volume) volume :=
  MeasureTheory.QuasiMeasurePreserving.fst
    (scatterPair_measurePreserving ω (mem_sphere_zero_iff_norm.mp ω.property)).quasiMeasurePreserving

theorem right_pair (ω : Sphere) : QuasiMeasurePreserving
    (fun p : Velocity × Velocity => scatterRight p.1 p.2 ω)
    ((volume : Measure Velocity).prod volume) volume :=
  MeasureTheory.QuasiMeasurePreserving.snd
    (scatterPair_measurePreserving ω (mem_sphere_zero_iff_norm.mp ω.property)).quasiMeasurePreserving

theorem left_quasiMeasurePreserving : QuasiMeasurePreserving left
    ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) volume := by
  let : SFinite ((volume : Measure Velocity).prod (volume : Measure Velocity)) := Measure.prod.instSFinite
  have h : QuasiMeasurePreserving
      (fun p : (Velocity × Velocity) × Sphere => scatterLeft p.1.1 p.1.2 p.2)
      (((volume : Measure Velocity).prod volume).prod sphereArea) volume := by
    apply MeasureTheory.QuasiMeasurePreserving.prod_of_left
    · unfold scatterLeft normalComponent
      fun_prop
    · exact ae_of_all _ left_pair
  exact h.comp ((measurePreserving_prodAssoc (volume : Measure Velocity) volume sphereArea).symm
    MeasurableEquiv.prodAssoc).quasiMeasurePreserving

theorem right_quasiMeasurePreserving : QuasiMeasurePreserving right
    ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) volume := by
  let : SFinite ((volume : Measure Velocity).prod (volume : Measure Velocity)) := Measure.prod.instSFinite
  have h : QuasiMeasurePreserving
      (fun p : (Velocity × Velocity) × Sphere => scatterRight p.1.1 p.1.2 p.2)
      (((volume : Measure Velocity).prod volume).prod sphereArea) volume := by
    apply MeasureTheory.QuasiMeasurePreserving.prod_of_left
    · unfold scatterRight normalComponent
      fun_prop
    · exact ae_of_all _ right_pair
  exact h.comp ((measurePreserving_prodAssoc (volume : Measure Velocity) volume sphereArea).symm
    MeasurableEquiv.prodAssoc).quasiMeasurePreserving

end BoltzmannNonuniqueness.CollisionNullSets

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticDensityMeasurable
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Collision representative invariance with space and time parameters -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.KineticCollisionNullSets

variable {X : Type*} [MeasurableSpace X]

theorem left_quasiMeasurePreserving (μ : Measure X) [SFinite μ] :
    QuasiMeasurePreserving (left (X := X))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea))
      (μ.prod (volume : Measure Velocity)) := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  let : SFinite ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) :=
    Measure.prod.instSFinite
  have h := MeasureTheory.QuasiMeasurePreserving.prodMap
    (MeasurePreserving.id μ).quasiMeasurePreserving CollisionNullSets.left_quasiMeasurePreserving
  exact h.comp (measurePreserving_prodAssoc μ (volume : Measure Velocity)
    ((volume : Measure Velocity).prod sphereArea)).quasiMeasurePreserving

theorem right_quasiMeasurePreserving (μ : Measure X) [SFinite μ] :
    QuasiMeasurePreserving (right (X := X))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea))
      (μ.prod (volume : Measure Velocity)) := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  let : SFinite ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) :=
    Measure.prod.instSFinite
  have h := MeasureTheory.QuasiMeasurePreserving.prodMap
    (MeasurePreserving.id μ).quasiMeasurePreserving CollisionNullSets.right_quasiMeasurePreserving
  exact h.comp (measurePreserving_prodAssoc μ (volume : Measure Velocity)
    ((volume : Measure Velocity).prod sphereArea)).quasiMeasurePreserving

theorem gain_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (b : ℝ) : gain b f =ᵐ[μ.prod volume] gain b g := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  have hl := ae_ae_of_ae_prod ((left_quasiMeasurePreserving μ).ae hfg)
  have hr := ae_ae_of_ae_prod ((right_quasiMeasurePreserving μ).ae hfg)
  filter_upwards [hl, hr] with p hlp hrp
  apply integral_congr_ae
  filter_upwards [hlp, hrp] with q hlq hrq
  change f (p.1, scatterLeft p.2 q.1 q.2) = g (p.1, scatterLeft p.2 q.1 q.2) at hlq
  change f (p.1, scatterRight p.2 q.1 q.2) = g (p.1, scatterRight p.2 q.1 q.2) at hrq
  unfold CollisionCutoff.integrand
  dsimp only
  rw [hlq, hrq]

theorem measurable_gain {f : X × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (gain b f) := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  have hL : Measurable (fun p : (X × Velocity) × (Velocity × Sphere) => f (left p)) := by
    apply hf.comp
    unfold left scatterLeft normalComponent
    fun_prop
  have hR : Measurable (fun p : (X × Velocity) × (Velocity × Sphere) => f (right p)) := by
    apply hf.comp
    unfold right scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : (X × Velocity) × (Velocity × Sphere) =>
      CollisionCutoff.kernel b p.1.2 p.2.1 p.2.2) := by
    unfold CollisionCutoff.kernel
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    · unfold collisionKernel normalComponent
      fun_prop
    · exact measurable_const
  exact ((hk.mul hL).mul hR).stronglyMeasurable.integral_prod_right.measurable

theorem measurable_frequency {f : X × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (frequency b f) := by
  have hk : Measurable (fun p : (X × Velocity) × Velocity =>
      CollisionCutoff.rate b p.1.2 p.2) := by
    unfold CollisionCutoff.rate
    exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (by fun_prop) measurable_const
  have hm : Measurable (fun p : (X × Velocity) × Velocity => f (p.1.1, p.2)) := by
    exact hf.comp (measurable_fst.fst.prodMk measurable_snd)
  exact measurable_const.mul (hk.mul hm).stronglyMeasurable.integral_prod_right.measurable

end BoltzmannNonuniqueness.KineticCollisionNullSets

end

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

section

/-! # Joint measurability of the collision-plane chart and normalized density -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.ChartKernel

theorem measurable_joint_normalized_density (q : ℝ) :
    Measurable (fun p : Velocity × Coordinates =>
      density (fun ξ => ENNReal.ofReal (H q ξ/H q p.1)) p.1 p.2) := by
  have hn : Measurable (fun p : Velocity × Coordinates => normal p.1 p.2.1) :=
    measurable_transverse.comp (measurable_fst.sub measurable_snd.fst)
  exact (measurable_const.mul hn.norm.inv.ennreal_ofReal).mul
    (((measurable_H q).comp measurable_joint_point).div
      ((measurable_H q).comp measurable_fst)).ennreal_ofReal

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Pulling the joint chart through a kinetic base projection -/

noncomputable section
open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.ChartKernel
variable {X : Type*} [MeasurableSpace X]

theorem measurable_lifted_density (q : ℝ) :
    Measurable (fun p : (X × Velocity) × Coordinates =>
      density (fun ξ => ENNReal.ofReal (H q ξ/H q p.1.2)) p.1.2 p.2) := by
  let f : (X × Velocity) × Coordinates → Velocity × Coordinates := fun p => (p.1.2,p.2)
  have hf : Measurable f := measurable_fst.snd.prodMk measurable_snd
  simpa only [Function.comp_def,f] using (measurable_joint_normalized_density q).comp hf

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

theorem realBound_pos (q : ℝ) : 0 < realBound q := by
  unfold realBound
  positivity

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

end BoltzmannNonuniqueness.MixedRealGain

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarriers
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

/-! # Velocity support and spatial confinement of the free cold cores -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetSupport

theorem initial_spatial_support (η K α γ s d : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : JetPrototype.density η K α γ s d a p ≠ 0) :
    p.1.1 ∈ mask η s a ∧ |p.1.2| < 1 / 8 := by
  have hsp : spatial η K γ s a p.1 ≠ 0 := left_ne_zero_of_mul hp
  have hm : (mask η s a).indicator (fun _ => (1 : ℝ)) p.1.1 ≠ 0 := left_ne_zero_of_mul hsp
  have hz : axialAmplitude K γ s p.1.2 ≠ 0 := right_ne_zero_of_mul hsp
  have hy : p.1.1 ∈ mask η s a := by
    by_contra h
    exact hm (indicator_of_notMem h _)
  have hz' : p.1.2 ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8) := by
    by_contra h
    exact hz (indicator_of_notMem h _)
  exact ⟨hy, abs_lt.mpr hz'⟩

end BoltzmannNonuniqueness.JetSupport

end

end

section

/-! # Gaussian decay of a cold barrier away from its spatial core -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetGaussianEscape

theorem gaussian_le_hot (q : ℝ) (v : Velocity) :
    Real.exp (-2 * ‖v‖ ^ 2) ≤ tiltConstant * H q v := by
  have hp := polynomial_le_gaussian v
  have hw : 1 ≤ W q v := by unfold W; linarith [singularity_nonneg q (transverse v)]
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (-2 * ‖v‖ ^ 2))
  have hexp : Real.exp (-2 * ‖v‖ ^ 2) * Real.exp (‖v‖ ^ 2) = Real.exp (-‖v‖ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : Real.exp (-2 * ‖v‖ ^ 2) * HotWeight.polynomial v ≤
      tiltConstant * HotWeight.G q v := by
    calc
      _ ≤ tiltConstant * Real.exp (-‖v‖ ^ 2) := by
        change Real.exp (-2 * ‖v‖ ^ 2) * (1 + ‖v‖ ^ 2) ^ (50 : ℕ) ≤ _
        calc
          _ ≤ Real.exp (-2 * ‖v‖ ^ 2) * (tiltConstant * Real.exp (‖v‖ ^ 2)) := hm
          _ = _ := by rw [mul_left_comm, hexp]
      _ ≤ _ := by
        unfold HotWeight.G
        simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left hw
          (mul_nonneg tiltConstant_pos.le (Real.exp_nonneg (-‖v‖ ^ 2)))
  rw [← HotWeight.H_mul_polynomial] at hprod
  exact (mul_le_mul_iff_of_pos_right (HotWeight.polynomial_pos v)).mp (by
    simpa only [mul_assoc] using hprod)

end BoltzmannNonuniqueness.JetGaussianEscape

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

/-! # Integration of the nonnegative, disjoint cold-jet series -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetSeries

theorem summable_single_support {ι : Type*} {f : ι → ℝ}
    (hf : ∀ i j, i ≠ j → f i ≠ 0 → f j = 0) : Summable f := by
  classical
  by_cases h : ∃ i, f i ≠ 0
  · obtain ⟨i, hi⟩ := h
    exact summable_of_ne_finset_zero (s := {i}) (fun j hj => hf i j (by simpa [eq_comm] using hj) hi)
  · have he : f = 0 := by ext i; simpa using not_exists.mp h i
    rw [he]
    exact summable_zero

end BoltzmannNonuniqueness.JetSeries

end

end

section

/-! # The full unperiodized cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetDatum

theorem term_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ : ℝ) (i : Index) (p : JetPrototype.Phase) : 0 ≤ term s₀ η K α γ d₀ i p :=
  density_nonneg hK (DatumBounds.scale_pos hs₀ _).le
    (mul_nonneg hd₀ (pow_nonneg (DatumBounds.scale_pos hs₀ _).le _)) η α γ i.2 p

theorem term_measurable (s₀ η K α γ d₀ : ℝ) (i : Index) :
    Measurable (term s₀ η K α γ d₀ i) := measurable_density _ _ _ _ _ _ _

end BoltzmannNonuniqueness.JetDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedKernelAction
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The normalized Carleman gain as a measurable velocity kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

theorem coordinateKernel_apply (c : Kernel X Velocity) [IsSFiniteKernel c]
    (q : ℝ) (z : X × Velocity) :
    coordinateKernel c q z = normalizedMeasure (c z.1) q z.2 := by
  rw [coordinateKernel,Kernel.withDensity_apply _ (measurable_lifted_density q),Kernel.prod_apply]
  rfl

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # S-finiteness and integration for the normalized gain input kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

theorem lintegral_inputKernel (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ)
    (z : X × Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ v, f v ∂inputKernel c q z) =
      ∫⁻ y, f (PlaneChart.chart z.2 y.1 y.2.1 y.2.2)
        ∂normalizedMeasure (c z.1) q z.2 := by
  change (∫⁻ v, f v ∂(coordinateKernel c q z).map
    (fun y => PlaneChart.chart z.2 y.1 y.2.1 y.2.2)) = _
  rw [lintegral_map hf (measurable_point z.2),coordinateKernel_apply]

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Integrating an input against the normalized collision kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

theorem measure_weighted (c : Measure Velocity) {h f : Velocity → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) (v : Velocity) :
    (measure c h v).withDensity (fun y => f (PlaneChart.chart v y.1 y.2.1 y.2.2)) =
      measure c (fun ξ => h ξ*f ξ) v := by
  have ht : Measurable (fun y : Coordinates => f (PlaneChart.chart v y.1 y.2.1 y.2.2)) :=
    hf.comp (measurable_point v)
  rw [measure,← withDensity_mul _ (measurable_density hh v) ht]
  congr 1
  funext y
  unfold density
  exact mul_assoc _ _ _

theorem lintegral_normalized (c : Measure Velocity) (q : ℝ) (v : Velocity)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f (PlaneChart.chart v y.1 y.2.1 y.2.2) ∂normalizedMeasure c q v) =
      chartGain c (fun ξ => ENNReal.ofReal (H q ξ/H q v)*f ξ) v := by
  have hh := ((measurable_H q).div_const (H q v)).ennreal_ofReal
  calc
    _ = ((measure c (fun ξ => ENNReal.ofReal (H q ξ/H q v)) v).withDensity
        (fun y => f (PlaneChart.chart v y.1 y.2.1 y.2.2))) univ := by
      rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      rfl
    _ = (measure c (fun ξ => ENNReal.ofReal (H q ξ/H q v)*f ξ) v) univ :=
      congrArg (fun μ : Measure Coordinates => μ univ) (measure_weighted c hh hf v)
    _ = _ := (total_eq c (hh.mul hf) v).symm

theorem lintegral_inputKernel_eq_gain {X : Type*} [MeasurableSpace X]
    (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) (z : X × Velocity)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂inputKernel c q z) =
      chartGain (c z.1) (fun ξ => ENNReal.ofReal (H q ξ/H q z.2)*f ξ) z.2 := by
  rw [lintegral_inputKernel c q z hf,lintegral_normalized (c z.1) q z.2 hf]

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Collision identity and representative invariance of normalized gain -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem chartGain_const_mul_right (c : Measure Velocity) (a : ℝ≥0∞) (ha : a ≠ ∞)
    (h : Velocity → ℝ≥0∞) (v : Velocity) :
    chartGain c (fun ξ => a*h ξ) v = a*chartGain c h v := by
  unfold chartGain
  simp_rw [lintegral_const_mul' a _ ha,
    show ∀ p : Velocity,
      ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹)*
        (a*∫⁻ z : ℝ, ∫⁻ s : ℝ, h (PlaneChart.chart v p z s)) =
      a*(ENNReal.ofReal (‖PlaneChart.normal v p‖⁻¹)*
        ∫⁻ z : ℝ, ∫⁻ s : ℝ, h (PlaneChart.chart v p z s)) by intro p; ac_rfl]
  rw [lintegral_const_mul' a _ ha]
  ac_rfl

end BoltzmannNonuniqueness

end

end

section

/-! # The normalized gain of the fixed velocity weight -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

theorem normalized_weight_gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∀ᵐ v : Velocity, normalizedChartGain
      (volume.withDensity (fun p => ENNReal.ofReal (H q p))) q v ≤
        ENNReal.ofReal (HotApplication.realBound q) := by
  filter_upwards [hcarleman _ _ (measurable_H q).ennreal_ofReal (measurable_H q).ennreal_ofReal,
    HotApplication.quadratic_gain_le_constant hcarleman hq₁ hq₂] with v hc hb
  rw [hc,SheetApplication.gain_H_eq, mul_comm (HotApplication.realBound q),
    ENNReal.ofReal_mul (H_nonneg q v)] at hb
  exact (ENNReal.mul_le_mul_iff_right (ne_of_gt (ENNReal.ofReal_pos.mpr (H_pos q v))) ENNReal.ofReal_ne_top).mp hb

theorem normalized_weight_scaled_bound (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (a : ℝ≥0∞) :
    ∀ᵐ v : Velocity, normalizedChartGain
      (a • volume.withDensity (fun p => ENNReal.ofReal (H q p))) q v ≤
        a*ENNReal.ofReal (HotApplication.realBound q) := by
  filter_upwards [normalized_weight_gain_bound hcarleman hq₁ hq₂] with v hv
  change chartGain _ _ _ ≤ _
  rw [chartGain_smul_measure]
  exact mul_le_mul' le_rfl hv

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetCoreMomentBound
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

theorem coefficient_nonneg {K d₀ : ℝ} (hK : 0 ≤ K) (hd₀ : 0 < d₀) (α : ℝ) :
    0 ≤ coefficient α K d₀ := by
  have hL : 0 ≤ JetLatticeGaussian.constant := by
    unfold JetLatticeGaussian.constant JetLatticeGaussian.exponential
    positivity
  unfold coefficient JetEscapedBarrier.coefficient JetGaussianEscape.constant
  have := JetThermalKernel.bound_pos
  positivity

theorem powerConstant_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (η α : ℝ) (m : ℕ) : 0 ≤ powerConstant s₀ η α K d₀ m := by
  have hr : 0 ≤ JetEscapedBarrier.rate η d₀ := by
    unfold JetEscapedBarrier.rate
    positivity
  unfold powerConstant
  apply mul_nonneg (mul_nonneg (coefficient_nonneg hK hd₀ α) (by positivity))
  exact tsum_nonneg (fun j => pow_nonneg (DatumBounds.scale_pos (η := η) hs₀ (j + 1)).le _)

end BoltzmannNonuniqueness.JetEscapedTotal

end

end

section

/-! # Escaped sums for arbitrary retained cold colors

The comparison hypothesis here is a pointwise bound for a color family. It is
kept explicit for application to the solutions of the finite labeled system.
All constants are independent of the retained subset.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetLatticeTail

namespace BoltzmannNonuniqueness.JetEscapedEnvelope

theorem constant_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (η α : ℝ) (m : ℕ) : 0 ≤ constant s₀ η α K d₀ m :=
  mul_nonneg (mul_nonneg (by norm_num) (JetEscapedTotal.powerConstant_nonneg hs₀ hK hd₀ η α m))
    tiltConstant_pos.le

end BoltzmannNonuniqueness.JetEscapedEnvelope

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveSourceFormula
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! # Positive gain comparison retaining the principal input action -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem chartGain_le_principal_add_remainders
    {c d e k : Measure Velocity} (hcd : c ≤ d+e+k)
    (q : ℝ) (v : Velocity) {f : Velocity → ℝ≥0∞} (hf : ∀ p, f p ≤ 1) :
    chartGain c (fun p => ENNReal.ofReal (H q p/H q v)*f p) v ≤
      chartGain d (fun p => ENNReal.ofReal (H q p/H q v)*f p) v+
      normalizedChartGain e q v+normalizedChartGain k q v := by
  apply (chartGain_mono_measure hcd _ v).trans
  rw [chartGain_add_measure,chartGain_add_measure]
  have h (μ : Measure Velocity) :
      chartGain μ (fun p => ENNReal.ofReal (H q p/H q v)*f p) v ≤
        normalizedChartGain μ q v := by
    apply chartGain_mono_right
    intro p
    simpa only [mul_one] using mul_le_mul' le_rfl (hf p)
  exact add_le_add (add_le_add le_rfl (h e)) (h k)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MixedPhysicalMeasures
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Polarized cutoff rates and their exact collision-map symmetries -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem mixedPreRate_measurable {c h : X × Velocity → ℝ}
    (hc : Measurable c) (hh : Measurable h) (b : ℝ) : Measurable (mixedPreRate b c h) := by
  have hk : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      CollisionCutoff.kernel b z.1.2.1 z.1.2.2 z.2) := by
    unfold CollisionCutoff.kernel
    apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
    · unfold collisionKernel normalComponent
      fun_prop
    · exact measurable_const
  exact (hk.mul (hc.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst))).mul
    (hh.comp (measurable_fst.fst.prodMk measurable_fst.snd.snd))

omit [MeasurableSpace X] in
theorem mixedPostRate_formula (b : ℝ) (c h : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    mixedPostRate b c h z = CollisionCutoff.kernel b z.1.2.1 z.1.2.2 z.2*
      c (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*h (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) := by
  change CollisionCutoff.kernel b (scatterLeft z.1.2.1 z.1.2.2 z.2)
    (scatterRight z.1.2.1 z.1.2.2 z.2) z.2* _ * _ = _
  rw [CollisionCutoff.kernel_scatter]
  rfl

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Pointwise domination supplies every mixed gain fibre integral -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem mixedPostRate_nonneg (b : ℝ) {c h : X × Velocity → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p)
    (z : (X × (Velocity × Velocity)) × Sphere) : 0 ≤ mixedPostRate b c h z :=
  mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) (hc _)) (hh _)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The actual cutoff mixed gain is dominated by the nonnegative full gain -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem mixedGainDensity_le_nonnegative (b : ℝ) {c h : X × Velocity → ℝ}
    (hcm : Measurable c) (hhm : Measurable h)
    (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p) (z : X × Velocity) :
    ENNReal.ofReal (mixedGainDensity b c h z) ≤
      nonnegativeGain (fun v => ENNReal.ofReal (c (z.1,v)))
        (fun v => ENNReal.ofReal (h (z.1,v))) z.2 := by
  let A : Velocity × Sphere → ℝ := fun q => mixedPostRate b c h (collisionGrouping.symm (z,q))
  let B : Velocity × Sphere → ℝ := fun q => mixedPostRate b h c (collisionGrouping.symm (z,q))
  have hA : ∀ p, 0 ≤ A p := fun p => mixedPostRate_nonneg b hc hh _
  have hB : ∀ p, 0 ≤ B p := fun p => mixedPostRate_nonneg b hh hc _
  have hAm : Measurable A := ((mixedPreRate_measurable hcm hhm b).comp
    scatterTripleEquiv.measurable).comp
      (collisionGrouping.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hAi : ENNReal.ofReal (∫ p, A p ∂gainPairMeasure) ≤ ∫⁻ p, ENNReal.ofReal (A p) ∂gainPairMeasure := by
    simpa only [Real.enorm_eq_ofReal (integral_nonneg hA),Real.enorm_eq_ofReal (hA _)] using
      (enorm_integral_le_lintegral_enorm A (μ := gainPairMeasure))
  have hBi : ENNReal.ofReal (∫ p, B p ∂gainPairMeasure) ≤ ∫⁻ p, ENNReal.ofReal (B p) ∂gainPairMeasure := by
    simpa only [Real.enorm_eq_ofReal (integral_nonneg hB),Real.enorm_eq_ofReal (hB _)] using
      (enorm_integral_le_lintegral_enorm B (μ := gainPairMeasure))
  change ENNReal.ofReal ((1/2:ℝ)*((∫ p, A p ∂gainPairMeasure)+(∫ p, B p ∂gainPairMeasure))) ≤ _
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2),
    ENNReal.ofReal_add (integral_nonneg hA) (integral_nonneg hB)]
  apply (mul_le_mul' le_rfl (add_le_add hAi hBi)).trans
  rw [← lintegral_add_left hAm.ennreal_ofReal,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    MixedRealGain.nonnegative_eq_lintegral (fun p => hc (z.1,p)) (fun p => hh (z.1,p))]
  apply lintegral_mono
  intro p
  dsimp only
  rw [← ENNReal.ofReal_add (hA p) (hB p),← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/2)]
  apply ENNReal.ofReal_le_ofReal
  have heA : A p = CollisionCutoff.kernel b z.2 p.1 p.2*
      c (z.1,scatterLeft z.2 p.1 p.2)*h (z.1,scatterRight z.2 p.1 p.2) :=
    mixedPostRate_formula b c h _
  have heB : B p = CollisionCutoff.kernel b z.2 p.1 p.2*
      h (z.1,scatterLeft z.2 p.1 p.2)*c (z.1,scatterRight z.2 p.1 p.2) :=
    mixedPostRate_formula b h c _
  rw [heA,heB]
  have hprod : 0 ≤ c (z.1,scatterLeft z.2 p.1 p.2)*h (z.1,scatterRight z.2 p.1 p.2)+
      h (z.1,scatterLeft z.2 p.1 p.2)*c (z.1,scatterRight z.2 p.1 p.2) :=
    add_nonneg (mul_nonneg (hc _) (hh _)) (mul_nonneg (hh _) (hc _))
  have hk := mul_le_mul_of_nonneg_right (CollisionCutoff.kernel_le b z.2 p.1 p.2) hprod
  unfold MixedRealGain.integrand
  nlinarith only [hk]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedPairCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Normalizing the actual cutoff mixed gain by the velocity weight -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem normalized_mixed_cutoff_le_chart (hcarleman : Published.GPV2009CarlemanInput)
    (b q : ℝ) {c f : X × Velocity → ℝ} (hcm : Measurable c) (hfm : Measurable f)
    (hc : ∀ z, 0 ≤ c z) (hf : ∀ z, 0 ≤ f z) (x : X) :
    ∀ᵐ v : Velocity, ENNReal.ofReal (mixedGainDensity b c (fun z => H q z.2*f z) (x,v)) ≤
      ENNReal.ofReal (H q v)*chartGain (volume.withDensity (fun p => ENNReal.ofReal (c (x,p))))
        (fun p => ENNReal.ofReal (H q p/H q v)*ENNReal.ofReal (f (x,p))) v := by
  have hwm : Measurable (fun z => H q z.2*f z) :=
    ((ChartKernel.measurable_H q).comp measurable_snd).mul hfm
  have hwn (z) : 0 ≤ H q z.2*f z := mul_nonneg (H_nonneg q z.2) (hf z)
  filter_upwards [hcarleman (fun p => ENNReal.ofReal (c (x,p)))
    (fun p => ENNReal.ofReal (H q p*f (x,p)))
    ((hcm.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal)
    ((hwm.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal)] with v hv
  have h := mixedGainDensity_le_nonnegative b hcm hwm hc hwn (x,v)
  rw [hv] at h
  have he : (fun p => ENNReal.ofReal (H q p*f (x,p))) =
      (fun p => ENNReal.ofReal (H q v)*(ENNReal.ofReal (H q p/H q v)*ENNReal.ofReal (f (x,p)))) := by
    funext p
    rw [ENNReal.ofReal_mul (H_nonneg q p),← mul_assoc,
      ← ENNReal.ofReal_mul (H_nonneg q v)]
    congr 2
    field_simp [(H_pos q v).ne']
  rw [he,chartGain_const_mul_right _ _ ENNReal.ofReal_ne_top] at h
  exact h

end BoltzmannNonuniqueness.CollisionCompactness

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

theorem frequencyConstant_nonneg {b : ℝ} (hb : 0 ≤ b) (q : ℝ) : 0 ≤ frequencyConstant q b := by
  unfold frequencyConstant
  have hi : 0 ≤ ∫ w, H q w := integral_nonneg (H_nonneg q)
  positivity

theorem integrable_dominated {q A : ℝ} (hq : q < 2) {f : Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w) (hfB : ∀ w, f w ≤ A * H q w) : Integrable f := by
  apply ((integrable_H hq).const_mul A).mono' hfm.aestronglyMeasurable
  filter_upwards [] with w
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hf w)] using hfB w

theorem frequency_nonneg {f : Velocity → ℝ} (hf : ∀ w, 0 ≤ f w) (b : ℝ) (v : Velocity) :
    0 ≤ CollisionCutoff.frequency b f v := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg (fun w => mul_nonneg (CollisionCutoff.rate_nonneg b v w) (hf w))

theorem frequency_bound {q A b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (hfB : ∀ w, f w ≤ A * H q w) (v : Velocity) :
    CollisionCutoff.frequency b f v ≤ A * frequencyConstant q b := by
  have hi := integrable_dominated hq hfm hf hfB
  calc
    _ ≤ 2 * Real.pi * b * ∫ w, |f w| :=
      (le_abs_self _).trans (CollisionCutoff.abs_frequency_le hb hi v)
    _ ≤ 2 * Real.pi * b * ∫ w, A * H q w := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono hi.abs ((integrable_H hq).const_mul A)
        (fun w => by simpa only [abs_of_nonneg (hf w)] using hfB w)
    _ = _ := by rw [integral_const_mul]; unfold frequencyConstant; ring

end BoltzmannNonuniqueness.CutoffLipschitz

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveIntegralFixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Order and dominated convergence for positive characteristic integrals -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P : Type*} [MeasurableSpace P]

theorem value_mono {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ k₀ : P → ℝ} (hfk : ∀ p, f₀ p ≤ k₀ p)
    {g h : Domain P → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S) (hgh : ∀ z, g z ≤ h z)
    (z : Domain P) : value T L flow f₀ g z ≤ value T L flow k₀ h z := by
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hfk _) (Real.exp_pos _).le
  · apply intervalIntegral.integral_mono_on (time_bounds hT z.1).1
      (damped_integrable hT hL hflow hgm hg z) (damped_integrable hT hL hflow hhm hh z)
    intro r _
    exact mul_le_mul_of_nonneg_left (hgh _) (Real.exp_pos _).le

theorem value_tendsto {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : P → ℝ) {g : ℕ → Domain P → ℝ} {h : Domain P → ℝ}
    (hgm : ∀ n, Measurable (g n)) (hg : ∀ n z, |g n z| ≤ S)
    (hlim : ∀ z, Tendsto (fun n => g n z) atTop (𝓝 (h z)))
    (z : Domain P) : Tendsto (fun n => value T L flow f₀ (g n) z) atTop
      (𝓝 (value T L flow f₀ h z)) := by
  apply tendsto_const_nhds.add
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => S)
  · exact .of_forall (fun n => (damped_integrable hT hL hflow (hgm n) (hg n) z).def'.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro n
    apply ae_of_all
    intro r hr
    rw [uIoc_of_le (time_bounds hT z.1).1] at hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-L * (time T z.1 - r)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hr.2])
    exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans (by simpa using hg n _)
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun r _ => tendsto_const_nhds.mul (hlim _))

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Finite sums of positive characteristic integrals -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P I : Type*} [MeasurableSpace P]

theorem value_finsetSum {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (s : Finset I) (f₀ : I → P → ℝ) (g : I → Domain P → ℝ)
    (hgm : ∀ i ∈ s, Measurable (g i)) (hg : ∀ i ∈ s, ∀ z, |g i z| ≤ S)
    (z : Domain P) :
    ∑ i ∈ s, value T L flow (f₀ i) (g i) z =
      value T L flow (fun p => ∑ i ∈ s, f₀ i p) (fun q => ∑ i ∈ s, g i q) z := by
  unfold value
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [← intervalIntegral.integral_finsetSum
    (fun i hi => damped_integrable hT hL hflow (hgm i hi) (hg i hi) z)]
  apply intervalIntegral.integral_congr
  intro r _
  exact (Finset.mul_sum s _ _).symm

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianLocalExistence
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive local cutoff iteration along the actual free transport -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.GaussianLocal

theorem measurable_state {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f) :
    Measurable (state f) := hf.comp (by fun_prop)

theorem measurable_flight : Measurable (fun z : ℝ × JetPrototype.Phase => JetBarrier.flight z.1 z.2) := by
  unfold JetBarrier.flight VelocityWeight.transverse VelocityWeight.axial
  fun_prop

end BoltzmannNonuniqueness.GaussianLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FlightMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Free-flight measure preservation and representative invariance -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.FlightMeasure

theorem spacetime_measurePreserving (s : ℝ) :
    MeasurePreserving (fun z : ℝ × JetPrototype.Phase => (z.1,JetBarrier.flight (z.1-s) z.2))
      ((volume : Measure ℝ).prod phaseVolume) ((volume : Measure ℝ).prod phaseVolume) := by
  exact (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (μc := phaseVolume) (μd := phaseVolume)
    (g := fun r p => JetBarrier.flight (r-s) p)
    (GaussianLocal.measurable_flight.comp
      ((measurable_fst.sub measurable_const).prodMk measurable_snd))
    (ae_of_all _ (fun r => (flight_measurePreserving (r-s)).map_eq))

theorem value_congr_at_time {f₀ k₀ : JetPrototype.Phase → ℝ}
    {g h : ℝ × JetPrototype.Phase → ℝ}
    (hinit : f₀ =ᵐ[phaseVolume] k₀) (hsource : g =ᵐ[(volume : Measure ℝ).prod phaseVolume] h)
    (T L t : ℝ) :
    (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)) =ᵐ[phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight k₀ h (t,p)) := by
  let τ := PositiveIntegral.time T t
  have hi := (flight_measurePreserving (-τ)).quasiMeasurePreserving.ae hinit
  have hs := (spacetime_measurePreserving τ).quasiMeasurePreserving.ae hsource
  have hsp := (Measure.measurePreserving_swap (μ := phaseVolume) (ν := volume)).quasiMeasurePreserving.ae hs
  have hr := ae_ae_of_ae_prod hsp
  filter_upwards [hi,hr] with p hip hrp
  unfold PositiveIntegral.value
  change Real.exp (-L*τ)*f₀ (JetBarrier.flight (-τ) p) + _ =
    Real.exp (-L*τ)*k₀ (JetBarrier.flight (-τ) p) + _
  rw [hip]
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hrp] with r hr _
  change g (r,JetBarrier.flight (r-PositiveIntegral.time T t) p) =
    h (r,JetBarrier.flight (r-PositiveIntegral.time T t) p) at hr
  rw [hr]

end BoltzmannNonuniqueness.FlightMeasure

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PhaseDecompositionNorm
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded representatives that realize the essential upper bound -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem ae_abs_le_size {f : JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hf : ∀ p, |f p| ≤ R) : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f p| ≤ size f := by
  have hm : MemLp f ∞ FlightMeasure.phaseVolume :=
    memLp_top_of_bound hfm.aestronglyMeasurable R (ae_of_all _ (fun p => by
      simpa only [Real.norm_eq_abs] using hf p))
  simpa only [Real.norm_eq_abs,← toReal_eLpNorm hm.1,size] using ae_le_lpNorm_exponent_top hm

end BoltzmannNonuniqueness.PhaseEssSup

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveIntegralPasting
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The positive integral only uses source values on its time interval -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_time_clamp {T : ℝ} (hT : 0 ≤ T) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (time T u.1,u.2) = value T L JetBarrier.flight f₀ g u := by
  simp only [value,PhaseEssSup.time_idempotent hT]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Order of the characteristic integral for almost-everywhere data -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.FlightMeasure

theorem value_mono_ae {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {f₀ k₀ : JetPrototype.Phase → ℝ} {g h : ℝ × JetPrototype.Phase → ℝ}
    (hinit : f₀ ≤ᵐ[phaseVolume] k₀) (hsource : g ≤ᵐ[(volume : Measure ℝ).prod phaseVolume] h)
    (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ u, |g u| ≤ S) (hh : ∀ u, |h u| ≤ S) (t : ℝ) :
    (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)) ≤ᵐ[phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight k₀ h (t,p)) := by
  let τ := PositiveIntegral.time T t
  have hi := (flight_measurePreserving (-τ)).quasiMeasurePreserving.ae hinit
  have hs := (spacetime_measurePreserving τ).quasiMeasurePreserving.ae hsource
  have hr := ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := phaseVolume) (ν := volume)).quasiMeasurePreserving.ae hs)
  filter_upwards [hi,hr] with p hip hrp
  apply add_le_add (mul_le_mul_of_nonneg_left hip (Real.exp_pos _).le)
  apply intervalIntegral.integral_mono_ae (PositiveIntegral.time_bounds hT t).1
    (PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight hgm hg (t,p))
    (PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight hhm hh (t,p))
  filter_upwards [hrp] with r hrr
  exact mul_le_mul_of_nonneg_left hrr (Real.exp_pos _).le

end BoltzmannNonuniqueness.FlightMeasure

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

theorem measurable_nonnegativeGain {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) : Measurable (nonnegativeGain f g) := by
  let : SFinite (gainPairMeasure) := Measure.prod.instSFinite
  have hl : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      scatterLeft p.1 p.2.1 p.2.2) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hr : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      scatterRight p.1 p.2.1 p.2.2) := by
    unfold scatterRight normalComponent
    fun_prop
  have hk : Measurable (fun p : Velocity × (Velocity × Sphere) =>
      ENNReal.ofReal (collisionKernel p.1 p.2.1 p.2.2) / 2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact (hk.mul (((hf.comp hl).mul (hg.comp hr)).add
    ((hg.comp hl).mul (hf.comp hr)))).lintegral_prod_right'

theorem measurableSet_good (q : ℝ) : MeasurableSet (good q) :=
  measurableSet_le (measurable_nonnegativeGain (measurable_H q).ennreal_ofReal
    (measurable_H q).ennreal_ofReal)
    ((measurable_H q).const_mul (HotApplication.realBound q)).ennreal_ofReal

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

theorem measurable_gain {f : X × Velocity → ℝ} (hf : Measurable f) (q b : ℝ) :
    Measurable (gain q b f) :=
  Measurable.ite ((measurableSet_good q).preimage measurable_snd)
    ((KineticCollisionNullSets.measurable_gain (measurable_density hf q) b).div
      ((measurable_H q).comp measurable_snd)) measurable_const

theorem measurable_frequency {f : X × Velocity → ℝ} (hf : Measurable f) (q b : ℝ) :
    Measurable (frequency q b f) :=
  KineticCollisionNullSets.measurable_frequency (measurable_density hf q) b

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Pointwise weighted gain bounds off the fixed exceptional set -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.HotRepresentative

theorem actual_gain_bound {q A : ℝ} {v : Velocity} (hv : v ∈ good q)
    {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ w, 0 ≤ f w)
    (hfB : ∀ w, f w ≤ A * H q w) (b : ℝ) :
    CollisionCutoff.gain b f v ≤ A^2 * HotApplication.realBound q * H q v := by
  have hi := GainOrder.integrable_const_mul A v (integrable_H_gain hv)
  calc
    _ ≤ BoltzmannNonuniqueness.gain (fun p => f p.2) 0 v :=
      CollisionCutoff.gain_le b hfm hf v 0 (GainOrder.integrable_of_le hfm hf hfB v hi)
    _ ≤ BoltzmannNonuniqueness.gain (fun p => A * H q p.2) 0 v :=
      GainOrder.gain_mono hfm hf hfB v 0 hi
    _ = A^2 * BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v :=
      GainOrder.gain_const_mul A (H q) v 0
    _ ≤ A^2 * (HotApplication.realBound q * H q v) :=
      mul_le_mul_of_nonneg_left (H_gain_bound hv) (sq_nonneg A)
    _ = _ := by ring

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

theorem gain_bound {q A : ℝ} (_hA : 0 ≤ A) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (b : ℝ) (p : X × Velocity) :
    gain q b f p ≤ A^2 * HotApplication.realBound q := by
  unfold gain
  split_ifs with hv
  · apply (div_le_iff₀ (H_pos q p.2)).mpr
    apply actual_gain_bound hv
      ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
      (fun w => mul_nonneg (H_nonneg _ _) (hf _).1)
    intro w
    exact (mul_le_mul_of_nonneg_left (hf _).2 (H_nonneg _ _)).trans_eq (mul_comm _ _)
  · exact mul_nonneg (sq_nonneg A) (HotApplication.realBound_pos q).le

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

theorem frequency_bound {q A b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A)
    (p : X × Velocity) : frequency q b f p ≤ A * CutoffLipschitz.frequencyConstant q b :=
  CutoffLipschitz.frequency_bound hq hb
    ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
    (fun w => (density_bounds hf (p.1,w)).1) (fun w => (density_bounds hf (p.1,w)).2) p.2

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Bounded positive source for the H-weighted local equation -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem measurable_source {f : X × Velocity → ℝ} (hf : Measurable f) (q b L : ℝ) :
    Measurable (source q b L f) :=
  (measurable_gain hf q b).add ((measurable_const.sub (measurable_frequency hf q b)).mul hf)

theorem source_bounds {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hL : R * CutoffLipschitz.frequencyConstant q b ≤ L)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R)
    (p : X × Velocity) :
    0 ≤ source q b L f p ∧ source q b L f p ≤ HotApplication.realBound q * R^2 + L*R := by
  have hν := frequency_nonneg (fun p => (hf p).1) q b p
  have hνB := frequency_bound hq hb hfm hf p
  have hLp : 0 ≤ L := (mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)).trans hL
  constructor
  · exact add_nonneg (gain_nonneg (fun p => (hf p).1) q b p)
      (mul_nonneg (sub_nonneg.mpr (hνB.trans hL)) (hf p).1)
  · have hg := gain_bound (q := q) hR hfm hf b p
    have hl : (L - frequency q b f p) * f p ≤ L*R :=
      (mul_le_mul_of_nonneg_right (sub_le_self _ hν) (hf p).1).trans
        (mul_le_mul_of_nonneg_left (hf p).2 hLp)
    unfold source
    nlinarith only [hg,hl]

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetSolutions
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
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

theorem gain_mono {q R : ℝ} {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p) (hfg : ∀ p, f p ≤ g p) (hg : ∀ p, g p ≤ R)
    (b : ℝ) (p : X × Velocity) : gain q b f p ≤ gain q b g p := by
  have hfn p : 0 ≤ f p ∧ f p ≤ R := ⟨hf p,(hfg p).trans (hg p)⟩
  have hgn p : 0 ≤ g p ∧ g p ≤ R := ⟨(hf p).trans (hfg p),hg p⟩
  unfold gain
  split_ifs with hp
  · apply div_le_div_of_nonneg_right _ (H_nonneg q p.2)
    apply integral_mono (integrable_cutoff hfm hfn b p hp) (integrable_cutoff hgm hgn b p hp)
    intro w
    unfold CollisionCutoff.integrand density
    have hL := mul_le_mul_of_nonneg_left (hfg (p.1,scatterLeft p.2 w.1 w.2)) (H_nonneg q (scatterLeft p.2 w.1 w.2))
    have hR := mul_le_mul_of_nonneg_left (hfg (p.1,scatterRight p.2 w.1 w.2)) (H_nonneg q (scatterRight p.2 w.1 w.2))
    exact mul_le_mul (mul_le_mul_of_nonneg_left hL (CollisionCutoff.kernel_nonneg _ _ _ _)) hR
      (mul_nonneg (H_nonneg _ _) (hf _))
      (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _) (mul_nonneg (H_nonneg _ _) (hgn _).1))
  · exact le_rfl

theorem gain_tendsto {q R : ℝ} (_hR : 0 ≤ R) {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p ∧ f n p ≤ R)
    (hlim : ∀ p, Tendsto (fun n => f n p) atTop (𝓝 (g p))) (b : ℝ) (p : X × Velocity) :
    Tendsto (fun n => gain q b (f n) p) atTop (𝓝 (gain q b g p)) := by
  unfold gain
  split_ifs with hp
  · apply Tendsto.div_const
    apply tendsto_integral_of_dominated_convergence
      (fun w => R^2 * GainOrder.integrand (H q) p.2 w)
    · intro n
      exact (integrable_cutoff (hfm n) (hf n) b p hp).aestronglyMeasurable
    · exact (integrable_H_gain hp).const_mul _
    · intro n
      apply ae_of_all
      intro w
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · apply (CollisionCutoff.integrand_le b (fun v => (density_bounds (q := q) (hf n) (p.1,v)).1) p.2 w).trans
        have h := GainOrder.integrand_mono (fun v => (density_bounds (q := q) (hf n) (p.1,v)).1)
          (fun v => (density_bounds (q := q) (hf n) (p.1,v)).2) p.2 w
        unfold GainOrder.integrand density at h ⊢
        nlinarith only [h]
      · exact mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg _ _ _ _)
          (density_bounds (q := q) (hf n) _).1) (density_bounds (q := q) (hf n) _).1
    · apply ae_of_all
      intro w
      exact ((tendsto_const_nhds.mul (tendsto_const_nhds.mul (hlim _))).mul
        (tendsto_const_nhds.mul (hlim _)))
  · exact tendsto_const_nhds

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Positive local iteration in the manuscript's singular weighted norm -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem measurable_forcing {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f) (q b L : ℝ) :
    Measurable (forcing q b L f) :=
  (HotRepresentative.measurable_source (GaussianLocal.measurable_state hf) q b L).comp (by fun_prop)

end BoltzmannNonuniqueness.WeightedLocal

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

section

/-! # Common-loss cold source in the singular weighted space -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem measurable_coldSource {F c : X × Velocity → ℝ} (hFm : Measurable F) (hcm : Measurable c)
    (q b L : ℝ) : Measurable (coldSource q b L F c) :=
  (measurable_gain hcm q b).add ((measurable_const.sub (measurable_frequency hFm q b)).mul hcm)

theorem coldSource_bounds {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hL : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F c : X × Velocity → ℝ} (hFm : Measurable F) (hcm : Measurable c)
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hc : ∀ p, 0 ≤ c p ∧ c p ≤ R) (p : X × Velocity) :
    0 ≤ coldSource q b L F c p ∧ coldSource q b L F c p ≤ HotApplication.realBound q*R^2+L*R := by
  have hν := frequency_nonneg (fun p => (hF p).1) q b p
  have hνB := frequency_bound hq hb hFm hF p
  have hLp : 0 ≤ L := (mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)).trans hL
  constructor
  · exact add_nonneg (gain_nonneg (fun p => (hc p).1) q b p)
      (mul_nonneg (sub_nonneg.mpr (hνB.trans hL)) (hc p).1)
  · have hg := gain_bound (q := q) hR hcm hc b p
    have hl : (L-frequency q b F p)*c p ≤ L*R :=
      (mul_le_mul_of_nonneg_right (sub_le_self _ hν) (hc p).1).trans
        (mul_le_mul_of_nonneg_left (hc p).2 hLp)
    unfold coldSource
    nlinarith only [hg,hl]

theorem coldSource_mono {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F c d : X × Velocity → ℝ} (hFm : Measurable F) (hcm : Measurable c) (hdm : Measurable d)
    (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R) (hcn : ∀ p, 0 ≤ c p)
    (hcd : ∀ p, c p ≤ d p) (hdR : ∀ p, d p ≤ R) (p : X × Velocity) :
    coldSource q b L F c p ≤ coldSource q b L F d p := by
  have hν : frequency q b F p ≤ L := (frequency_bound hq hb hFm hF p).trans hL
  exact add_le_add (gain_mono hcm hdm hcn hcd hdR b p)
    (mul_le_mul_of_nonneg_left (hcd p) (sub_nonneg.mpr hν))

theorem coldSource_tendsto {q R : ℝ} (hR : 0 ≤ R) (b L : ℝ) (F : X × Velocity → ℝ)
    {c : ℕ → X × Velocity → ℝ} {d : X × Velocity → ℝ}
    (hcm : ∀ n, Measurable (c n)) (hc : ∀ n p, 0 ≤ c n p ∧ c n p ≤ R)
    (hlim : ∀ p, Tendsto (fun n => c n p) atTop (𝓝 (d p))) (p : X × Velocity) :
    Tendsto (fun n => coldSource q b L F (c n) p) atTop (𝓝 (coldSource q b L F d p)) :=
  (gain_tendsto hR hcm hc hlim b p).add (tendsto_const_nhds.mul (hlim p))

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Positive cold iteration beneath the H-weighted total solution -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem measurable_coldForcing {F c : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c) (q b L : ℝ) : Measurable (coldForcing q b L F c) :=
  (HotRepresentative.measurable_coldSource (GaussianLocal.measurable_state hFm)
    (GaussianLocal.measurable_state hcm) q b L).comp (by fun_prop)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Weighted collision representatives respect equality almost everywhere -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem density_congr (μ : Measure X) {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q : ℝ) : density q f =ᵐ[μ.prod volume] density q g := by
  filter_upwards [hfg] with p hp
  unfold density
  rw [hp]

theorem gain_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q b : ℝ) : gain q b f =ᵐ[μ.prod volume] gain q b g := by
  have hh := KineticCollisionNullSets.gain_congr μ (density_congr μ hfg q) b
  filter_upwards [hh] with p hp
  unfold gain
  split_ifs <;> simp only [hp]

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Spatial covariance of the constructed weighted cold solutions -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.WeightedTranslation

theorem measurable_shift (y : Space) : Measurable (shift y) := by
  unfold shift
  fun_prop

end BoltzmannNonuniqueness.WeightedTranslation

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

/-! # Domination of finite sums of cold sources by the total source -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem finite_sum_coldSource_le {q b L R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : R*CutoffLipschitz.frequencyConstant q b ≤ L) (s : Finset I)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i ∈ s, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i ∈ s, ∀ p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    ∑ i ∈ s, coldSource q b L F (c i) p ≤ source q b L F p := by
  have hν : frequency q b F p ≤ L := (frequency_bound hq hb hFm hF p).trans hL
  unfold coldSource source
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  exact add_le_add (finite_sum_gain_le s hcm hFm hc hF hSum b p)
    (mul_le_mul_of_nonneg_left (hSum p) (sub_nonneg.mpr hν))

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotCollisionDecomposition
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Replacing only the hot remainder by an essential-norm representative -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.HotCanonical

theorem state_congr {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[(volume : Measure ℝ).prod FlightMeasure.phaseVolume] G) :
    GaussianLocal.state F =ᵐ[((volume : Measure ℝ).prod JetPrototype.spaceVolume).prod volume]
      GaussianLocal.state G :=
  (measurePreserving_prodAssoc (volume : Measure ℝ) JetPrototype.spaceVolume
    (volume : Measure Velocity)).quasiMeasurePreserving.ae_eq_comp hFG

end BoltzmannNonuniqueness.HotCanonical

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedNetLoss
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Mild equations stable under changing spatial representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem slice_congr_spacetime {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hFG : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => G (t,p))) :
    F =ᵐ[spacetimeVolume] G :=
  (ae_prod_iff_ae_ae (measurableSet_eq_fun hFm hGm)).mpr (ae_of_all _ hFG)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Cold-source equality and finite-family domination almost everywhere -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

theorem coldForcing_congr_cold {c d : ℝ × JetPrototype.Phase → ℝ}
    (hcd : c =ᵐ[spacetimeVolume] d) (q b L : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    coldForcing q b L F c =ᵐ[spacetimeVolume] coldForcing q b L F d := by
  have hs := HotCanonical.state_congr hcd
  have hg := HotRepresentative.gain_congr ((volume : Measure ℝ).prod JetPrototype.spaceVolume) hs q b
  have he : HotRepresentative.coldSource q b L (GaussianLocal.state F) (GaussianLocal.state c) =ᵐ[
      ((volume : Measure ℝ).prod JetPrototype.spaceVolume).prod volume]
      HotRepresentative.coldSource q b L (GaussianLocal.state F) (GaussianLocal.state d) := by
    filter_upwards [hs,hg] with u hu hgu
    unfold HotRepresentative.coldSource
    rw [hu,hgu]
  exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume : Measure ℝ) JetPrototype.spaceVolume
      (volume : Measure Velocity))).quasiMeasurePreserving.ae_eq_comp he

theorem finite_coldForcing_le_ae {I : Type*} [Countable I] {q b L R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (s : Finset I)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i ∈ s, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc : ∀ i ∈ s, ∀ u, 0 ≤ c i u ∧ c i u ≤ R)
    (hSum : ∀ᵐ u ∂spacetimeVolume, ∑ i ∈ s, c i u ≤ F u) :
    ∀ᵐ u ∂spacetimeVolume, ∑ i ∈ s, coldForcing q b L F (c i) u ≤ forcing q b L F u := by
  classical
  let d (i : I) (u : ℝ × JetPrototype.Phase) := if (∑ j ∈ s, c j u) ≤ F u then c i u else 0
  have hm : MeasurableSet {u : ℝ × JetPrototype.Phase | (∑ j ∈ s, c j u) ≤ F u} :=
    measurableSet_le (Finset.measurable_sum s hcm) hFm
  have hdm (i) (hi : i ∈ s) : Measurable (d i) := (hcm i hi).ite hm measurable_const
  have hdb (i) (hi : i ∈ s) (u) : 0 ≤ d i u ∧ d i u ≤ R := by
    dsimp [d]
    split_ifs
    · exact hc i hi u
    · exact ⟨le_rfl,hR⟩
  have hds (u) : (∑ i ∈ s, d i u) ≤ F u := by
    by_cases hu : (∑ i ∈ s, c i u) ≤ F u
    · simpa only [d,ite_eq_left hu] using hu
    · simpa only [d,ite_eq_right hu,Finset.sum_const_zero] using (hF u).1
  have hbound (u) : (∑ i ∈ s, coldForcing q b L F (d i) u) ≤ forcing q b L F u :=
    HotRepresentative.finite_sum_coldSource_le hq hb hloss s
      (fun i hi => GaussianLocal.measurable_state (hdm i hi)) (GaussianLocal.measurable_state hFm)
      (fun i hi p => hdb i hi (p.1.1,(p.1.2,p.2)))
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hds (p.1.1,(p.1.2,p.2))) _
  have he (i : I) : d i =ᵐ[spacetimeVolume] c i := hSum.mono (fun u hu => ite_eq_left hu)
  have hce : ∀ᵐ u ∂spacetimeVolume, ∀ i, coldForcing q b L F (d i) u = coldForcing q b L F (c i) u :=
    ae_all_iff.mpr (fun i => coldForcing_congr_cold (he i) q b L F)
  filter_upwards [hce] with u hu
  have h := hbound u
  simpa only [hu] using h

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClippedColdFiniteLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded positive cold iteration without a pointwise total fixed point -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedCold_properties {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ R)
    (n : ℕ) : Measurable (clippedColdPicard q b L T F c₀ n) ∧
      ∀ u, 0 ≤ clippedColdPicard q b L T F c₀ n u ∧ clippedColdPicard q b L T F c₀ n u ≤ F u := by
  let S := HotApplication.realBound q*R^2+L*R
  have hS : 0 ≤ S := by
    have h := (HotApplication.realBound_pos q).le
    dsimp [S]
    positivity
  induction n with
  | zero => exact ⟨measurable_const,fun u => ⟨le_rfl,(hF u).1⟩⟩
  | succ n ih =>
    have hcb (u) : 0 ≤ clippedColdPicard q b L T F c₀ n u ∧
        clippedColdPicard q b L T F c₀ n u ≤ R := ⟨(ih.2 u).1,(ih.2 u).2.trans (hF u).2⟩
    have hgm := measurable_coldForcing hFm ih.1 q b L
    have hgb (u) : 0 ≤ coldForcing q b L F (clippedColdPicard q b L T F c₀ n) u ∧
        coldForcing q b L F (clippedColdPicard q b L T F c₀ n) u ≤ S :=
      HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
        (GaussianLocal.measurable_state ih.1)
        (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hcb (p.1.1,(p.1.2,p.2))) _
    refine ⟨hFm.min (PositiveIntegral.measurable_value hT GaussianLocal.measurable_flight hc₀m hgm),?_⟩
    intro u
    exact ⟨le_min (hF u).1
      (PositiveIntegral.value_bounds hT hL hR hS JetBarrier.flight hc₀ hgb u).1,min_le_left _ _⟩

theorem clippedCold_monotone {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ R)
    (u : ℝ × JetPrototype.Phase) : Monotone (fun n => clippedColdPicard q b L T F c₀ n u) := by
  have hp := clippedCold_properties hq hb hL hT hR hloss hFm hc₀m hF hc₀
  have hcb (n) (u) : 0 ≤ clippedColdPicard q b L T F c₀ n u ∧
      clippedColdPicard q b L T F c₀ n u ≤ R :=
    ⟨((hp n).2 u).1,((hp n).2 u).2.trans (hF u).2⟩
  have hgb (n) (u) : 0 ≤ coldForcing q b L F (clippedColdPicard q b L T F c₀ n) u ∧
      coldForcing q b L F (clippedColdPicard q b L T F c₀ n) u ≤ HotApplication.realBound q*R^2+L*R :=
    HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (GaussianLocal.measurable_state (hp n).1)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hcb n (p.1.1,(p.1.2,p.2))) _
  have hstep : ∀ n u, clippedColdPicard q b L T F c₀ n u ≤ clippedColdPicard q b L T F c₀ (n+1) u := by
    intro n
    induction n with
    | zero => intro u; exact ((hp 1).2 u).1
    | succ n ih =>
      intro u
      apply min_le_min_left
      apply PositiveIntegral.value_mono hT hL GaussianLocal.measurable_flight (fun _ => le_rfl)
        (measurable_coldForcing hFm (hp n).1 q b L)
        (measurable_coldForcing hFm (hp (n+1)).1 q b L)
        (fun z => by rw [abs_of_nonneg (hgb n z).1]; exact (hgb n z).2)
        (fun z => by rw [abs_of_nonneg (hgb (n+1) z).1]; exact (hgb (n+1) z).2)
      intro p
      exact HotRepresentative.coldSource_mono hq hb hloss (GaussianLocal.measurable_state hFm)
        (GaussianLocal.measurable_state (hp n).1) (GaussianLocal.measurable_state (hp (n+1)).1)
        (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => (hcb n (p.1.1,(p.1.2,p.2))).1)
        (fun p => ih (p.1.1,(p.1.2,p.2))) (fun p => (hcb (n+1) (p.1.1,(p.1.2,p.2))).2) _
  exact monotone_nat_of_le_succ (fun n => hstep n u)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The bounded monotone cold limit for a measurable total state -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedCold_solution {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ R) :
    Measurable (clippedColdLimit q b L T F c₀) ∧
      (∀ u, 0 ≤ clippedColdLimit q b L T F c₀ u ∧ clippedColdLimit q b L T F c₀ u ≤ F u) ∧
      (∀ u, clippedColdLimit q b L T F c₀ u = min (F u)
        (PositiveIntegral.value T L JetBarrier.flight c₀
          (coldForcing q b L F (clippedColdLimit q b L T F c₀)) u)) ∧
      ∀ u, Tendsto (fun n => clippedColdPicard q b L T F c₀ n u) atTop
        (𝓝 (clippedColdLimit q b L T F c₀ u)) := by
  let c := clippedColdLimit q b L T F c₀
  let u := clippedColdPicard q b L T F c₀
  have hp := clippedCold_properties hq hb hL hT hR hloss hFm hc₀m hF hc₀
  have hcb (n) (z) : 0 ≤ u n z ∧ u n z ≤ R :=
    ⟨((hp n).2 z).1,((hp n).2 z).2.trans (hF z).2⟩
  have hgb (n) (z) : 0 ≤ coldForcing q b L F (u n) z ∧
      coldForcing q b L F (u n) z ≤ HotApplication.realBound q*R^2+L*R :=
    HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (GaussianLocal.measurable_state (hp n).1)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hcb n (p.1.1,(p.1.2,p.2))) _
  have hmono (z) : Monotone (fun n => u n z) :=
    clippedCold_monotone hq hb hL hT hR hloss hFm hc₀m hF hc₀ z
  have hbdd (z) : BddAbove (Set.range (fun n => u n z)) :=
    ⟨F z,by rintro _ ⟨n,rfl⟩; exact ((hp n).2 z).2⟩
  have hlim (z) : Tendsto (fun n => u n z) atTop (𝓝 (c z)) :=
    tendsto_atTop_ciSup (hmono z) (hbdd z)
  have hcm : Measurable c := measurable_of_tendsto_metrizable (fun n => (hp n).1)
    (tendsto_pi_nhds.mpr hlim)
  have hbound (z) : 0 ≤ c z ∧ c z ≤ F z :=
    ⟨(le_ciSup (hbdd z) 0 : u 0 z ≤ c z),ciSup_le (fun n => ((hp n).2 z).2)⟩
  refine ⟨hcm,hbound,?_,hlim⟩
  intro z
  have hsource (p) : Tendsto (fun n => coldForcing q b L F (u n) p) atTop
      (𝓝 (coldForcing q b L F c p)) :=
    HotRepresentative.coldSource_tendsto hR b L (GaussianLocal.state F)
      (fun n => GaussianLocal.measurable_state (hp n).1)
      (fun n p => hcb n (p.1.1,(p.1.2,p.2)))
      (fun p => hlim (p.1.1,(p.1.2,p.2))) _
  have hv := PositiveIntegral.value_tendsto hT hL GaussianLocal.measurable_flight c₀
    (fun n => measurable_coldForcing hFm (hp n).1 q b L)
    (fun n p => by rw [abs_of_nonneg (hgb n p).1]; exact (hgb n p).2) hsource z
  have hnext : Tendsto (fun n => u (n+1) z) atTop (𝓝 (c z)) :=
    (hlim z).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hnext (tendsto_const_nhds.min hv)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Finite sums of clipped cold iterates stay below a mild total solution -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedCold_finite_picard {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (s : Finset I)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hSum₀ : ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) :
    ∀ n t, ∀ᵐ p ∂FlightMeasure.phaseVolume, ∑ i ∈ s, clippedColdPicard q b L T F (c₀ i) n (t,p) ≤ F (t,p) := by
  let S := HotApplication.realBound q*R^2+L*R
  have hS : 0 ≤ S := by
    have hg := (HotApplication.realBound_pos q).le
    dsimp [S]
    positivity
  have hp (i) := clippedCold_properties hq hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i)
  have hcb (i n u) : 0 ≤ clippedColdPicard q b L T F (c₀ i) n u ∧
      clippedColdPicard q b L T F (c₀ i) n u ≤ R :=
    ⟨((hp i n).2 u).1,((hp i n).2 u).2.trans (hF u).2⟩
  have hgb (i n u) : 0 ≤ coldForcing q b L F (clippedColdPicard q b L T F (c₀ i) n) u ∧
      coldForcing q b L F (clippedColdPicard q b L T F (c₀ i) n) u ≤ S :=
    HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (GaussianLocal.measurable_state (hp i n).1)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hcb i n (p.1.1,(p.1.2,p.2))) _
  have hfb (u) : 0 ≤ forcing q b L F u ∧ forcing q b L F u ≤ S :=
    HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) _
  intro n
  induction n with
  | zero =>
    intro t
    exact ae_of_all _ (fun p => by simpa only [clippedColdPicard,Finset.sum_const_zero] using (hF (t,p)).1)
  | succ n ih =>
    let g (i : I) := coldForcing q b L F (clippedColdPicard q b L T F (c₀ i) n)
    have hgm (i) : Measurable (g i) := measurable_coldForcing hFm (hp i n).1 q b L
    have hsum : ∀ᵐ u ∂spacetimeVolume, ∑ i ∈ s, clippedColdPicard q b L T F (c₀ i) n u ≤ F u :=
      (ae_prod_iff_ae_ae (measurableSet_le (Finset.measurable_sum s (fun i _ => (hp i n).1)) hFm)).mpr
        (ae_of_all _ ih)
    have hsource := finite_coldForcing_le_ae hq hb hR hloss s hFm (fun i _ => (hp i n).1)
      hF (fun i _ => hcb i n) hsum
    have hsumabs (u) : |∑ i ∈ s, g i u| ≤ (s.card+1 : ℕ)*S := by
      rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => (hgb i n u).1))]
      calc
        _ ≤ ∑ _i ∈ s, S := Finset.sum_le_sum (fun i _ => (hgb i n u).2)
        _ = (s.card : ℝ)*S := by simp
        _ ≤ (s.card+1 : ℕ)*S := mul_le_mul_of_nonneg_right (by norm_num) hS
    have hfabs (u) : |forcing q b L F u| ≤ (s.card+1 : ℕ)*S := by
      rw [abs_of_nonneg (hfb u).1]
      have hcard : (1:ℝ) ≤ (s.card+1 : ℕ) := by norm_num
      have hmul := mul_le_mul_of_nonneg_right hcard hS
      exact (hfb u).2.trans (by simpa only [one_mul] using hmul)
    intro t
    have hv := FlightMeasure.value_mono_ae hT hL (ae_of_all _ hSum₀) hsource
      (Finset.measurable_sum s (fun i _ => hgm i)) (measurable_forcing hFm q b L) hsumabs hfabs t
    filter_upwards [hv,hFeq t] with p hvp hfp
    have hsumvalue := PositiveIntegral.value_finsetSum hT hL GaussianLocal.measurable_flight s c₀ g
      (fun i _ => hgm i) (fun i _ u => by rw [abs_of_nonneg (hgb i n u).1]; exact (hgb i n u).2) (t,p)
    calc
      _ ≤ ∑ i ∈ s, PositiveIntegral.value T L JetBarrier.flight (c₀ i) (g i) (t,p) :=
        Finset.sum_le_sum (fun i _ => min_le_right _ _)
      _ = _ := hsumvalue
      _ ≤ _ := hvp
      _ = F (t,p) := hfp.symm

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The clipping is inactive almost everywhere for a mild total solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedCold_mildAE {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : Measurable c₀)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ p, 0 ≤ c₀ p ∧ c₀ p ≤ R)
    (hcF₀ : ∀ p, c₀ p ≤ F₀ p) (hFeq : MildAE q b L T F₀ F) :
    ColdMildAE q b L T F c₀ (clippedColdLimit q b L T F c₀) := by
  let c := clippedColdLimit q b L T F c₀
  have hc := clippedCold_solution hq hb hL hT hR hloss hFm hc₀m hF hc₀
  have hcb (u) : 0 ≤ c u ∧ c u ≤ R := ⟨(hc.2.1 u).1,(hc.2.1 u).2.trans (hF u).2⟩
  have hgb (u : ℝ × JetPrototype.Phase) : 0 ≤ coldForcing q b L F c u ∧
      coldForcing q b L F c u ≤ HotApplication.realBound q*R^2+L*R :=
    HotRepresentative.coldSource_bounds hq hb hR hloss
    (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state hc.1)
    (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hcb (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
  have hfb (u : ℝ × JetPrototype.Phase) : 0 ≤ forcing q b L F u ∧
      forcing q b L F u ≤ HotApplication.realBound q*R^2+L*R :=
    HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
    (fun p => hF (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)
  have horder (u) : coldForcing q b L F c u ≤ forcing q b L F u :=
    HotRepresentative.coldSource_mono hq hb hloss
      (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state hc.1)
      (GaussianLocal.measurable_state hFm) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => (hcb (p.1.1,(p.1.2,p.2))).1)
      (fun p => (hc.2.1 (p.1.1,(p.1.2,p.2))).2)
      (fun p => (hF (p.1.1,(p.1.2,p.2))).2) _
  have hvalue (u) := PositiveIntegral.value_mono hT hL GaussianLocal.measurable_flight hcF₀
    (measurable_coldForcing hFm hc.1 q b L) (measurable_forcing hFm q b L)
    (fun u => by rw [abs_of_nonneg (hgb u).1]; exact (hgb u).2)
    (fun u => by rw [abs_of_nonneg (hfb u).1]; exact (hfb u).2) horder u
  intro t ht
  filter_upwards [hFeq t ht] with p hp
  have hv := hvalue (t,p)
  change PositiveIntegral.value T L JetBarrier.flight c₀ (coldForcing q b L F c) (t,p) ≤ _ at hv
  rw [← hp] at hv
  rw [hc.2.2.1 (t,p),min_eq_right hv]

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Finite-family domination passes to the cold limits -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedCold_finite_limit {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (s : Finset I)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hSum₀ : ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) :
    ∀ t, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      ∑ i ∈ s, clippedColdLimit q b L T F (c₀ i) (t,p) ≤ F (t,p) := by
  have hn := clippedCold_finite_picard hq hb hL hT hR hloss s hFm hc₀m hF hc₀ hSum₀ hFeq
  intro t
  have hall : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ n,
      ∑ i ∈ s, clippedColdPicard q b L T F (c₀ i) n (t,p) ≤ F (t,p) :=
    ae_all_iff.mpr (fun n => hn n t)
  filter_upwards [hall] with p hp
  have hlim (i) := (clippedCold_solution hq hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i)).2.2.2 (t,p)
  exact le_of_tendsto (tendsto_finsetSum s (fun i _ => hlim i)) (Filter.Eventually.of_forall hp)

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ColdMildRepresentative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Pointwise dominated representatives of an almost-everywhere cold family -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

theorem measurable_normalizedFamily {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hcm : ∀ i, Measurable (c i)) (i : I) :
    Measurable (normalizedFamily F c i) := by
  classical
  have he : {u : ℝ × JetPrototype.Phase | ∀ s : Finset I, (∑ j ∈ s, c j u) ≤ F u} =
      ⋂ s : Finset I, {u | (∑ j ∈ s, c j u) ≤ F u} := by ext u; simp
  have hm : MeasurableSet {u : ℝ × JetPrototype.Phase | ∀ s : Finset I, (∑ j ∈ s, c j u) ≤ F u} := by
    rw [he]
    exact MeasurableSet.iInter (fun s => measurableSet_le
      (Finset.measurable_sum s (fun j _ => hcm j)) hFm)
  exact (hcm i).ite hm measurable_const

omit [Countable I] in
theorem normalizedFamily_bounds {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ} (hcn : ∀ i u, 0 ≤ c i u) (i : I) (u) :
    0 ≤ normalizedFamily F c i u ∧ normalizedFamily F c i u ≤ c i u := by
  classical
  unfold normalizedFamily
  split_ifs
  · exact ⟨hcn i u,le_rfl⟩
  · exact ⟨le_rfl,hcn i u⟩

omit [Countable I] in
theorem normalizedFamily_sum_le {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, 0 ≤ F u) (c : I → ℝ × JetPrototype.Phase → ℝ) (s : Finset I) (u) :
    (∑ i ∈ s, normalizedFamily F c i u) ≤ F u := by
  classical
  by_cases hu : ∀ r : Finset I, (∑ j ∈ r, c j u) ≤ F u
  · simpa only [normalizedFamily,ite_eq_left hu] using hu s
  · simpa only [normalizedFamily,ite_eq_right hu,Finset.sum_const_zero] using hF u

theorem normalizedFamily_ae_at_time {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hfinite : ∀ s : Finset I, ∀ t, ∀ᵐ p ∂FlightMeasure.phaseVolume, (∑ i ∈ s, c i (t,p)) ≤ F (t,p))
    (i : I) (t : ℝ) : (fun p => normalizedFamily F c i (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => c i (t,p)) := by
  classical
  have hg : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ s : Finset I, (∑ j ∈ s, c j (t,p)) ≤ F (t,p) :=
    ae_all_iff.mpr (fun s => hfinite s t)
  filter_upwards [hg] with p hp
  exact ite_eq_left hp

omit [Countable I] in
theorem normalizedFamily_summable {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ} (hF : ∀ u, 0 ≤ F u) (hcn : ∀ i u, 0 ≤ c i u) (u) :
    Summable (fun i => normalizedFamily F c i u) ∧ (∑' i, normalizedFamily F c i u) ≤ F u := by
  have hn (i) : 0 ≤ normalizedFamily F c i u := (normalizedFamily_bounds hcn i u).1
  have hs (s : Finset I) := normalizedFamily_sum_le hF c s u
  exact ⟨summable_of_sum_le hn hs,Real.tsum_le_of_sum_le hn hs⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Cold mild equations are independent of spatial representatives -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem ColdMildAE.representative {q b L T : ℝ} {c₀ : JetPrototype.Phase → ℝ}
    {F c d : ℝ × JetPrototype.Phase → ℝ} (hc : ColdMildAE q b L T F c₀ c)
    (hcm : Measurable c) (hdm : Measurable d)
    (hcd : ∀ t, (fun p => c (t,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => d (t,p))) :
    ColdMildAE q b L T F c₀ d := by
  have hsource := coldForcing_congr_cold (slice_congr_spacetime hcm hdm hcd) q b L F
  intro t ht
  exact (hcd t).symm.trans ((hc t ht).trans
    (FlightMeasure.value_congr_at_time (ae_of_all _ (fun _ => rfl)) hsource T L t))

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RebuiltHotInitial
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A pointwise summable cold family over an almost-everywhere mild total state -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

theorem rebuiltColdFamily_properties {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) :
    (∀ i, Measurable (rebuiltColdFamily q b L T F c₀ i)) ∧
      (∀ i u, 0 ≤ rebuiltColdFamily q b L T F c₀ i u ∧
        rebuiltColdFamily q b L T F c₀ i u ≤ clippedColdLimit q b L T F (c₀ i) u) ∧
      (∀ s : Finset I, ∀ u, ∑ i ∈ s, rebuiltColdFamily q b L T F c₀ i u ≤ F u) ∧
      (∀ u, Summable (fun i => rebuiltColdFamily q b L T F c₀ i u) ∧
        (∑' i, rebuiltColdFamily q b L T F c₀ i u) ≤ F u) ∧
      ∀ i, ColdMildAE q b L T F (c₀ i) (rebuiltColdFamily q b L T F c₀ i) := by
  classical
  let c (i : I) := clippedColdLimit q b L T F (c₀ i)
  have hc (i) := clippedCold_solution hq hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i)
  have hcm (i) : Measurable (c i) := (hc i).1
  have hcn (i) (u) : 0 ≤ c i u := ((hc i).2.1 u).1
  have hfin (s : Finset I) := clippedCold_finite_limit hq hb hL hT hR hloss s hFm hc₀m hF hc₀ (hSum₀ s) hFeq
  have hd (i) : Measurable (rebuiltColdFamily q b L T F c₀ i) := measurable_normalizedFamily hFm hcm i
  refine ⟨hd,normalizedFamily_bounds hcn,normalizedFamily_sum_le (fun u => (hF u).1) c,
    normalizedFamily_summable (fun u => (hF u).1) hcn,?_⟩
  intro i
  have hi : ∀ p, c₀ i p ≤ F₀ p := by
    intro p
    simpa only [Finset.sum_singleton] using hSum₀ {i} p
  have hm := clippedCold_mildAE hq hb hL hT hR hloss hFm (hc₀m i) hF (hc₀ i) hi
    (fun t _ => hFeq t)
  exact hm.representative (hcm i) (hd i)
    (fun t => (normalizedFamily_ae_at_time hfin i t).symm)

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClippedColdTime
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Time clamping of the reconstructed cold family -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem mild_all_of_time_clamp {T : ℝ} (hT : 0 ≤ T) (L : ℝ)
    {f : ℝ × JetPrototype.Phase → ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {g : ℝ × JetPrototype.Phase → ℝ}
    (hf : ∀ u, f (PositiveIntegral.time T u.1,u.2) = f u)
    (he : ∀ t ∈ Set.Icc 0 T, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :
    ∀ t, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)) := by
  intro t
  filter_upwards [he (PositiveIntegral.time T t) (PositiveIntegral.time_bounds hT t)] with p hp
  rw [hf (t,p)] at hp
  exact hp.trans (PositiveIntegral.value_time_clamp hT L f₀ g (t,p))

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetStability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A common positive local time for bounded weighted data -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocalControl

theorem bounds {q b A : ℝ} (hb : 0 ≤ b) (hA : 0 < A) :
    0 ≤ damping q b A ∧ 0 ≤ sourceBound q b A ∧ 0 ≤ lipschitz q b A := by
  have hC := CutoffLipschitz.frequencyConstant_nonneg hb q
  have hG := (HotApplication.realBound_pos q).le
  have hL : 0 ≤ damping q b A := by unfold damping; positivity
  exact ⟨hL, by unfold sourceBound; positivity, by unfold lipschitz; positivity⟩

end BoltzmannNonuniqueness.WeightedLocalControl

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

/-! # Countably labeled periodic copies of the finite cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem measurable_color (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (i : JetLattice.Label) :
    Measurable (color s₀ η K α γ d₀ q N i) := by
  unfold color
  split_ifs
  · exact ((JetDatum.term_measurable s₀ η K α γ d₀ _).comp (measurable_shift _)).div
      ((ChartKernel.measurable_H q).comp measurable_snd)
  · exact measurable_const

theorem color_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ q : ℝ) (N : ℕ) (i : JetLattice.Label) (p : JetPrototype.Phase) :
    0 ≤ color s₀ η K α γ d₀ q N i p := by
  unfold color
  split_ifs
  · exact div_nonneg (JetDatum.term_nonneg hs₀ hK hd₀ η α γ _ _) (H_nonneg _ _)
  · exact le_rfl

private theorem in_enlargement {s₀ η K α γ d₀ q : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) {i : JetLattice.Label} {p : JetPrototype.Phase}
    (hp : color s₀ η K α γ d₀ q N i p ≠ 0) :
    PlaneChart.join p.1.1 p.1.2 ∈ JetLattice.spatialEnlargement s₀ η 0 i := by
  have hi : i.annulus < N := by
    by_contra h
    exact hp (by simp only [color,ite_eq_right h])
  have hn : JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
      (shift (displacement i.lattice) p) ≠ 0 := by
    intro h
    exact hp (by simp only [color,ite_eq_left hi,h,zero_div])
  have hsp := JetSupport.initial_spatial_support η K α γ
    (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) i.positive hn
  constructor
  · rw [PlaneChart.transverse_join]
    apply Metric.mem_cthickening_of_dist_le _ _ _ _ hsp.1
    simpa [shift,displacement,jetScale] using (enlargementWidth_pos hη
      (DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1))).le
  · have hax : |p.1.2-JetLattice.axialShift i.lattice| < 1/8 := hsp.2
    change |axial (PlaneChart.join p.1.1 p.1.2)-JetLattice.axialShift i.lattice| ≤ _
    rw [PlaneChart.axial_join]
    linarith

theorem color_disjoint {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ)
    (p : JetPrototype.Phase) (i j : JetLattice.Label) (hij : i ≠ j)
    (hi : color s₀ η K α γ d₀ q N i p ≠ 0) : color s₀ η K α γ d₀ q N j p = 0 := by
  by_contra hj
  exact hij (JetLattice.common_point_label hs₀ hsmax hη hηmax (by norm_num : (0:ℝ) ≤ 1/32)
    (in_enlargement hs₀ hη hi) (in_enlargement hs₀ hη hj))

theorem color_summable {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ q : ℝ) (N : ℕ) (p : JetPrototype.Phase) :
    Summable (fun i => color s₀ η K α γ d₀ q N i p) :=
  JetSeries.summable_single_support (color_disjoint hs₀ hsmax hη hηmax K α γ d₀ q N p)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Finite weighted bounds for the countably labeled periodic seed -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem finite_sum_le_seed {s₀ η K d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (α γ q : ℝ) (N : ℕ) (u : Finset JetLattice.Label) (p : JetPrototype.Phase) :
    ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤ seed s₀ η K α γ d₀ q N p :=
  (color_summable hs₀ hsmax hη hηmax K α γ d₀ q N p).sum_le_tsum u
    (fun i _ => color_nonneg hs₀ hK hd₀ η α γ q N i p)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual labeled periodic approximation on a common local interval -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem initial_color_bounds {s₀ η K d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (α γ q : ℝ) (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p) :
    (∀ i p, 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ initial s₀ η K α γ d₀ q N h₀ p) ∧
    (∀ u : Finset JetLattice.Label, ∀ p,
      ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤ initial s₀ η K α γ d₀ q N h₀ p) := by
  have hf (u : Finset JetLattice.Label) (p) : ∑ i ∈ u, color s₀ η K α γ d₀ q N i p ≤
      initial s₀ η K α γ d₀ q N h₀ p :=
    (finite_sum_le_seed hs₀ hsmax hη hηmax hK hd₀ α γ q N u p).trans (le_add_of_nonneg_right (hh₀ p))
  refine ⟨?_,hf⟩
  intro i p
  classical
  exact ⟨color_nonneg hs₀ hK hd₀ η α γ q N i p,by simpa using hf {i} p⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotSeedCoreLower
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A localized periodic thermal seed, normalized in the singular weighted norm -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem bound_pos : 0 < bound := by
  unfold bound
  exact mul_pos (mul_pos (sq_pos_of_pos JetThermalKernel.bound_pos) (Real.exp_pos _)) tiltConstant_pos

theorem measurable_centered : Measurable centered :=
  ((measurable_id.add_const (1/2)).fract).sub_const (1/2)

theorem measurable_centeredSpace : Measurable centeredSpace := by
  apply Measurable.prodMk
  · apply (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.comp
    exact Measurable.of_eval (fun i => measurable_centered.comp
      (show Measurable (fun x : Space => x.1 i) from by fun_prop))
  · exact measurable_centered.comp measurable_snd

theorem measurable_raw (q δ : ℝ) : Measurable (raw q δ) := by
  have hjoin : Measurable (fun x : Space => PlaneChart.join x.1 x.2) :=
    split.symm.measurable.comp (measurable_snd.prodMk measurable_fst)
  exact (JetThermalKernel.J_smooth.continuous.measurable.comp
    ((hjoin.comp (measurable_centeredSpace.comp measurable_fst)).const_smul δ⁻¹)).mul
    ((JetThermalKernel.J_smooth.continuous.measurable.comp measurable_snd).div
      ((ChartKernel.measurable_H q).comp measurable_snd))

theorem raw_nonneg (q δ : ℝ) (p : JetPrototype.Phase) : 0 ≤ raw q δ p :=
  mul_nonneg (JetThermalKernel.J_nonneg _) (div_nonneg (JetThermalKernel.J_nonneg _) (H_nonneg _ _))

theorem velocity_bound (q : ℝ) (v : Velocity) :
    JetThermalKernel.J v/H q v ≤ JetThermalKernel.bound*Real.exp 2*tiltConstant := by
  by_cases hv : 1 ≤ ‖v‖
  · rw [JetThermalKernel.J_zero hv,zero_div]
    exact mul_nonneg (mul_nonneg JetThermalKernel.bound_pos.le (Real.exp_pos _).le) tiltConstant_pos.le
  · have hv2 : ‖v‖^2 ≤ 1 := by nlinarith [norm_nonneg v,lt_of_not_ge hv]
    have he : 1 ≤ Real.exp 2*Real.exp (-2*‖v‖^2) := by
      rw [← Real.exp_add,← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    apply (div_le_iff₀ (H_pos q v)).mpr
    calc
      _ ≤ JetThermalKernel.bound := JetThermalKernel.J_le v
      _ ≤ JetThermalKernel.bound*(Real.exp 2*Real.exp (-2*‖v‖^2)) :=
        by simpa only [mul_one] using mul_le_mul_of_nonneg_left he JetThermalKernel.bound_pos.le
      _ ≤ JetThermalKernel.bound*(Real.exp 2*(tiltConstant*H q v)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (JetGaussianEscape.gaussian_le_hot q v) (Real.exp_pos _).le)
          JetThermalKernel.bound_pos.le
      _ = _ := by ring

theorem raw_le (q δ : ℝ) (p : JetPrototype.Phase) : raw q δ p ≤ bound := by
  unfold raw bound
  have h := mul_le_mul
    (JetThermalKernel.J_le (δ⁻¹ • PlaneChart.join (centeredSpace p.1).1 (centeredSpace p.1).2))
    (velocity_bound q p.2)
    (div_nonneg (JetThermalKernel.J_nonneg _) (H_nonneg _ _)) JetThermalKernel.bound_pos.le
  exact h.trans_eq (by ring)

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # The localized thermal seed has positive essential weighted norm -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Metric
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem size_pos_of_positive_set {f : JetPrototype.Phase → ℝ} {R : ℝ}
    (hfm : Measurable f) (hb : ∀ p, |f p| ≤ R) {s : Set JetPrototype.Phase}
    (hs : FlightMeasure.phaseVolume s ≠ 0) (hf : ∀ p ∈ s, 0 < f p) : 0 < size f := by
  obtain ⟨p,hp,hbound⟩ := exists_mem_of_measure_ne_zero_of_ae hs
    (ae_restrict_of_ae (ae_abs_le_size hfm hb))
  exact (hf p hp).trans_le ((le_abs_self _).trans hbound)

end BoltzmannNonuniqueness.PhaseEssSup

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem centered_eq {x : ℝ} (hx : |x| < 1/2) : centered x = x := by
  have h := abs_lt.mp hx
  unfold centered
  rw [Int.fract_eq_self.mpr ⟨by linarith [h.1],by linarith [h.2]⟩]
  ring

theorem centeredSpace_eq {x : Space} (hx : ‖x‖ < 1/2) : centeredSpace x = x := by
  apply Prod.ext
  · ext i
    apply centered_eq
    exact (show |x.1 i| ≤ ‖x.1‖ from by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x.1 i).trans_lt
      ((norm_fst_le x).trans_lt hx)
  · apply centered_eq
    exact (show |x.2| ≤ ‖x‖ from by simpa only [Real.norm_eq_abs] using norm_snd_le x).trans_lt hx

theorem J_pos {v : Velocity} (hv : ‖v‖ < 1) : 0 < JetThermalKernel.J v := by
  have hn : JetThermalKernel.J v ≠ 0 := by
    change v ∈ Function.support JetThermalKernel.J
    rw [JetThermalKernel.J_support]
    simpa only [mem_ball,dist_zero_right] using hv
  exact lt_of_le_of_ne (JetThermalKernel.J_nonneg v) hn.symm

theorem raw_pos {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ)
    {p : JetPrototype.Phase} (hx : ‖p.1‖ < δ/4) (hv : ‖p.2‖ < 1/2) : 0 < raw q δ p := by
  have hc : centeredSpace p.1 = p.1 := centeredSpace_eq (by linarith)
  have hu : ‖p.1.1‖ < δ/4 := (norm_fst_le p.1).trans_lt hx
  have hz : |p.1.2| < δ/4 := by simpa only [Real.norm_eq_abs] using (norm_snd_le p.1).trans_lt hx
  have hj : ‖PlaneChart.join p.1.1 p.1.2‖ < δ := by
    have he := PlaneChart.norm_join_sq p.1.1 p.1.2
    have hsq := sq_abs p.1.2
    nlinarith [norm_nonneg p.1.1,norm_nonneg (PlaneChart.join p.1.1 p.1.2),abs_nonneg p.1.2]
  have harg : ‖δ⁻¹ • PlaneChart.join p.1.1 p.1.2‖ < 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hδ)]
    exact (inv_mul_lt_one₀ hδ).mpr hj
  unfold raw
  rw [hc]
  exact mul_pos (J_pos harg) (div_pos (J_pos (by linarith)) (H_pos q p.2))

theorem raw_size_pos {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ) :
    0 < PhaseEssSup.size (raw q δ) := by
  let s : Set JetPrototype.Phase := ball (0 : Space) (δ/4) ×ˢ ball (0 : Velocity) (1/2)
  have hs : FlightMeasure.phaseVolume s ≠ 0 := by
    change ((volume : Measure Space).prod (volume : Measure Velocity))
      (ball (0 : Space) (δ/4) ×ˢ ball (0 : Velocity) (1/2)) ≠ 0
    rw [Measure.prod_prod]
    exact mul_ne_zero (measure_ball_pos volume (0 : Space) (by linarith)).ne'
      (measure_ball_pos volume (0 : Velocity) (by norm_num : (0:ℝ) < 1/2)).ne'
  apply PhaseEssSup.size_pos_of_positive_set (measurable_raw q δ)
    (fun p => by rw [abs_of_nonneg (raw_nonneg q δ p)]; exact raw_le q δ p) hs
  intro p hp
  exact raw_pos hδ hδmax q (by simpa only [mem_ball,dist_zero_right] using hp.1)
    (by simpa only [mem_ball,dist_zero_right] using hp.2)

end BoltzmannNonuniqueness.HotSeedProfile

end

end

section

/-! # The normalized periodic hot seed has the data required by cap selection -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.HotSeedProfile

theorem normalized_bounds {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ 1) (q : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ p, 0 ≤ normalized q δ p ∧ normalized q δ p ≤ M := by
  have hs := raw_size_pos hδ hδmax q
  let c := δ/PhaseEssSup.size (raw q δ)
  have hc : 0 < c := div_pos hδ hs
  refine ⟨c*bound,mul_pos hc bound_pos,?_⟩
  intro p
  exact ⟨mul_nonneg hc.le (raw_nonneg q δ p),mul_le_mul_of_nonneg_left (raw_le q δ p) hc.le⟩

end BoltzmannNonuniqueness.HotSeedProfile

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicMildApproximation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded positive periodic mild states and finite-step continuation -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

namespace PeriodicMildState

theorem all_mild {q b L T R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L T R f₀) (hT : 0 ≤ T) :
    ∀ t, (fun p => F.value (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L F.value) (t,p)) :=
  mild_all_of_time_clamp hT L F.clamped F.mild

end PeriodicMildState

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapLabelFreeLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The rebuilt cold family of an actual cap shot -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.cold_properties {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    (∀ i, Measurable (F.cold i)) ∧ (∀ i u, 0 ≤ F.cold i u) ∧
      (∀ s : Finset JetLattice.Label, ∀ u, ∑ i ∈ s, F.cold i u ≤ F.solution.value u) ∧
      (∀ i, ColdMildAE q (N+1) (damping q (N+1) F.amplitude) T F.solution.value
        (color s₀ η K α γ d₀ q N i) (F.cold i)) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀ α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ 2*F.amplitude :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (F.initial_bound p)⟩
  have hL : 0 ≤ damping q (N+1) F.amplitude :=
    (bounds (q := q) (by positivity : 0 ≤ (N+1:ℝ)) F.amplitude_pos).1
  have hR : 0 ≤ 2*F.amplitude := mul_nonneg (by norm_num) F.amplitude_pos.le
  have hp := rebuiltColdFamily_properties hq (by positivity : 0 ≤ (N+1:ℝ)) hL hT hR le_rfl
    F.solution.measurable_value (measurable_color s₀ η K α γ d₀ q N)
    F.solution.value_bounds hc₀ hi.2 (F.solution.all_mild hT)
  exact ⟨hp.1,fun i u => (hp.2.1 i u).1,hp.2.2.1,hp.2.2.2.2⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapHotUndamped
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual rescaled cold density, before taking its atomic limit -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.coldTotal_properties {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    Measurable F.coldTotal ∧ ∀ u, Summable (fun i => F.cold i u) ∧
      0 ≤ F.coldTotal u ∧ F.coldTotal u ≤ F.solution.value u := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  refine ⟨Measurable.tsum hc.1,fun u => ?_⟩
  exact ⟨summable_of_sum_le (fun i => hc.2.1 i u) (fun s => hc.2.2.1 s u),
    tsum_nonneg (fun i => hc.2.1 i u),
    Real.tsum_le_of_sum_le (fun i => hc.2.1 i u) (fun s => hc.2.2.1 s u)⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_OffAxisBoxExhaustion
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Choosing a bounded representative of a collision kernel on the null axis -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

theorem offAxis_apply (K : Kernel (X × Velocity) Velocity) (z : X × Velocity)
    (hz : transverse z.2 ≠ 0) : offAxis K z = K z := by
  classical
  simp [offAxis,Kernel.piecewise_apply,hz]

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MainPositiveRemainderBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive iteration of the selected main-core collision kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem positiveMain_action (r s₀ η K α γ d₀ q : ℝ) (N : ℕ)
    (f : KineticPhase → ℝ≥0∞) (z : KineticPhase) :
    ChartKernel.action (positiveMainKernel r s₀ η K α γ d₀ q N) f z =
      ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N) f z+
      ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N) f z := by
  change (∫⁻ v, f (z.1,v) ∂(_+_)) = _
  rw [lintegral_add_measure]
  rfl

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RescaledBoundedGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A principal positive action plus a vanishing error for the actual cold gain -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.rescaled_cold_gain_majorant (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T)
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (hfone : ∀ z, f z ≤ 1) :
    ∀ᵐ v : Velocity,
      chartGain (volume.withDensity (fun p => ENNReal.ofReal (r*(H q p*F.coldTotal
        (r*x.1,(JetPeriodicDatum.spatialMap (r • x.2),p))))))
        (fun p => ENNReal.ofReal (H q p/H q v)*f (x,p)) v ≤
      ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N) f (x,v)+
        ENNReal.ofReal r*coldGainErrorConstant s₀ η K α d₀ q := by
  let E := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0)
  have hE : 0 ≤ E := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _
  have hc := F.rescaled_cold_measure_majorant_q80 hr hs₀ hsmax hη hηmax hK hα hγ hd₀
    hsmall hq₂ hT hTmax x ht
  have hesc : volume.withDensity (fun p => ENNReal.ofReal
      (r*(H q p*F.escapedTotal ((r*x.1,r • x.2),p)))) ≤
      ENNReal.ofReal (r*E) • volume.withDensity (fun p => ENNReal.ofReal (H q p)) := by
    rw [← withDensity_smul _ (ChartKernel.measurable_H q).ennreal_ofReal]
    apply withDensity_mono
    filter_upwards [] with p
    change ENNReal.ofReal (r*(H q p*_)) ≤ ENNReal.ofReal (r*E)*ENNReal.ofReal (H q p)
    rw [← ENNReal.ofReal_mul (mul_nonneg hr.le hE)]
    have he := F.escapedTotal_bound_global_q80 hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hdmax
      hsmall hq₂ hT hTmax 0 (z := ((r*x.1,r • x.2),p)) ht
    simp only [Real.rpow_zero,mul_one] at he
    apply ENNReal.ofReal_le_ofReal
    calc
      r*(H q p*F.escapedTotal ((r*x.1,r • x.2),p)) =
          (r*H q p)*F.escapedTotal ((r*x.1,r • x.2),p) := by ring
      _ ≤ (r*H q p)*E := mul_le_mul_of_nonneg_left he (mul_nonneg hr.le (H_nonneg q p))
      _ = (r*E)*H q p := by ring
  filter_upwards [ChartKernel.normalized_weight_scaled_bound hcarleman hq₁ hq₂
    (ENNReal.ofReal (r*E)),SheetApplication.ae_transverse_ne_zero] with v hv haxis
  have hg := chartGain_le_principal_add_remainders hc q v (fun p => hfone (x,p))
  have hrm := selectedRemainder_gain_bound_q80 (γ := γ) (N := N) hr hs₀ hsmax hη hηmax hK hα hd₀ hdmax hq₁ hq₂
    x (by nlinarith [ht.1]) haxis
  have hem : normalizedChartGain (volume.withDensity (fun p => ENNReal.ofReal
      (r*(H q p*F.escapedTotal ((r*x.1,r • x.2),p))))) q v ≤
      ENNReal.ofReal (r*E)*ENNReal.ofReal (HotApplication.realBound q) :=
    (chartGain_mono_measure hesc _ v).trans hv
  have haction : chartGain (selectedColdKernel r s₀ η K α γ d₀ N x)
      (fun p => ENNReal.ofReal (H q p/H q v)*f (x,p)) v =
      ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N) f (x,v) := by
    rw [ChartKernel.action,selectedFreeKernel,ChartKernel.offAxis_apply _ _ haxis]
    exact (ChartKernel.lintegral_inputKernel_eq_gain
      (selectedColdKernel r s₀ η K α γ d₀ N) q (x,v) (f := fun p => f (x,p))
      (hf.comp (measurable_const.prodMk measurable_id))).symm
  apply (hg.trans (add_le_add (add_le_add le_rfl hrm) hem)).trans_eq
  rw [haction,ENNReal.ofReal_mul hr.le]
  simp only [coldGainErrorConstant,mul_add,mul_assoc,add_assoc,E]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual cap-sized hot input retains the same principal cold action -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

theorem action_const_mul {X : Type*} [MeasurableSpace X]
    (K : Kernel (X × Velocity) Velocity) (f : X × Velocity → ℝ≥0∞)
    (a : ℝ≥0∞) (ha : a ≠ ∞) (z : X × Velocity) :
    action K (fun w => a*f w) z = a*action K f z :=
  lintegral_const_mul' a _ ha

end BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.rescaled_cold_gain_majorant_two (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T)
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (hftwo : ∀ z, f z ≤ 2) :
    ∀ᵐ v : Velocity,
      chartGain (volume.withDensity (fun p => ENNReal.ofReal (r*(H q p*F.coldTotal
        (r*x.1,(JetPeriodicDatum.spatialMap (r • x.2),p))))))
        (fun p => ENNReal.ofReal (H q p/H q v)*f (x,p)) v ≤
      ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N) f (x,v)+
        2*(ENNReal.ofReal r*coldGainErrorConstant s₀ η K α d₀ q) := by
  let a : ℝ≥0∞ := 1/2
  have ha : a ≠ ∞ := by norm_num [a]
  have hcancel : (2:ℝ≥0∞)*a = 1 := by
    dsimp only [a]
    rw [one_div]
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hbound (z) : a*f z ≤ 1 := by
    calc
      _ ≤ a*2 := mul_le_mul' le_rfl (hftwo z)
      _ = 1 := by rw [mul_comm,hcancel]
  have h := F.rescaled_cold_gain_majorant (f := fun z => a*f z) hcarleman hr hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hdmax hsmall hq₁ hq₂ hT hTmax x ht (measurable_const.mul hf) hbound
  filter_upwards [h] with v hv
  have hfunc : (fun p => ENNReal.ofReal (H q p/H q v)*(a*f (x,p))) =
      (fun p => a*(ENNReal.ofReal (H q p/H q v)*f (x,p))) := by
    funext p
    ac_rfl
  rw [hfunc,chartGain_const_mul_right _ a ha,ChartKernel.action_const_mul _ _ a ha] at hv
  have htwo := mul_le_mul' (le_rfl : (2:ℝ≥0∞) ≤ 2) hv
  simpa only [mul_add,← mul_assoc,hcancel,one_mul] using htwo

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapMixedPositiveBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual cold density in the Euclidean dilation coordinates -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.dilatedCold_measurable {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) (r : ℝ) :
    Measurable (F.dilatedCold r) := by
  have hc := (F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).1
  have hx : Measurable (fun z : KineticPhase =>
      (r*z.1.1,(JetPeriodicDatum.spatialMap (r • z.1.2),z.2))) := by
    apply Measurable.prodMk (by fun_prop)
    exact ((JetPeriodicDatum.spatialMap_measurePreserving.measurable.comp
      (by fun_prop)).prodMk measurable_snd)
  exact measurable_const.mul (((ChartKernel.measurable_H q).comp measurable_snd).mul (hc.comp hx))

theorem CapApproximation.dilatedCold_nonneg {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N) (hr : 0 ≤ r)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) (z : KineticPhase) :
    0 ≤ F.dilatedCold r z :=
  mul_nonneg hr (mul_nonneg (H_nonneg q z.2)
    ((F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).2 _).2.1)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual mixed cutoff gain is controlled by the main positive action -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.mixed_gain_le_selected_action (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T)
    (b : ℝ) {f : KineticPhase → ℝ} (hf : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hftwo : ∀ z, f z ≤ 2) :
    ∀ᵐ v : Velocity, ENNReal.ofReal (CollisionCompactness.mixedGainDensity b
      (F.dilatedCold r) (fun z => H q z.2*f z) (x,v)) ≤
      ENNReal.ofReal (H q v)*
        (ChartKernel.action (selectedFreeKernel r s₀ η K α γ d₀ q N)
          (fun z => ENNReal.ofReal (f z)) (x,v)+
          2*(ENNReal.ofReal r*coldGainErrorConstant s₀ η K α d₀ q)) := by
  have hc := F.dilatedCold_measurable hs₀ hsmax hη hηmax hK hd₀.le hq₂ hT r
  have hcn := F.dilatedCold_nonneg hr.le hs₀ hsmax hη hηmax hK hd₀.le hq₂ hT
  have hg := F.rescaled_cold_gain_majorant_two hcarleman hr hs₀ hsmax hη hηmax hK hα hαmax
    hγ hd₀ hdmax hsmall hq₁ hq₂ hT hTmax x ht hf.ennreal_ofReal
    (fun z => (ENNReal.ofReal_le_ofReal (hftwo z)).trans_eq (by norm_num))
  filter_upwards [hg,CollisionCompactness.normalized_mixed_cutoff_le_chart hcarleman b q
    hc hf hcn hfn x] with v hv hm
  exact hm.trans (mul_le_mul' le_rfl hv)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The normalized mixed source is bounded by the positive main kernel -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.normalized_mixed_gain_le_positive_q80_oai (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T r : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (x : SpaceTime) (ht : r*x.1 ∈ Ioc 0 T)
    (b : ℝ) {f : KineticPhase → ℝ} (hf : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hftwo : ∀ z, f z ≤ 2) :
    ∀ᵐ v : Velocity, ENNReal.ofReal ((2*CollisionCompactness.mixedGainDensity b
      (F.dilatedCold r) (fun z => H q z.2*f z) (x,v))/H q v) ≤
        ChartKernel.action (positiveMainKernel r s₀ η K α γ d₀ q N)
          (fun z => ENNReal.ofReal (f z)) (x,v)+
          4*(ENNReal.ofReal r*coldGainErrorConstant s₀ η K α d₀ q) := by
  filter_upwards [F.mixed_gain_le_selected_action hcarleman hr hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hT hTmax x ht b hf hfn hftwo] with v hv
  rw [ENNReal.ofReal_div_of_pos (H_pos q v)]
  apply (ENNReal.div_le_iff' (ne_of_gt (ENNReal.ofReal_pos.mpr (H_pos q v)))
    ENNReal.ofReal_ne_top).mpr
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply (mul_le_mul' le_rfl hv).trans_eq
  rw [positiveMain_action]
  norm_num only [ENNReal.ofReal_ofNat]
  ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.CapApproximation.normalized_mixed_gain_le_positive_q80_oai
