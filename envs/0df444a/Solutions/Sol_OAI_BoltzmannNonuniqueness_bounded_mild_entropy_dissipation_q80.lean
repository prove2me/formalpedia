-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:31:02.54609+00:00
-- url     : https://prove2.me/submissions/615de505-884b-42a2-a9dd-8721f62dd2e6

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Admissibility
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.sphereArea_isFiniteMeasure _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The entropy-class solution and nonuniqueness statement

The solution class follows Definition 2.1 with explicit integrability conditions.
The renormalized equation uses derivatives of smooth periodic lifts, while
integrals use volume on the unit torus and Euclidean velocity space.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem maxwellian_pos (v : Velocity) : 0 < maxwellian v := by
  unfold maxwellian
  positivity

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AngularPairTests
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Angular normalization of the hard-sphere collision kernel

The angular measure is the ordinary area measure `volume.toSphere`. Its mass is
`4 * π`; the absolute normal component integrates to `2 * π * ‖g‖`.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

/-- The loss-frequency angular normalization in the manuscript. -/
theorem integral_collisionKernel_sphereArea (v w : Velocity) :
    (∫ ω : Sphere, collisionKernel v w ω ∂sphereArea) = 2 * Real.pi * ‖v - w‖ :=
  integral_abs_inner_sphereArea (v - w)

end BoltzmannNonuniqueness

end

end

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

/-- Absorbing an even power into half the Gaussian decay gives an explicit factorial constant. -/
theorem even_pow_mul_gaussian_le (r : ℝ) (n : ℕ) :
    r ^ (2 * n) * Real.exp (-r ^ 2) ≤
      (2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (-r ^ 2 / 2) := by
  have hfact : 0 < (n.factorial : ℝ) := by positivity
  have hpow : (r ^ 2 / 2) ^ n ≤ Real.exp (r ^ 2 / 2) * (n.factorial : ℝ) :=
    (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp (r ^ 2 / 2) (by positivity) n)
  have hid : r ^ (2 * n) = (2 : ℝ) ^ n * (r ^ 2 / 2) ^ n := by
    rw [pow_mul, ← mul_pow]
    congr 1
    ring
  calc
    r ^ (2 * n) * Real.exp (-r ^ 2) =
        (2 : ℝ) ^ n * (r ^ 2 / 2) ^ n * Real.exp (-r ^ 2) := by rw [hid]
    _ ≤ (2 : ℝ) ^ n * (Real.exp (r ^ 2 / 2) * (n.factorial : ℝ)) *
        Real.exp (-r ^ 2) := by gcongr
    _ = (2 : ℝ) ^ n * (n.factorial : ℝ) *
        (Real.exp (r ^ 2 / 2) * Real.exp (-r ^ 2)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

theorem H_even_moment_le (q : ℝ) (v : Velocity) (n : ℕ) :
    ‖v‖ ^ (2 * n) * H q v ≤
      (2 : ℝ) ^ n * (n.factorial : ℝ) * gaussianMajorant (1 / 2) q v := by
  have hw : 0 ≤ 1 + singularity q (transverse v) :=
    add_nonneg zero_le_one (singularity_nonneg q (transverse v))
  calc
    ‖v‖ ^ (2 * n) * H q v ≤ ‖v‖ ^ (2 * n) * gaussianMajorant 1 q v :=
      mul_le_mul_of_nonneg_left (H_le_gaussianMajorant q v) (pow_nonneg (norm_nonneg _) _)
    _ = (‖v‖ ^ (2 * n) * Real.exp (-‖v‖ ^ 2)) *
        (1 + singularity q (transverse v)) := by
      simp only [gaussianMajorant, neg_mul, one_mul]
      ring
    _ ≤ ((2 : ℝ) ^ n * (n.factorial : ℝ) * Real.exp (-‖v‖ ^ 2 / 2)) *
        (1 + singularity q (transverse v)) :=
      mul_le_mul_of_nonneg_right (even_pow_mul_gaussian_le ‖v‖ n) hw
    _ = _ := by
      unfold gaussianMajorant
      rw [show -(1 / 2 : ℝ) * ‖v‖ ^ 2 = -‖v‖ ^ 2 / 2 by ring]
      ring

theorem integrable_even_moment_H {q : ℝ} (hq : q < 2) (n : ℕ) :
    Integrable (fun v : Velocity => ‖v‖ ^ (2 * n) * H q v) := by
  have hb := (integrable_gaussianMajorant (β := 1 / 2) (by norm_num) hq).const_mul
    ((2 : ℝ) ^ n * (n.factorial : ℝ))
  have hn : AEStronglyMeasurable (fun v : Velocity => ‖v‖ ^ (2 * n)) := by fun_prop
  apply hb.mono' (hn.mul (integrable_H hq).aestronglyMeasurable)
  filter_upwards [] with v
  rw [Pi.mul_apply, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (H_nonneg q v))]
  exact H_even_moment_le q v n

private theorem one_add_rpow_le {s p : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p) :
    (1 + s) ^ p ≤ (2 : ℝ) ^ p * (1 + s ^ p) := by
  by_cases hs₁ : s ≤ 1
  · calc
      (1 + s) ^ p ≤ (2 : ℝ) ^ p :=
        Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ ≤ (2 : ℝ) ^ p * (1 + s ^ p) := by
        have hs' : 0 ≤ s ^ p := Real.rpow_nonneg hs p
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ 1 + s ^ p from le_add_of_nonneg_right hs')
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)
  · have hs₁' : 1 ≤ s := le_of_lt (lt_of_not_ge hs₁)
    calc
      (1 + s) ^ p ≤ (2 * s) ^ p :=
        Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ = (2 : ℝ) ^ p * s ^ p := Real.mul_rpow (by norm_num) hs
      _ ≤ (2 : ℝ) ^ p * (1 + s ^ p) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one)
          (Real.rpow_nonneg (by norm_num) p)

/-- Raising the majorant to a positive power multiplies its transverse singular exponent. -/
theorem H_rpow_le {p : ℝ} (hp : 0 ≤ p) (q : ℝ) (v : Velocity) :
    H q v ^ p ≤ (2 : ℝ) ^ p * gaussianMajorant p (p * q) v := by
  have hs : 0 ≤ singularity q (transverse v) := singularity_nonneg q (transverse v)
  have he : Real.exp (-‖v‖ ^ 2) ^ p = Real.exp (-p * ‖v‖ ^ 2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hr : singularity q (transverse v) ^ p = singularity (p * q) (transverse v) := by
    unfold singularity
    rw [← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  calc
    H q v ^ p ≤ gaussianMajorant 1 q v ^ p :=
      Real.rpow_le_rpow (H_nonneg q v) (H_le_gaussianMajorant q v) hp
    _ = Real.exp (-p * ‖v‖ ^ 2) * (1 + singularity q (transverse v)) ^ p := by
      unfold gaussianMajorant
      simp only [neg_mul, one_mul]
      rw [Real.mul_rpow (Real.exp_nonneg _) (by positivity), he]
      simp only [neg_mul]
    _ ≤ Real.exp (-p * ‖v‖ ^ 2) *
        ((2 : ℝ) ^ p * (1 + singularity q (transverse v) ^ p)) :=
      mul_le_mul_of_nonneg_left (one_add_rpow_le hs hp) (Real.exp_nonneg _)
    _ = _ := by rw [hr]; unfold gaussianMajorant; ring

/-- The precise power-integrability range used for the initial cutoff solutions. -/
theorem integrable_rpow_H {p q : ℝ} (hp : 1 ≤ p) (hpq : p * q < 2) :
    Integrable (fun v : Velocity => H q v ^ p) := by
  have hp₀ : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hp_nonneg : 0 ≤ p := hp₀.le
  have hm : AEStronglyMeasurable (fun v : Velocity => H q v ^ p) := by
    unfold H singularity transverse
    fun_prop
  apply ((integrable_gaussianMajorant hp₀ hpq).const_mul ((2 : ℝ) ^ p)).mono' hm
  filter_upwards [] with v
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (H_nonneg q v) p)]
  exact H_rpow_le hp₀.le q v

theorem exists_integrable_rpow_H {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ p : ℝ, 1 < p ∧ Integrable (fun v : Velocity => H q v ^ p) := by
  have hq₀ : 0 < q := lt_trans zero_lt_one hq₁
  have hdiv : (1 : ℝ) < 2 / q := (lt_div_iff₀ hq₀).mpr (by simpa using hq₂)
  obtain ⟨p, hp₁, hp₂⟩ := exists_between hdiv
  exact ⟨p, hp₁, integrable_rpow_H hp₁.le ((lt_div_iff₀ hq₀).mp hp₂)⟩

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticDensityMeasurable
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measure-preserving grouping of physical time and phase coordinates -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem kineticGrouping_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving (MeasurableEquiv.prodAssoc :
      ((ℝ × Position) × Velocity) ≃ᵐ ℝ × Phase)
      ((μ.prod volume).prod volume) (μ.prod volume) := by
  simpa only [Measure.volume_eq_prod] using measurePreserving_prodAssoc μ
    (volume : Measure Position) (volume : Measure Velocity)

end BoltzmannNonuniqueness

end

end

section

/-! # Collision representative invariance with space and time parameters -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.KineticCollisionNullSets

variable {X : Type*} [MeasurableSpace X]

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The Maxwellian reference entropy

Finite weighted absolute entropy makes the relative-entropy integral genuine.
Its nonnegativity is proved, including the zero-density convention.
-/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem log_maxwellian (v : Velocity) :
    Real.log (maxwellian v) = -(3 / 2 : ℝ) * Real.log (2 * Real.pi) - ‖v‖ ^ 2 / 2 := by
  have hp : 0 < (2 : ℝ) * Real.pi := by positivity
  rw [maxwellian, Real.log_mul (Real.rpow_pos_of_pos hp _).ne' (Real.exp_ne_zero _),
    Real.log_rpow hp, Real.log_exp]
  ring

theorem integrable_maxwellian : Integrable maxwellian := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (by norm_num : 0 < ((1 / 2 : ℂ)).re) 0 (0 : Velocity)).norm
  have hg : Integrable (fun v : Velocity => Real.exp (-‖v‖ ^ 2 / 2)) := by
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    funext v
    simp only [zero_mul, add_zero, Complex.norm_exp]
    congr 1
    norm_num
    norm_cast
    ring
  exact hg.const_mul _

theorem integrable_maxwellian_phase : Integrable (fun z : Phase => maxwellian z.2) :=
  integrable_maxwellian.comp_snd volume

end BoltzmannNonuniqueness

end

end

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_RegularizedLogBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # An integrable logarithmic majorant for positive regularized densities -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem abs_log_le_power_add_lower {l u ε : ℝ} (hl : 0 < l) (hlu : l ≤ u)
    (hε : 0 < ε) : |Real.log u| ≤ u^ε/ε+|Real.log l| := by
  have hu : 0 < u := hl.trans_le hlu
  have hlow := Real.log_le_log hl hlu
  have hup := Real.log_le_rpow_div hu.le hε
  have hp : 0 ≤ u^ε/ε := div_nonneg (Real.rpow_nonneg hu.le ε) hε.le
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log l)],by
    linarith [abs_nonneg (Real.log l)]⟩

theorem logarithmicMajorant_integrable {q B p δ : ℝ} (hq : q < 2)
    (hp : Integrable (fun v : Velocity => H q v^p)) :
    Integrable (logarithmicMajorant q B p δ) := by
  have h := (hp.const_mul (B^(p-1)/(p-1))).add
    (((integrable_H hq).const_mul (|Real.log δ|+|-(3/2:ℝ)*Real.log (2*Real.pi)|)).add
      ((integrable_even_moment_H hq 1).const_mul (5/2:ℝ)))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  simp only [logarithmicMajorant,Nat.reduceMul,Pi.add_apply]
  ring

theorem logarithm_weight_bound {q B p δ u : ℝ} (hB : 0 ≤ B) (hp : 1 < p)
    (hδ : 0 < δ) (v : Velocity)
    (hl : δ*Real.exp (-2*‖v‖^2) ≤ u) (hu : u ≤ B*H q v) :
    |Real.log (u/maxwellian v)| *H q v ≤ logarithmicMajorant q B p δ v := by
  have hp' : 0 < p-1 := sub_pos.mpr hp
  have hl' : 0 < δ*Real.exp (-2*‖v‖^2) := mul_pos hδ (Real.exp_pos _)
  have hu' : 0 < u := hl'.trans_le hl
  have hlb := abs_log_le_power_add_lower hl' hl hp'
  have hlogl : Real.log (δ*Real.exp (-2*‖v‖^2)) = Real.log δ-2*‖v‖^2 := by
    rw [Real.log_mul hδ.ne' (Real.exp_ne_zero _),Real.log_exp]
    ring
  rw [hlogl] at hlb
  have hlabs : |Real.log δ-2*‖v‖^2| ≤ |Real.log δ|+2*‖v‖^2 := by
    exact (abs_sub (Real.log δ) (2*‖v‖^2)).trans_eq
      (congrArg (fun x : ℝ => |Real.log δ|+x)
        (abs_of_nonneg (show 0 ≤ 2*‖v‖^2 by positivity)))
  have hmabs : |Real.log (maxwellian v)| ≤
      |-(3/2:ℝ)*Real.log (2*Real.pi)|+‖v‖^2/2 := by
    rw [log_maxwellian]
    exact (abs_sub (-(3/2:ℝ)*Real.log (2*Real.pi)) (‖v‖^2/2)).trans_eq
      (congrArg (fun x : ℝ => |-(3/2:ℝ)*Real.log (2*Real.pi)|+x)
        (abs_of_nonneg (show 0 ≤ ‖v‖^2/2 by positivity)))
  have hpow : u^(p-1) ≤ B^(p-1)*H q v^(p-1) := by
    rw [← Real.mul_rpow hB (H_nonneg q v)]
    exact Real.rpow_le_rpow hu'.le hu hp'.le
  have hlog : |Real.log (u/maxwellian v)| ≤
      B^(p-1)*H q v^(p-1)/(p-1)+
        (|Real.log δ|+|-(3/2:ℝ)*Real.log (2*Real.pi)|+(5/2:ℝ)*‖v‖^2) := by
    rw [Real.log_div hu'.ne' (maxwellian_pos v).ne']
    have ha := abs_sub (Real.log u) (Real.log (maxwellian v))
    have hd := div_le_div_of_nonneg_right hpow hp'.le
    linarith
  have hpower : H q v^(p-1)*H q v = H q v^p := by
    rw [← Real.rpow_add_one (H_pos q v).ne']
    congr 1
    ring
  calc
    _ ≤ (B^(p-1)*H q v^(p-1)/(p-1)+
        (|Real.log δ|+|-(3/2:ℝ)*Real.log (2*Real.pi)|+(5/2:ℝ)*‖v‖^2))*H q v :=
      mul_le_mul_of_nonneg_right hlog (H_nonneg q v)
    _ = logarithmicMajorant q B p δ v := by
      unfold logarithmicMajorant
      rw [add_mul]
      congr 1
      calc
        _ = (B^(p-1)/(p-1))*(H q v^(p-1)*H q v) := by ring
        _ = _ := by rw [hpower]

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyIntegralBalance
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The regularized entropy primitive used at zeros of finite approximations -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem scalarRelativeEntropy_eq {m : ℝ} (hm : 0 < m) (f : ℝ) :
    scalarRelativeEntropy m f = f*Real.log (f/m)-f+m := by
  by_cases hf : f = 0
  · simp [scalarRelativeEntropy,hf]
  · rw [Real.log_div hf hm.ne']
    unfold scalarRelativeEntropy
    ring

theorem scalarRelativeEntropy_hasDerivAt {m f : ℝ} (hm : 0 < m) (hf : 0 < f) :
    HasDerivAt (scalarRelativeEntropy m) (Real.log (f/m)) f := by
  have h := ((Real.hasDerivAt_mul_log hf.ne').sub
    ((hasDerivAt_id f).mul_const (1+Real.log m))).add_const m
  rw [Real.log_div hf.ne' hm.ne']
  refine h.congr_deriv (Eq.symm ?_)
  · ring

theorem regularizedEntropy_hasDerivAt {m e δ f : ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (hf : 0 ≤ f) :
    HasDerivAt (regularizedEntropy m e δ) (Real.log ((f+δ*e)/m)) f := by
  have hp : 0 < f+δ*e := add_pos_of_nonneg_of_pos hf (mul_pos hδ he)
  have h := (((scalarRelativeEntropy_hasDerivAt hm hp).comp f
    ((hasDerivAt_id f).add_const (δ*e))).sub_const (scalarRelativeEntropy m (δ*e))).add_const m
  refine h.congr_deriv (Eq.symm ?_)
  · ring

end BoltzmannNonuniqueness

end

end

section

/-! # The regularized entropy chain rule on an absolutely continuous free path -/

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace BoltzmannNonuniqueness

theorem regularizedEntropy_lipschitz {m e δ R : ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (_hR : 0 ≤ R) :
    ∃ C : ℝ≥0, LipschitzOnWith C (regularizedEntropy m e δ) (Icc 0 R) := by
  let L := Real.log (δ*e/m)
  let U := Real.log ((R+δ*e)/m)
  let C : ℝ≥0 := ⟨|L|+|U|,add_nonneg (abs_nonneg _) (abs_nonneg _)⟩
  refine ⟨C,(convex_Icc (0:ℝ) R).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (regularizedEntropy_hasDerivAt hm he hδ hx.1).hasDerivWithinAt) ?_⟩
  intro x hx
  have hl : L ≤ Real.log ((x+δ*e)/m) := Real.log_le_log (div_pos (mul_pos hδ he) hm)
    (div_le_div_of_nonneg_right (by linarith [hx.1]) hm.le)
  have hu : Real.log ((x+δ*e)/m) ≤ U := Real.log_le_log
    (div_pos (add_pos_of_nonneg_of_pos hx.1 (mul_pos hδ he)) hm)
    (div_le_div_of_nonneg_right (by linarith [hx.2]) hm.le)
  have hb : |Real.log ((x+δ*e)/m)| ≤ |L|+|U| := abs_le.mpr ⟨by
    linarith [neg_abs_le L,abs_nonneg U],by linarith [le_abs_self U,abs_nonneg L]⟩
  exact_mod_cast hb

theorem lipschitzOnWith_comp_absolutelyContinuousOnInterval {g f : ℝ → ℝ} {s : Set ℝ} {K : ℝ≥0}
    {a b : ℝ} (hg : LipschitzOnWith K g s) (hmaps : ∀ t ∈ Set.uIcc a b, f t ∈ s)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b := by
  have h0 := hf
  unfold AbsolutelyContinuousOnInterval at h0 ⊢
  have h1 := h0.const_mul (K : ℝ)
  rw [mul_zero] at h1
  refine squeeze_zero' ?_ ?_ h1
  · exact Filter.Eventually.of_forall (fun E => Finset.sum_nonneg (fun i _ => dist_nonneg))
  · refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall (fun E hE => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' := hE.left i hi
    have := hg (hmaps _ hi'.left) (hmaps _ hi'.right)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) this
    rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist, ENNReal.coe_toReal] at h2

theorem regularizedEntropy_chain_rule {a b m e δ R : ℝ} {F r : ℝ → ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hFn : ∀ t ∈ uIcc a b, 0 ≤ F t) (hFb : ∀ t ∈ uIcc a b, F t ≤ R)
    (hr : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt F (r t) t) :
    (∫ t in a..b, Real.log ((F t+δ*e)/m)*r t) =
      regularizedEntropy m e δ (F b)-regularizedEntropy m e δ (F a) := by
  obtain ⟨C,hC⟩ := regularizedEntropy_lipschitz hm he hδ hR
  have hc : AbsolutelyContinuousOnInterval (fun t => regularizedEntropy m e δ (F t)) a b :=
    lipschitzOnWith_comp_absolutelyContinuousOnInterval hC (fun t ht => ⟨hFn t ht,hFb t ht⟩) hF
  rw [← hc.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hr] with t ht hmem
  have hmemb : t ∈ uIcc a b := uIoc_subset_uIcc hmem
  exact ((regularizedEntropy_hasDerivAt hm he hδ (hFn t hmemb)).comp t (ht hmemb)).deriv.symm

end BoltzmannNonuniqueness

end

end

section

/-! # The entropy balance for an integral characteristic path -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem regularizedEntropy_integral_path {a b m e δ R A : ℝ} {r : ℝ → ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hr : IntervalIntegrable r volume a b)
    (hn : ∀ t ∈ uIcc a b, 0 ≤ A+∫ s in a..t, r s)
    (hb : ∀ t ∈ uIcc a b, A+(∫ s in a..t, r s) ≤ R) :
    (∫ t in a..b, Real.log (((A+∫ s in a..t, r s)+δ*e)/m)*r t) =
      regularizedEntropy m e δ (A+∫ s in a..b, r s)-regularizedEntropy m e δ A := by
  have hprimitive := hr.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : a ∈ uIcc a b)
  have hconstant : AbsolutelyContinuousOnInterval (fun _ : ℝ => A) a b := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  have hp : AbsolutelyContinuousOnInterval (fun t => A+∫ s in a..t, r s) a b :=
    hconstant.add hprimitive
  have hd : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (fun t => A+∫ s in a..t, r s) (r t) t := by
    filter_upwards [hr.ae_hasDerivAt_integral] with t ht hmem
    exact (ht hmem a left_mem_uIcc).const_add A
  simpa only [intervalIntegral.integral_same,add_zero] using
    regularizedEntropy_chain_rule hm he hδ hR hp hn hb hd

end BoltzmannNonuniqueness

end

end

section

/-! # Almost-everywhere bounds suffice for the entropy chain rule on a free path -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem continuous_path_bounds_of_ae {T R : ℝ} {F : ℝ → ℝ}
    (hT : 0 < T) (hR : 0 ≤ R) (hF : ContinuousOn F (Icc 0 T))
    (hae : ∀ᵐ t ∂volume.restrict (Icc 0 T), F t ∈ Icc 0 R) :
    ∀ t ∈ Icc 0 T, F t ∈ Icc 0 R := by
  let G : ℝ → ℝ := fun t => max 0 (min R (F t))
  have hG : ContinuousOn G (Icc 0 T) := continuousOn_const.sup (continuousOn_const.inf hF)
  have he : F =ᵐ[volume.restrict (Icc 0 T)] G := by
    filter_upwards [hae] with t ht
    dsimp [G]
    rw [min_eq_right ht.2,max_eq_right ht.1]
  have heq := Measure.eqOn_Icc_of_ae_eq volume hT.ne he hF hG
  intro t ht
  rw [heq ht]
  exact ⟨le_max_left _ _,max_le hR (min_le_left _ _)⟩

theorem regularizedEntropy_integral_path_of_ae_bounds {T m e δ R A : ℝ} {r : ℝ → ℝ}
    (hT : 0 < T) (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hr : IntervalIntegrable r volume 0 T)
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 T), (A+∫ s in 0..t, r s) ∈ Icc 0 R) :
    (∫ t in 0..T, Real.log (((A+∫ s in 0..t, r s)+δ*e)/m)*r t) =
      regularizedEntropy m e δ (A+∫ s in 0..T, r s)-regularizedEntropy m e δ A := by
  have hc : ContinuousOn (fun t => A+∫ s in 0..t, r s) (Icc 0 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hr
      (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
    rw [uIcc_of_le hT.le] at h
    exact continuousOn_const.add h
  have hb := continuous_path_bounds_of_ae hT hR hc hbound
  apply regularizedEntropy_integral_path hm he hδ hR hr
  · simpa only [uIcc_of_le hT.le] using fun t ht => (hb t ht).1
  · simpa only [uIcc_of_le hT.le] using fun t ht => (hb t ht).2

end BoltzmannNonuniqueness

end

end

section

/-! # Integrating the entropy chain rule over the characteristic labels -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem entropy_integral_balance {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (a m e R : Phase → ℝ) (r : ℝ × Phase → ℝ)
    (hm : ∀ p, 0 < m p) (he : ∀ p, 0 < e p) (hR : ∀ p, 0 ≤ R p)
    (hri : Integrable r ((volume.restrict (Icc 0 T)).prod volume))
    (hbound : ∀ᵐ p : Phase, ∀ᵐ t ∂volume.restrict (Icc 0 T),
      entropyPath a r t p ∈ Icc 0 (R p))
    (hET : Integrable (fun p => regularizedEntropy (m p) (e p) δ (entropyPath a r T p)))
    (hE0 : Integrable (fun p => regularizedEntropy (m p) (e p) δ (a p)))
    (hLi : Integrable (fun z : ℝ × Phase =>
      Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z)
      ((volume.restrict (Icc 0 T)).prod volume)) :
    (∫ p : Phase, regularizedEntropy (m p) (e p) δ (entropyPath a r T p))-
      (∫ p : Phase, regularizedEntropy (m p) (e p) δ (a p)) =
    ∫ z : ℝ × Phase, Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z
      ∂(volume.restrict (Icc 0 T)).prod volume := by
  have hp : ∀ᵐ p : Phase,
      regularizedEntropy (m p) (e p) δ (entropyPath a r T p)-
        regularizedEntropy (m p) (e p) δ (a p) =
      ∫ t, Real.log ((entropyPath a r t p+δ*e p)/m p)*r (t,p) ∂volume.restrict (Icc 0 T) := by
    filter_upwards [hri.prod_left_ae,hbound] with p hp hb
    have hpr : IntervalIntegrable (fun t => r (t,p)) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hp
    have h := regularizedEntropy_integral_path_of_ae_bounds hT (hm p) (he p) hδ (hR p) hpr hb
    rw [intervalIntegral.integral_of_le hT.le,← integral_Icc_eq_integral_Ioc] at h
    exact h.symm
  calc
    _ = ∫ p : Phase, regularizedEntropy (m p) (e p) δ (entropyPath a r T p)-
        regularizedEntropy (m p) (e p) δ (a p) := (integral_sub hET hE0).symm
    _ = ∫ p : Phase, ∫ t, Real.log ((entropyPath a r t p+δ*e p)/m p)*r (t,p)
        ∂volume.restrict (Icc 0 T) := integral_congr_ae hp
    _ = _ := (integral_prod_symm _ hLi).symm

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_ScalarEntropyConvex
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The scalar relative-entropy balance along characteristic paths -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem scalar_entropy_integral_balance {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (a m e R : Phase → ℝ) (r : ℝ × Phase → ℝ)
    (hm : ∀ p, 0 < m p) (he : ∀ p, 0 < e p) (hR : ∀ p, 0 ≤ R p)
    (hri : Integrable r ((volume.restrict (Icc 0 T)).prod volume))
    (hbound : ∀ᵐ p : Phase, ∀ᵐ t ∂volume.restrict (Icc 0 T),
      entropyPath a r t p ∈ Icc 0 (R p))
    (hET : Integrable (fun p => scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p)))
    (hE0 : Integrable (fun p => scalarRelativeEntropy (m p) (a p+δ*e p)))
    (hbase : Integrable (fun p => scalarRelativeEntropy (m p) (δ*e p))) (hmi : Integrable m)
    (hLi : Integrable (fun z : ℝ × Phase =>
      Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z)
      ((volume.restrict (Icc 0 T)).prod volume)) :
    (∫ p : Phase, scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p))-
      (∫ p : Phase, scalarRelativeEntropy (m p) (a p+δ*e p)) =
    ∫ z : ℝ × Phase, Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z
      ∂(volume.restrict (Icc 0 T)).prod volume := by
  have hAT : Integrable (fun p => regularizedEntropy (m p) (e p) δ (entropyPath a r T p)) :=
    (hET.sub hbase).add hmi
  have hA0 : Integrable (fun p => regularizedEntropy (m p) (e p) δ (a p)) :=
    (hE0.sub hbase).add hmi
  have h := entropy_integral_balance hT hδ a m e R r hm he hR hri hbound hAT hA0 hLi
  have heq : (fun p => scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p)-
      scalarRelativeEntropy (m p) (a p+δ*e p)) =
      (fun p => regularizedEntropy (m p) (e p) δ (entropyPath a r T p)-
        regularizedEntropy (m p) (e p) δ (a p)) := by
    funext p
    unfold regularizedEntropy
    ring
  calc
    _ = ∫ p : Phase, scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p)-
        scalarRelativeEntropy (m p) (a p+δ*e p) := (integral_sub hET hE0).symm
    _ = ∫ p : Phase, regularizedEntropy (m p) (e p) δ (entropyPath a r T p)-
        regularizedEntropy (m p) (e p) δ (a p) := congrArg (fun f : Phase → ℝ => ∫ p, f p) heq
    _ = _ := (integral_sub hAT hA0).trans h

end BoltzmannNonuniqueness

end

end

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

section

/-! # The real-valued hot-gain estimate for the approximation equations -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.HotApplication
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.HotRealGain

theorem quadratic_gain (hcarleman : Published.GPV2009CarlemanInput)
    {q : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∀ᵐ v : Velocity,
      Integrable (GainOrder.integrand (H q) v) ((volume : Measure Velocity).prod sphereArea) ∧
      ∀ x : Position, gain (fun p => H q p.2) x v ≤ realBound q * H q v := by
  filter_upwards [quadratic_gain_le_constant hcarleman hq₁ hq₂] with v hv
  exact ⟨GainNonnegative.integrable_of_bound (measurable_H q) (H_nonneg q) v hv,
    fun x => GainNonnegative.gain_le_of_bound (measurable_H q) (H_nonneg q)
      (mul_nonneg (realBound_pos q).le (H_nonneg q v)) v x hv⟩

end BoltzmannNonuniqueness.HotRealGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarriers
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HalfGaussianMoment
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Half-Gaussian velocity moments for the hot weight and cold cores -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.VelocityMoment

theorem weight_pos (v : Velocity) : 0 < weight v := Real.exp_pos _
theorem weight_one_le (v : Velocity) : 1 ≤ weight v := Real.one_le_exp (by positivity)

theorem weight_H_le (q : ℝ) (v : Velocity) :
    weight v*H q v ≤ gaussianMajorant (1/2) q v := by
  calc
    _ ≤ weight v*gaussianMajorant 1 q v :=
      mul_le_mul_of_nonneg_left (H_le_gaussianMajorant q v) (weight_pos v).le
    _ = _ := by
      unfold weight gaussianMajorant
      rw [← mul_assoc,← Real.exp_add]
      congr 2
      ring

theorem weight_H_integrable {q : ℝ} (hq : q < 2) :
    Integrable (fun v => weight v*H q v) := by
  apply (integrable_gaussianMajorant (by norm_num : (0:ℝ) < 1/2) hq).mono'
    (by unfold weight H singularity; fun_prop)
  filter_upwards [] with v
  rw [Real.norm_of_nonneg (mul_nonneg (weight_pos v).le (H_nonneg q v))]
  exact weight_H_le q v

theorem hotConstant_nonneg (q : ℝ) : 0 ≤ hotConstant q :=
  integral_nonneg (fun v => mul_nonneg (weight_pos v).le (H_nonneg q v))

theorem hot_moment {q a : ℝ} (hq : q < 2) (ha : 0 ≤ a) :
    moment (fun v => a*H q v) = ENNReal.ofReal (a*hotConstant q) := by
  have hi := (weight_H_integrable hq).const_mul a
  unfold moment hotConstant
  simp_rw [show ∀ v : Velocity, weight v*(a*H q v) = a*(weight v*H q v) by intro v; ring]
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_const_mul]
  · exact ae_of_all _ (fun v => mul_nonneg ha (mul_nonneg (weight_pos v).le (H_nonneg q v)))

end BoltzmannNonuniqueness.VelocityMoment

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityPolynomialBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Hard-sphere pair rates controlled by the half-Gaussian moment -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.VelocityMoment

theorem norm_le_weight (v : Velocity) : ‖v‖ ≤ weight v := by
  have he := Real.add_one_le_exp (‖v‖^2/2)
  change ‖v‖ ≤ Real.exp (‖v‖^2/2)
  nlinarith [sq_nonneg (‖v‖-1)]

theorem pair_weight_le (v w : Velocity) : 1+‖v‖+‖w‖ ≤ 3*weight v*weight w := by
  have h1 := weight_one_le v
  have h2 := weight_one_le w
  have ha : weight v ≤ weight v*weight w := le_mul_of_one_le_right (weight_pos v).le h2
  have hb : weight w ≤ weight v*weight w := le_mul_of_one_le_left (weight_pos w).le h1
  have hc : 1 ≤ weight v*weight w := (h1.trans ha)
  linarith [norm_le_weight v,norm_le_weight w]

theorem moment_tensor {f : Velocity → ℝ} (hfm : Measurable f) :
    (∫⁻ p : Velocity × Velocity, ENNReal.ofReal (weight p.1*f p.1)*
      ENNReal.ofReal (weight p.2*f p.2)) = moment f*moment f := by
  have hm : Measurable (fun v => ENNReal.ofReal (weight v*f v)) := by unfold weight; fun_prop
  rw [Measure.volume_eq_prod]
  exact MeasureTheory.lintegral_prod_mul hm.aemeasurable hm.aemeasurable

theorem pairMoment_le {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) :
    pairMoment f ≤ 3*moment f*moment f := by
  have hm : Measurable (fun p : Velocity × Velocity => ENNReal.ofReal (weight p.1*f p.1)*
      ENNReal.ofReal (weight p.2*f p.2)) := by unfold weight; fun_prop
  calc
    _ ≤ ∫⁻ p : Velocity × Velocity, (3:ℝ≥0∞)*(ENNReal.ofReal (weight p.1*f p.1)*
        ENNReal.ofReal (weight p.2*f p.2)) := by
      apply lintegral_mono
      intro p
      have he : (1+‖p.1‖+‖p.2‖)*f p.1*f p.2 ≤
          3*((weight p.1*f p.1)*(weight p.2*f p.2)) := by
        have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pair_weight_le p.1 p.2)
          (hf p.1)) (hf p.2)
        nlinarith [h]
      apply (ENNReal.ofReal_le_ofReal he).trans_eq
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),ENNReal.ofReal_mul
        (mul_nonneg (weight_pos p.1).le (hf p.1)),ENNReal.ofReal_ofNat]
    _ = 3*(moment f*moment f) := by rw [lintegral_const_mul _ hm,moment_tensor hfm]
    _ = _ := by ring

theorem pairMoment_le_square {f : Velocity → ℝ} {M : ℝ}
    (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) (hM : 0 ≤ M) (hb : moment f ≤ ENNReal.ofReal M) :
    pairMoment f ≤ ENNReal.ofReal (3*M^2) := by
  calc
    _ ≤ 3*moment f*moment f := pairMoment_le hfm hf
    _ ≤ 3*ENNReal.ofReal M*ENNReal.ofReal M := mul_le_mul' (mul_le_mul' le_rfl hb) hb
    _ = _ := by rw [pow_two,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),
      ENNReal.ofReal_mul hM,ENNReal.ofReal_ofNat]; ring

end BoltzmannNonuniqueness.VelocityMoment

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionWeakMarginals
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrable velocity majorants for hard-sphere pair densities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

theorem pairKernel_nonneg (q : ℝ) (p : Velocity × Velocity) : 0 ≤ pairKernel q p :=
  mul_nonneg (mul_nonneg (by positivity) (H_nonneg q p.1)) (H_nonneg q p.2)

theorem pairKernel_measurable (q : ℝ) : Measurable (pairKernel q) := by
  unfold pairKernel H singularity
  fun_prop

theorem pairKernel_integrable {q : ℝ} (hq : q < 2) : Integrable (pairKernel q) := by
  have hm : Measurable (H q) := by unfold H singularity; fun_prop
  have hh : VelocityMoment.moment (H q) = ENNReal.ofReal (VelocityMoment.hotConstant q) := by
    simpa only [one_mul] using VelocityMoment.hot_moment hq zero_le_one
  have hb := VelocityMoment.pairMoment_le_square hm (H_nonneg q)
    (VelocityMoment.hotConstant_nonneg q) hh.le
  refine ⟨(pairKernel_measurable q).aestronglyMeasurable,?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (pairKernel_nonneg q))).mpr
    (hb.trans_lt ENNReal.ofReal_lt_top)

variable {X : Type*} [MeasurableSpace X]

theorem pairDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (pairDensity f) := by unfold pairDensity; fun_prop

omit [MeasurableSpace X] in
theorem pairDensity_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : X × (Velocity × Velocity)) : 0 ≤ pairDensity f z :=
  mul_nonneg (mul_nonneg (by positivity) (hf _)) (hf _)

omit [MeasurableSpace X] in
theorem pairDensity_bound {q A : ℝ} (hA : 0 ≤ A) {f : X × Velocity → ℝ}
    (hf : ∀ z, 0 ≤ f z) (z : X × (Velocity × Velocity))
    (h₁ : f (z.1,z.2.1) ≤ A*H q z.2.1) (h₂ : f (z.1,z.2.2) ≤ A*H q z.2.2) :
    pairDensity f z ≤ A^2*pairKernel q z.2 := by
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left h₁
    (by positivity : 0 ≤ 1+‖z.2.1‖+‖z.2.2‖)) h₂ (hf _)
      (mul_nonneg (by positivity) (mul_nonneg hA (H_nonneg q _)))
  unfold pairDensity pairKernel
  nlinarith [hh]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Measure preservation and integrability for the full hard-sphere collision rate -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem scatterTriple_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (scatterTriple (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  let ν := μ.prod (volume : Measure (Velocity × Velocity))
  have hf (ω : Sphere) : MeasurePreserving
      (fun p : X × (Velocity × Velocity) => (p.1,scatterPair ω p.2)) ν ν := by
    have hω : ‖(ω : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
    have hh := (MeasurePreserving.id μ).prod (scatterPair_measurePreserving (ω : Velocity) hω)
    have he : (Prod.map id (scatterPair (ω : Velocity))) =
        (fun p : X × (Velocity × Velocity) => (p.1,scatterPair ω p.2)) := by
      funext p
      rfl
    rw [he] at hh
    simpa only [ν,Measure.volume_eq_prod] using hh
  have hm : Measurable (fun z : Sphere × (X × (Velocity × Velocity)) =>
      (z.2.1,scatterPair z.1 z.2.2)) := by
    unfold scatterPair scatterLeft scatterRight normalComponent
    fun_prop
  have hh := (MeasurePreserving.id sphereArea).skew_product (μc := ν) (μd := ν)
    (g := fun (ω : Sphere) (p : X × (Velocity × Velocity)) => (p.1,scatterPair ω p.2)) hm
    (ae_of_all _ (fun ω => (hf ω).map_eq))
  have h₁ : MeasurePreserving Prod.swap (ν.prod sphereArea) (sphereArea.prod ν) :=
    Measure.measurePreserving_swap
  have h₂ : MeasurePreserving Prod.swap (sphereArea.prod ν) (ν.prod sphereArea) :=
    Measure.measurePreserving_swap
  exact h₂.comp (hh.comp h₁)


omit [MeasurableSpace X] in
theorem postRate_formula (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    postRate f z = collisionKernel z.1.2.1 z.1.2.2 z.2*
      f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) := by
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  change collisionKernel (scatterLeft z.1.2.1 z.1.2.2 z.2) (scatterRight z.1.2.1 z.1.2.2 z.2) z.2*
    f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) = _
  rw [collisionKernel_scatter _ _ _ hw]

theorem preRate_measurable {f : X × Velocity → ℝ} (hf : Measurable f) : Measurable (preRate f) := by
  unfold preRate collisionKernel normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem preRate_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : (X × (Velocity × Velocity)) × Sphere) : 0 ≤ preRate f z :=
  mul_nonneg (mul_nonneg (collisionKernel_nonneg _ _ _) (hf _)) (hf _)

omit [MeasurableSpace X] in
theorem preRate_le_pairDensity {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : (X × (Velocity × Velocity)) × Sphere) : preRate f z ≤ pairDensity f z.1 := by
  have hk : collisionKernel z.1.2.1 z.1.2.2 z.2 ≤ 1+‖z.1.2.1‖+‖z.1.2.2‖ :=
    (collisionKernel_le_norm _ _ _).trans ((norm_sub_le _ _).trans (by linarith))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (hf _)) (hf _)

theorem preRate_integrable {μ : Measure X} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (preRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  apply (hpair.comp_fst sphereArea).mono' (preRate_measurable hfm).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (preRate_nonneg hf z)]
  exact preRate_le_pairDensity hf z

theorem postRate_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (postRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (scatterTriple_measurePreserving μ).integrable_comp_of_integrable (preRate_integrable hfm hf hpair)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable physical gain and loss and their equal total mass -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_r77726a_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
theorem collisionGrouping_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (collisionGrouping (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) := by
  have ha := (measurePreserving_prodAssoc μ (volume : Measure Velocity) (volume : Measure Velocity)).symm.prod
    (MeasurePreserving.id sphereArea)
  have hb := measurePreserving_prodAssoc (μ.prod (volume : Measure Velocity))
    (volume : Measure Velocity) sphereArea
  have he : (⇑(collisionGrouping (X := X))) =
      MeasurableEquiv.prodAssoc ∘ Prod.map (MeasurableEquiv.prodAssoc.symm)
        (id : Sphere → Sphere) := by
    funext z
    rfl
  rw [he]
  simpa only [Measure.volume_eq_prod] using hb.comp ha

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusTransport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Free transport and its measure-preserving characteristic coordinates on the torus -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

theorem flight_measurePreserving (t : ℝ) :
    MeasurePreserving (flight t) (volume : Measure Phase) volume := by
  have hm : Measurable (Function.uncurry (fun (v : Velocity) (x : Position) =>
      x+torusProjection (t • v))) := by
    unfold Function.uncurry torusProjection
    fun_prop
  have hskew := (MeasurePreserving.id (volume : Measure Velocity)).skew_product hm
    (ae_of_all _ (fun v => (measurePreserving_add_right (volume : Measure Position)
      (torusProjection (t • v))).map_eq))
  have he : flight t = Prod.swap ∘ (fun z : Velocity × Position =>
      (z.1,z.2+torusProjection (t • z.1))) ∘ Prod.swap := rfl
  rw [he,Measure.volume_eq_prod]
  exact (Measure.measurePreserving_swap (μ := (volume : Measure Velocity)) (ν := volume)).comp
    (hskew.comp Measure.measurePreserving_swap)

theorem along_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving (fun z : ℝ × Phase => (z.1,flight z.1 z.2))
      (μ.prod volume) (μ.prod volume) :=
  (MeasurePreserving.id μ).skew_product (g := fun t p => flight t p) measurable_flight
    (ae_of_all _ (fun t => (flight_measurePreserving t).map_eq))

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Integrals in characteristic coordinates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

theorem integral_flight (f : Phase → ℝ) (t : ℝ) :
    (∫ p, f (flight t p)) = ∫ p, f p :=
  (flight_measurePreserving t).integral_comp (flightEquiv t).measurableEmbedding f

end BoltzmannNonuniqueness.TorusFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CutoffLossFrequency
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The cutoff collision terms are dominated by the physical collision marginals -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_4 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem cutoffLossDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (cutoffLossDensity b f) := by
  have hk : Measurable (fun z : (X × Velocity) × (Velocity × Sphere) =>
      CollisionCutoff.kernel b z.1.2 z.2.1 z.2.2) := by
    unfold CollisionCutoff.kernel
    exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (by unfold collisionKernel normalComponent; fun_prop) measurable_const
  have hm : Measurable (fun z : (X × Velocity) × (Velocity × Sphere) =>
      CollisionCutoff.kernel b z.1.2 z.2.1 z.2.2*f z.1*f (z.1.1,z.2.1)) := by
    exact (hk.mul (hf.comp measurable_fst)).mul
      (hf.comp (measurable_fst.fst.prodMk measurable_snd.fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace X] in
theorem cutoffLossDensity_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (b : ℝ) (p : X × Velocity) : 0 ≤ cutoffLossDensity b f p :=
  integral_nonneg (fun _q => mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg b _ _ _)
    (hf _)) (hf _))

omit [MeasurableSpace X] in
theorem cutoffGainDensity_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (b : ℝ) (p : X × Velocity) : 0 ≤ KineticCollisionNullSets.gain b f p :=
  integral_nonneg (fun _q => mul_nonneg (mul_nonneg (CollisionCutoff.kernel_nonneg b _ _ _)
    (hf _)) (hf _))

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Identification of the cutoff loss marginal with collision frequency -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_5 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem integral_cutoffKernel (b : ℝ) (v w : Velocity) :
    (∫ ω : Sphere, CollisionCutoff.kernel b v w ω ∂sphereArea) =
      2*Real.pi*CollisionCutoff.rate b v w := by
  unfold CollisionCutoff.kernel CollisionCutoff.rate
  by_cases h : ‖v-w‖ < b
  · simp only [ite_eq_left h,integral_collisionKernel_sphereArea]
  · simp only [ite_eq_right h,integral_zero,mul_zero]

omit [MeasurableSpace X] in
theorem cutoffLossDensity_eq_frequency (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity)
    (hi : Integrable (fun q : Velocity × Sphere =>
      CollisionCutoff.kernel b p.2 q.1 q.2*f p*f (p.1,q.1))
      ((volume : Measure Velocity).prod sphereArea)) :
    cutoffLossDensity b f p = f p*KineticCollisionNullSets.frequency b f p := by
  unfold cutoffLossDensity
  rw [integral_prod _ hi]
  simp_rw [integral_mul_const,integral_cutoffKernel]
  calc
    _ = ∫ w : Velocity, (f p*(2*Real.pi))*(CollisionCutoff.rate b p.2 w*f (p.1,w)) := by
      apply integral_congr_ae
      filter_upwards [] with w
      ring
    _ = _ := by
      rw [integral_const_mul]
      unfold KineticCollisionNullSets.frequency CollisionCutoff.frequency
      ring

theorem cutoff_loss_ae_eq_frequency {μ : Measure X} [SFinite μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) (b : ℝ) :
    cutoffLossDensity b f =ᵐ[μ.prod (volume : Measure Velocity)]
      fun p => f p*KineticCollisionNullSets.frequency b f p := by
  have hl : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => preRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (preRate_integrable hfm hf hpair)
  filter_upwards [hl.prod_right_ae] with p hp
  apply cutoffLossDensity_eq_frequency
  have hS : MeasurableSet {q : Velocity × Sphere | ‖p.2-q.1‖ < b} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hi := hp.indicator hS
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext q
  by_cases h : ‖p.2-q.1‖ < b
  · rw [Set.indicator_of_mem (show q ∈ {q : Velocity × Sphere | ‖p.2-q.1‖ < b} from h)]
    simp only [CollisionCutoff.kernel,ite_eq_left h]
    rfl
  · rw [Set.indicator_of_notMem (show q ∉ {q : Velocity × Sphere | ‖p.2-q.1‖ < b} from h)]
    simp only [CollisionCutoff.kernel,ite_eq_right h,zero_mul]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionDissipation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The moving relative-speed cutoff has the full collision limit -/

noncomputable section

open MeasureTheory Filter Set

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_6_r77726a_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
theorem truncatedPreRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) (b : ℝ) :
    Measurable (truncatedPreRate b f) :=
  (preRate_measurable hfm).indicator (measurableSet_lt (by fun_prop) measurable_const)

theorem truncatedPostRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) (b : ℝ) :
    Measurable (truncatedPostRate b f) :=
  ((preRate_measurable hfm).comp scatterTriple_measurable).indicator
    (measurableSet_lt (by fun_prop) measurable_const)

theorem cutoffGain_eq_marginal (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) :
    KineticCollisionNullSets.gain b f p = ∫ q : Velocity × Sphere,
      truncatedPostRate b f (collisionGrouping.symm (p,q)) ∂volume.prod sphereArea := by
  apply integral_congr_ae
  filter_upwards [] with q
  change CollisionCutoff.kernel b p.2 q.1 q.2 * f (p.1,scatterLeft p.2 q.1 q.2) *
    f (p.1,scatterRight p.2 q.1 q.2) =
    if ‖p.2-q.1‖ < b then postRate f ((p.1,(p.2,q.1)),q.2) else 0
  rw [postRate_formula]
  by_cases hq : ‖p.2-q.1‖ < b <;> simp [CollisionCutoff.kernel,hq]

theorem cutoffLoss_eq_marginal (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) :
    cutoffLossDensity b f p = ∫ q : Velocity × Sphere,
      truncatedPreRate b f (collisionGrouping.symm (p,q)) ∂volume.prod sphereArea := by
  apply integral_congr_ae
  filter_upwards [] with q
  change CollisionCutoff.kernel b p.2 q.1 q.2*f p*f (p.1,q.1) =
    if ‖p.2-q.1‖ < b then preRate f ((p.1,(p.2,q.1)),q.2) else 0
  by_cases hq : ‖p.2-q.1‖ < b <;> simp [CollisionCutoff.kernel,preRate,hq]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Particle interchange and elastic substitution for the cutoff collision rate -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem particleSwap_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (particleSwap (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := ((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap
      (μ := (volume : Measure Velocity)) (ν := (volume : Measure Velocity)))).prod
      (MeasurePreserving.id sphereArea)
  have he : (⇑(particleSwap (X := X))) = Prod.map (Prod.map id Prod.swap) id := by
    funext z
    rfl
  rw [he]
  simpa only [Measure.volume_eq_prod] using h

theorem preRate_particleSwap (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : preRate f (particleSwap z) = preRate f z := by
  have hk : collisionKernel z.1.2.2 z.1.2.1 z.2 = collisionKernel z.1.2.1 z.1.2.2 z.2 := by
    unfold collisionKernel normalComponent
    rw [show z.1.2.2-z.1.2.1 = -(z.1.2.1-z.1.2.2) by abel,inner_neg_left,abs_neg]
  change collisionKernel z.1.2.2 z.1.2.1 z.2*f (z.1.1,z.1.2.2)*f (z.1.1,z.1.2.1) = _
  rw [hk]
  unfold preRate
  ring

theorem truncatedPreRate_particleSwap (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    truncatedPreRate b f (particleSwap z) = truncatedPreRate b f z := by
  change (if ‖z.1.2.2-z.1.2.1‖ < b then preRate f (particleSwap z) else 0) =
    (if ‖z.1.2.1-z.1.2.2‖ < b then preRate f z else 0)
  rw [norm_sub_rev,preRate_particleSwap]

omit [MeasurableSpace X] in
theorem truncatedPreRate_scatter (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    truncatedPreRate b f (scatterTriple z) = truncatedPostRate b f z := by
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  change (if ‖scatterLeft z.1.2.1 z.1.2.2 z.2-scatterRight z.1.2.1 z.1.2.2 z.2‖ < b
    then preRate f (scatterTriple z) else 0) = _
  rw [scatter_relative_speed _ _ _ hw]
  rfl

omit [MeasurableSpace X] in
theorem truncatedPostRate_scatter (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    truncatedPostRate b f (scatterTriple z) = truncatedPreRate b f z := by
  rw [← truncatedPreRate_scatter,scatterTriple_involutive]

theorem integral_preRate_particleSwap (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)
  simp only [truncatedPreRate_particleSwap] at h
  exact h.symm

theorem integral_postRate_scatter (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
  simp only [truncatedPostRate_scatter] at h
  exact h.symm

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The gain rate and particle interchange -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem scatterLeft_swap (v w ω : Velocity) : scatterLeft w v ω = scatterRight v w ω := by
  have hn : normalComponent w v ω = -normalComponent v w ω := by
    unfold normalComponent
    rw [show w-v = -(v-w) by abel,inner_neg_left]
  simp only [scatterLeft,scatterRight,hn,neg_smul,sub_neg_eq_add]

theorem scatterRight_swap (v w ω : Velocity) : scatterRight w v ω = scatterLeft v w ω := by
  exact (scatterLeft_swap w v ω).symm

namespace CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem scatterTriple_particleSwap (z : (X × (Velocity × Velocity)) × Sphere) :
    scatterTriple (particleSwap z) = particleSwap (scatterTriple z) := by
  change ((z.1.1,(scatterLeft z.1.2.2 z.1.2.1 z.2,scatterRight z.1.2.2 z.1.2.1 z.2)),z.2) =
    ((z.1.1,(scatterRight z.1.2.1 z.1.2.2 z.2,scatterLeft z.1.2.1 z.1.2.2 z.2)),z.2)
  exact congrArg (fun p : Velocity × Velocity => ((z.1.1,p),z.2))
    (Prod.ext (scatterLeft_swap z.1.2.1 z.1.2.2 z.2)
      (scatterRight_swap z.1.2.1 z.1.2.2 z.2))

theorem postRate_particleSwap (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : postRate f (particleSwap z) = postRate f z := by
  change preRate f (scatterTriple (particleSwap z)) = preRate f (scatterTriple z)
  rw [scatterTriple_particleSwap,preRate_particleSwap]

theorem truncatedPostRate_particleSwap (b : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    truncatedPostRate b f (particleSwap z) = truncatedPostRate b f z := by
  change (if ‖z.1.2.2-z.1.2.1‖ < b then postRate f (particleSwap z) else 0) =
    (if ‖z.1.2.1-z.1.2.2‖ < b then postRate f z else 0)
  rw [norm_sub_rev,postRate_particleSwap]

theorem integral_postRate_particleSwap (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
  simp only [truncatedPostRate_particleSwap] at h
  exact h.symm

theorem integral_postRate_scatter_right (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.2)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.2)*truncatedPostRate b f z)
  simp only [truncatedPostRate_scatter] at h
  exact h.symm

end CollisionCompactness
end BoltzmannNonuniqueness

end

end

section

/-! # The symmetric weak collision identity with the invariant speed cutoff -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem cutoff_weak_identity {μ : Measure X} [SFinite μ] (b : ℝ) (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) -
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    (1/2:ℝ) * ∫ z, collisionJump ψ z*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  have hr : Integrable (fun z => ψ (z.1.1,z.1.2.2)*truncatedPreRate b f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpre
    simp only [Function.comp_def,truncatedPreRate_particleSwap] at h
    exact h
  have hrpost : Integrable (fun z => ψ (z.1.1,z.1.2.2)*truncatedPostRate b f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,truncatedPostRate_particleSwap] at h
    exact h
  have hl' : Integrable (fun z =>
      ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,truncatedPostRate_scatter] at h
    exact h
  have hr' : Integrable (fun z =>
      ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hrpost
    simp only [Function.comp_def,truncatedPostRate_scatter] at h
    exact h
  have he : (fun z => collisionJump ψ z*truncatedPreRate b f z) =
      (fun z => ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z)+
      (fun z => ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z)-
      (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)-
      (fun z => ψ (z.1.1,z.1.2.2)*truncatedPreRate b f z) := by
    funext z
    dsimp [collisionJump]
    ring
  rw [he,integral_sub' ((hl'.add hr').sub hpre) hr,
    integral_sub' (hl'.add hr') hpre,integral_add' hl' hr']
  rw [← integral_postRate_scatter,← integral_postRate_scatter_right,
    ← integral_postRate_particleSwap,← integral_preRate_particleSwap]
  ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Passing collision tests between rates and the physical gain/loss marginals -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_8 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem collision_test_marginal {μ : Measure X} [SFinite μ]
    (r : (X × (Velocity × Velocity)) × Sphere → ℝ) (ψ : X × Velocity → ℝ)
    (hi : Integrable (fun z => ψ (z.1.1,z.1.2.1)*r z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (fun p => ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
      ∂(volume : Measure Velocity).prod sphereArea)) (μ.prod volume) ∧
    (∫ p, ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
      ∂(volume : Measure Velocity).prod sphereArea) ∂μ.prod volume) =
      ∫ z, ψ (z.1.1,z.1.2.1)*r z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have hg := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable hi
  have he : (fun p : X × Velocity => ∫ q : Velocity × Sphere,
      ψ p*r (collisionGrouping.symm (p,q)) ∂(volume : Measure Velocity).prod sphereArea) =
      (fun p => ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
        ∂(volume : Measure Velocity).prod sphereArea)) := by
    funext p
    exact integral_const_mul _ _
  have hgroup : Integrable (fun y : (X × Velocity) × (Velocity × Sphere) =>
      ψ y.1*r (collisionGrouping.symm y))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) := hg
  constructor
  · have h := hgroup.integral_prod_left
    rw [he] at h
    exact h
  · calc
      _ = ∫ p, ∫ q : Velocity × Sphere, ψ p*r (collisionGrouping.symm (p,q))
          ∂(volume : Measure Velocity).prod sphereArea ∂μ.prod volume := by rw [he]
      _ = ∫ y : (X × Velocity) × (Velocity × Sphere), ψ y.1*r (collisionGrouping.symm y)
          ∂(μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea) :=
        (integral_prod _ hgroup).symm
      _ = _ := (collisionGrouping_measurePreserving μ).symm.integral_comp
        collisionGrouping.symm.measurableEmbedding (fun z => ψ (z.1.1,z.1.2.1)*r z)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Recovering weighted collision-rate integrability from a nonnegative marginal -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_9 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

theorem collision_test_integrable_of_marginal {μ : Measure X} [SFinite μ]
    {r : (X × (Velocity × Velocity)) × Sphere → ℝ} (hrm : Measurable r)
    (hrn : ∀ z, 0 ≤ r z)
    (hri : Integrable r ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    {ψ : X × Velocity → ℝ} (hψm : Measurable ψ)
    (hψi : Integrable (fun p => ψ p*(∫ q : Velocity × Sphere,
      r (collisionGrouping.symm (p,q)) ∂(volume : Measure Velocity).prod sphereArea)) (μ.prod volume)) :
    Integrable (fun z => ψ (z.1.1,z.1.2.1)*r z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  let s : (X × Velocity) × (Velocity × Sphere) → ℝ := fun z => r (collisionGrouping.symm z)
  have hsm : Measurable s := hrm.comp collisionGrouping.symm.measurable
  have hsi : Integrable s ((μ.prod (volume : Measure Velocity)).prod
      ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable hri
  have hweighted : Integrable (fun z => ψ z.1*s z) ((μ.prod (volume : Measure Velocity)).prod
      ((volume : Measure Velocity).prod sphereArea)) := by
    apply (integrable_prod_iff ((hψm.comp measurable_fst).mul hsm).aestronglyMeasurable).mpr
    refine ⟨?_,?_⟩
    · filter_upwards [hsi.prod_right_ae] with p hp
      exact hp.const_mul (ψ p)
    · apply hψi.norm.congr
      filter_upwards [] with p
      have hn : 0 ≤ ∫ q : Velocity × Sphere, s (p,q) ∂(volume : Measure Velocity).prod sphereArea :=
        integral_nonneg (fun q => hrn _)
      change |ψ p*(∫ q : Velocity × Sphere, s (p,q) ∂(volume : Measure Velocity).prod sphereArea)| =
        ∫ q : Velocity × Sphere, |ψ p*s (p,q)| ∂(volume : Measure Velocity).prod sphereArea
      rw [abs_mul,abs_of_nonneg hn]
      calc
        _ = ∫ q : Velocity × Sphere, |ψ p| * s (p,q)
            ∂(volume : Measure Velocity).prod sphereArea := (integral_const_mul _ _).symm
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [] with q
          rw [abs_mul,abs_of_nonneg (hrn _)]

  exact (collisionGrouping_measurePreserving μ).integrable_comp_of_integrable hweighted

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Maxwellian and density logarithms under collision symmetry -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

namespace CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem collisionJump_scatter (ψ : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump ψ (scatterTriple z) = -collisionJump ψ z := by
  have hi := scatterTriple_involutive (X := X) z
  have hl := congrArg (fun p => p.1.2.1) hi
  have hr := congrArg (fun p => p.1.2.2) hi
  change scatterLeft (scatterLeft z.1.2.1 z.1.2.2 z.2)
    (scatterRight z.1.2.1 z.1.2.2 z.2) z.2 = z.1.2.1 at hl
  change scatterRight (scatterLeft z.1.2.1 z.1.2.2 z.2)
    (scatterRight z.1.2.1 z.1.2.2 z.2) z.2 = z.1.2.2 at hr
  change ψ (z.1.1,scatterLeft (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2)+
    ψ (z.1.1,scatterRight (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2)-
    ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)-
    ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) = _
  rw [hl,hr]
  unfold collisionJump
  ring

end CollisionCompactness
end BoltzmannNonuniqueness

end

end

section

/-! # Symmetric collision production and its entropy sign -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem integral_jump_post (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, collisionJump ψ z*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    -(∫ z, collisionJump ψ z*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => collisionJump ψ z*truncatedPostRate b f z)
  simp only [collisionJump_scatter,truncatedPostRate_scatter,neg_mul,integral_neg] at h
  exact h.symm

theorem collisionJump_integrable {μ : Measure X} [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (fun z => collisionJump ψ z*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    Integrable (fun z => collisionJump ψ z*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hr : Integrable (fun z => ψ (z.1.1,z.1.2.2)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpre
    simp only [Function.comp_def,truncatedPreRate_particleSwap] at h
    exact h
  have hrpost : Integrable (fun z => ψ (z.1.1,z.1.2.2)*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,truncatedPostRate_particleSwap] at h
    exact h
  have hl' : Integrable (fun z =>
      ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,truncatedPostRate_scatter] at h
    exact h
  have hr' : Integrable (fun z =>
      ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hrpost
    simp only [Function.comp_def,truncatedPostRate_scatter] at h
    exact h
  have hp : Integrable (fun z => collisionJump ψ z*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := ((hl'.add hr').sub hpre).sub hr
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    dsimp [collisionJump]
    ring
  refine ⟨hp,?_⟩
  have ht := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hp
  simp only [Function.comp_def,collisionJump_scatter,truncatedPreRate_scatter,neg_mul] at ht
  convert ht.neg using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Pi.neg_apply,neg_neg]

theorem cutoff_production_identity {μ : Measure X} [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    :
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) -
    (∫ z, ψ (z.1.1,z.1.2.1)*truncatedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    -(1/4:ℝ) * ∫ z, collisionJump ψ z*(truncatedPostRate b f z-truncatedPreRate b f z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  obtain ⟨hjpre,hjpost⟩ := collisionJump_integrable b f ψ hpre hpost
  simp_rw [mul_sub]
  rw [integral_sub hjpost hjpre,integral_jump_post]
  have h := cutoff_weak_identity b f ψ hpre hpost
  linarith

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_GainSmoothingError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # One-sided gain differences for the nonlinear cold comparison -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GainUpperDifference

theorem integrand_bound {f g : Velocity → ℝ} {q A B D : ℝ} (hD : 0 ≤ D)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, f w - g w ≤ D * H q w) (v : Velocity) (p : Velocity × Sphere) :
    GainOrder.integrand f v p - GainOrder.integrand g v p ≤
      (D * (A + B)) * GainOrder.integrand (H q) v p := by
  let l := scatterLeft v p.1 p.2
  let r := scatterRight v p.1 p.2
  have h1 : (f l - g l) * f r ≤ (D * H q l) * (A * H q r) :=
    (mul_le_mul_of_nonneg_right (hfg l) (hf r)).trans
      (mul_le_mul_of_nonneg_left (hfB r) (mul_nonneg hD (H_nonneg q l)))
  have h2 : g l * (f r - g r) ≤ (B * H q l) * (D * H q r) :=
    (mul_le_mul_of_nonneg_left (hfg r) (hg l)).trans
      (mul_le_mul_of_nonneg_right (hgB l) (mul_nonneg hD (H_nonneg q r)))
  have he : GainOrder.integrand f v p - GainOrder.integrand g v p =
      collisionKernel v p.1 p.2 * ((f l - g l) * f r + g l * (f r - g r)) := by
    unfold GainOrder.integrand l r
    ring
  rw [he]
  calc
    _ ≤ collisionKernel v p.1 p.2 *
        ((D * H q l) * (A * H q r) + (B * H q l) * (D * H q r)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (collisionKernel_nonneg _ _ _)
    _ = _ := by unfold GainOrder.integrand l r; ring

theorem cutoff_integrand_bound {f g : Velocity → ℝ} {q A B D : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, f w - g w ≤ D * H q w) (b : ℝ) (v : Velocity) (p : Velocity × Sphere) :
    CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b g v p ≤
      (D * (A + B)) * GainOrder.integrand (H q) v p := by
  by_cases hp : ‖v - p.1‖ < b
  · simpa only [CollisionCutoff.integrand, CollisionCutoff.kernel, GainOrder.integrand, ite_eq_left hp] using
      integrand_bound hD hf hg hfB hgB hfg v p
  · simp only [CollisionCutoff.integrand, CollisionCutoff.kernel, ite_eq_right hp, zero_mul, sub_self]
    exact mul_nonneg (mul_nonneg hD (add_nonneg hA hB)) (GainOrder.integrand_nonneg (H_nonneg q) v p)

/-- Only the positive difference of the two densities enters the upper gain difference. -/
theorem cutoff_gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {q A B D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, f w - g w ≤ D * H q w) (b : ℝ) :
    ∀ᵐ v : Velocity,
      CollisionCutoff.gain b f v - CollisionCutoff.gain b g v ≤
        (D * (A + B) * HotApplication.realBound q) * H q v := by
  filter_upwards [HotRealGain.quadratic_gain hcarleman hq₁ hq₂] with v hv
  have hfi := GainOrder.integrable_of_le hfm hf hfB v (GainOrder.integrable_const_mul A v hv.1)
  have hgi := GainOrder.integrable_of_le hgm hg hgB v (GainOrder.integrable_const_mul B v hv.1)
  have hfc := CollisionCutoff.integrable_gain b hfm hf v hfi
  have hgc := CollisionCutoff.integrable_gain b hgm hg v hgi
  calc
    _ = ∫ p, CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b g v p
        ∂((volume : Measure Velocity).prod sphereArea) := (integral_sub hfc hgc).symm
    _ ≤ ∫ p, (D * (A + B)) * GainOrder.integrand (H q) v p
        ∂((volume : Measure Velocity).prod sphereArea) :=
      integral_mono (hfc.sub hgc) (hv.1.const_mul _)
        (cutoff_integrand_bound hA hB hD hf hg hfB hgB hfg b v)
    _ = (D * (A + B)) * gain (fun p => H q p.2) 0 v := integral_const_mul _ _
    _ ≤ (D * (A + B)) * (HotApplication.realBound q * H q v) :=
      mul_le_mul_of_nonneg_left (hv.2 0) (mul_nonneg hD (add_nonneg hA hB))
    _ = _ := by ring

end BoltzmannNonuniqueness.GainUpperDifference

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

theorem gain_difference (hcarleman : Published.GPV2009CarlemanInput)
    {q A B D : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) (b : ℝ) :
    ∀ᵐ v : Velocity, |CollisionCutoff.gain b f v - CollisionCutoff.gain b g v| ≤
      (D * (A + B) * HotApplication.realBound q) * H q v := by
  have hforward := GainUpperDifference.cutoff_gain_bound hcarleman hq₁ hq₂ hA hB hD
    hfm hgm hf hg hfB hgB (fun w => (le_abs_self _).trans (hfg w)) b
  have hbackward := GainUpperDifference.cutoff_gain_bound hcarleman hq₁ hq₂ hB hA hD
    hgm hfm hg hf hgB hfB (fun w => (le_abs_self _).trans (by simpa only [abs_sub_comm] using hfg w)) b
  filter_upwards [hforward, hbackward] with v hv hv'
  rw [add_comm B A] at hv'
  exact abs_le.mpr ⟨by linarith, hv⟩

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

theorem frequency_difference {q A B D b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) (v : Velocity) :
    |CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v| ≤ D * frequencyConstant q b := by
  have hfi := integrable_dominated hq hfm hf hfB
  have hgi := integrable_dominated hq hgm hg hgB
  have he : CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v =
      CollisionCutoff.frequency b (fun w => f w - g w) v := by
    unfold CollisionCutoff.frequency
    rw [← mul_sub, ← integral_sub (CollisionCutoff.integrable_frequency hb hfi v)
      (CollisionCutoff.integrable_frequency hb hgi v)]
    congr 2
    funext w
    ring
  rw [he]
  calc
    _ ≤ 2 * Real.pi * b * ∫ w, |f w - g w| :=
      CollisionCutoff.abs_frequency_le hb (hfi.sub hgi) v
    _ ≤ 2 * Real.pi * b * ∫ w, D * H q w := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono (hfi.sub hgi).abs ((integrable_H hq).const_mul D) hfg
    _ = _ := by rw [integral_const_mul]; unfold frequencyConstant; ring

theorem loss_difference {q A B D b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) (v : Velocity) :
    |f v * CollisionCutoff.frequency b f v - g v * CollisionCutoff.frequency b g v| ≤
      (D * (A + B) * frequencyConstant q b) * H q v := by
  have hνf := frequency_nonneg hf b v
  have hνB := frequency_bound hq hb hfm hf hfB v
  have hνD := frequency_difference hq hb hfm hgm hf hg hfB hgB hfg v
  calc
    _ = |(f v - g v) * CollisionCutoff.frequency b f v +
        g v * (CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v)| := by congr 1; ring
    _ ≤ |f v - g v| * CollisionCutoff.frequency b f v +
        g v * |CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v| := by
      simpa only [abs_mul, abs_of_nonneg hνf, abs_of_nonneg (hg v)] using abs_add_le
        ((f v - g v) * CollisionCutoff.frequency b f v)
        (g v * (CollisionCutoff.frequency b f v - CollisionCutoff.frequency b g v))
    _ ≤ (D * H q v) * (A * frequencyConstant q b) + (B * H q v) * (D * frequencyConstant q b) :=
      add_le_add (mul_le_mul (hfg v) hνB hνf (mul_nonneg hD (H_nonneg q v)))
        (mul_le_mul (hgB v) hνD (abs_nonneg _) (mul_nonneg hB (H_nonneg q v)))
    _ = _ := by ring

/-- The local difference constant for the actual cutoff collision field. -/
theorem collision_difference (hcarleman : Published.GPV2009CarlemanInput)
    {q A B D b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) :
    ∀ᵐ v : Velocity, |collision b f v - collision b g v| ≤
      (D * (A + B) * (HotApplication.realBound q + frequencyConstant q b)) * H q v := by
  filter_upwards [gain_difference hcarleman hq₁ hq₂ hA hB hD hfm hgm hf hg hfB hgB hfg b]
    with v hv
  have hl := loss_difference hq₂ hb hB hD hfm hgm hf hg hfB hgB hfg v
  calc
    _ = |(CollisionCutoff.gain b f v - CollisionCutoff.gain b g v) -
        (f v * CollisionCutoff.frequency b f v - g v * CollisionCutoff.frequency b g v)| := by
      unfold collision
      congr 1
      ring
    _ ≤ |CollisionCutoff.gain b f v - CollisionCutoff.gain b g v| +
        |f v * CollisionCutoff.frequency b f v - g v * CollisionCutoff.frequency b g v| := abs_sub _ _
    _ ≤ _ := by nlinarith only [hv, hl]

end BoltzmannNonuniqueness.CutoffLipschitz

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_RegularizedCollisionDifference
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The cutoff collision error of positive Gaussian regularization -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetBarrierCollision

namespace BoltzmannNonuniqueness

theorem gaussianRegularization_measurable (δ : ℝ) {f : Velocity → ℝ} (hf : Measurable f) :
    Measurable (gaussianRegularization δ f) := by
  unfold gaussianRegularization
  fun_prop

theorem gaussianRegularization_bound {δ A q : ℝ} (_hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    {f : Velocity → ℝ} (hf : ∀ v, f v ≤ A*H q v) (v : Velocity) :
    gaussianRegularization δ f v ≤ (A+tiltConstant)*H q v := by
  have he := JetGaussianEscape.gaussian_le_hot q v
  have hle : δ*Real.exp (-2*‖v‖^2) ≤ tiltConstant*H q v :=
    (mul_le_mul_of_nonneg_right hδone (Real.exp_nonneg _)).trans (by simpa using he)
  unfold gaussianRegularization
  nlinarith only [hf v,hle]

theorem gaussianRegularization_collision_error (hcarleman : Published.GPV2009CarlemanInput)
    {δ A q b : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hA : 0 ≤ A)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b)
    {f : Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ v, 0 ≤ f v)
    (hfb : ∀ v, f v ≤ A*H q v) :
    ∀ᵐ v : Velocity,
      |CutoffLipschitz.collision b (gaussianRegularization δ f) v-CutoffLipschitz.collision b f v| ≤
        δ*(tiltConstant*(2*A+tiltConstant)*
          (HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b))*H q v := by
  have hn : ∀ v, 0 ≤ gaussianRegularization δ f v :=
    fun v => add_nonneg (hfn v) (mul_nonneg hδ (Real.exp_nonneg _))
  have hd : ∀ v, |gaussianRegularization δ f v-f v| ≤ (δ*tiltConstant)*H q v := by
    intro v
    have he := mul_le_mul_of_nonneg_left (JetGaussianEscape.gaussian_le_hot q v) hδ
    simpa only [gaussianRegularization,add_sub_cancel_left,
      abs_of_nonneg (mul_nonneg hδ (Real.exp_nonneg _)),mul_assoc] using he
  have ht := CutoffLipschitz.collision_difference hcarleman hq₁ hq₂ hb
    (add_nonneg hA tiltConstant_pos.le) hA (mul_nonneg hδ tiltConstant_pos.le)
    (gaussianRegularization_measurable δ hfm) hfm hn hfn
    (gaussianRegularization_bound hδ hδone hfb) hfb hd
  filter_upwards [ht] with v hv
  convert hv using 1
  all_goals try with_reducible_and_instances rfl
  ring

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionSources
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform integrability of the actual cutoff equation's right-hand side -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem collisionSource_measurable {f : X × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (collisionSource b f) :=
  (KineticCollisionNullSets.measurable_gain hf b).sub
    (hf.mul (KineticCollisionNullSets.measurable_frequency hf b))

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyDissipationAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The integrable entropy error caused by positive regularization -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem entropyErrorCoefficient_nonneg {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b) (q : ℝ) :
    0 ≤ entropyErrorCoefficient q A b := by
  unfold entropyErrorCoefficient
  exact mul_nonneg (mul_nonneg tiltConstant_pos.le (by linarith [tiltConstant_pos]))
    (add_nonneg (HotApplication.realBound_pos q).le (CutoffLipschitz.frequencyConstant_nonneg hb q))

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticEntropyErrorLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrable entropy tests for bounded kinetic densities -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem kinetic_log_product_integrable {μ : Measure X} [IsFiniteMeasure μ]
    {q B C δ : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hB : 0 ≤ B) (hC : 0 ≤ C) (hδ : 0 < δ)
    {u a : X × Velocity → ℝ} (hum : Measurable u) (ham : Measurable a)
    (hl : ∀ p, δ*Real.exp (-2*‖p.2‖^2) ≤ u p)
    (hu : ∀ p, u p ≤ B*H q p.2)
    (ha : ∀ᵐ p ∂μ.prod (volume : Measure Velocity), |a p| ≤ C*H q p.2) :
    Integrable (fun p => Real.log (u p/maxwellian p.2)*a p) (μ.prod volume) := by
  obtain ⟨p,hp,hpi⟩ := exists_integrable_rpow_H hq₁ hq₂
  have hmaj := ((logarithmicMajorant_integrable (B := B) (δ := δ) hq₂ hpi).const_mul C).comp_snd μ
  have hMm : Measurable (fun p : X × Velocity => maxwellian p.2) := by
    unfold maxwellian
    fun_prop
  apply hmaj.mono' (((hum.div hMm).log).mul ham).aestronglyMeasurable
  filter_upwards [ha] with z hz
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul]
  calc
    _ ≤ |Real.log (u z/maxwellian z.2)| * (C*H q z.2) :=
      mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    _ = C*(|Real.log (u z/maxwellian z.2)| * H q z.2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (logarithm_weight_bound hB hp hδ z.2 (hl z) (hu z)) hC

end BoltzmannNonuniqueness

end

end

section

/-! # A quantitative integral bound for the kinetic logarithmic test -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem kinetic_log_integral_bound {μ : Measure X} [IsFiniteMeasure μ]
    {q B C δ p : ℝ} (hq : q < 2) (hB : 0 ≤ B) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {u a : X × Velocity → ℝ}
    (hl : ∀ z, δ*Real.exp (-2*‖z.2‖^2) ≤ u z) (hu : ∀ z, u z ≤ B*H q z.2)
    (ha : ∀ᵐ z ∂μ.prod (volume : Measure Velocity), |a z| ≤ C*H q z.2) :
    |∫ z, Real.log (u z/maxwellian z.2)*a z ∂μ.prod volume| ≤
      C*∫ z : X × Velocity, logarithmicMajorant q B p δ z.2 ∂μ.prod volume := by
  have hi := ((logarithmicMajorant_integrable (B := B) (δ := δ) hq hpi).const_mul C).comp_snd μ
  have hb : ∀ᵐ z ∂μ.prod (volume : Measure Velocity),
      ‖Real.log (u z/maxwellian z.2)*a z‖ ≤ C*logarithmicMajorant q B p δ z.2 := by
    filter_upwards [ha] with z hz
    rw [Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ |Real.log (u z/maxwellian z.2)| * (C*H q z.2) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = C*(|Real.log (u z/maxwellian z.2)| * H q z.2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (logarithm_weight_bound hB hp hδ z.2 (hl z) (hu z)) hC
  have h := norm_integral_le_of_norm_le hi hb
  simpa only [Real.norm_eq_abs,integral_const_mul] using h

end BoltzmannNonuniqueness

end

end

section

/-! # The Gaussian entropy error is integrable on a finite kinetic base -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem gaussianRegularizedDensity_measurable (δ : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (gaussianRegularizedDensity δ f) := by
  unfold gaussianRegularizedDensity
  fun_prop

theorem kinetic_regularization_error_bound (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [SFinite μ] {δ A q b : ℝ}
    (hδ : 0 ≤ δ) (hδone : δ ≤ 1) (hA : 0 ≤ A)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hfb : ∀ p, f p ≤ A*H q p.2) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      |CollisionCompactness.collisionSource b (gaussianRegularizedDensity δ f) p-
        CollisionCompactness.collisionSource b f p| ≤
          (δ*entropyErrorCoefficient q A b)*H q p.2 := by
  have hgm := gaussianRegularizedDensity_measurable δ hfm
  have hsm := (CollisionCompactness.collisionSource_measurable hgm b).sub
    (CollisionCompactness.collisionSource_measurable hfm b)
  have hH : Measurable (fun p : X × Velocity => (δ*entropyErrorCoefficient q A b)*H q p.2) := by
    unfold H singularity transverse
    fun_prop
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hsm.abs hH)).mpr
  filter_upwards [] with x
  have hx := gaussianRegularization_collision_error hcarleman hδ hδone hA hq₁ hq₂ hb
    (hfm.comp (measurable_const.prodMk measurable_id)) (fun v => hfn (x,v)) (fun v => hfb (x,v))
  exact hx

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedEntropyProduction
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Collision bounds for a finite approximation under its hot majorant -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem bounded_pair_integrable {μ : Measure X} [IsFiniteMeasure μ]
    {q A : ℝ} (hq : q < 2) (hA : 0 ≤ A) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ A*H q p.2) :
    Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity))) := by
  have hi := ((pairKernel_integrable hq).const_mul (A^2)).comp_snd μ
  apply hi.mono' (pairDensity_measurable hfm).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (pairDensity_nonneg hfn z)]
  exact pairDensity_bound hA hfn z (hfb _) (hfb _)

theorem bounded_cutoff_gain (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [SFinite μ] {q A : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hfb : ∀ p, f p ≤ A*H q p.2) (b : ℝ) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      KineticCollisionNullSets.gain b f p ≤ (A^2*HotApplication.realBound q)*H q p.2 := by
  have hH : Measurable (fun p : X × Velocity => (A^2*HotApplication.realBound q)*H q p.2) := by
    unfold H singularity transverse
    fun_prop
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le (KineticCollisionNullSets.measurable_gain hfm b) hH)).mpr
  filter_upwards [] with x
  have h := GainUpperDifference.cutoff_gain_bound hcarleman hq₁ hq₂ hA (le_refl (0:ℝ)) hA
    (hfm.comp (measurable_const.prodMk measurable_id)) measurable_const
    (fun v => hfn (x,v)) (fun _ => le_refl (0:ℝ)) (fun v => hfb (x,v))
    (fun v => by simp) (fun v => by simpa using hfb (x,v)) b
  filter_upwards [h] with v hv
  have hz : CollisionCutoff.gain b (fun _ : Velocity => 0) v = 0 := by
    simp [CollisionCutoff.gain,CollisionCutoff.integrand]
  rw [hz,sub_zero,add_zero] at hv
  simpa only [pow_two,Function.comp_def,id_eq,KineticCollisionNullSets.gain] using hv

theorem bounded_cutoff_loss {μ : Measure X} [IsFiniteMeasure μ]
    {q A b : ℝ} (hq : q < 2) (hA : 0 ≤ A) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hfb : ∀ p, f p ≤ A*H q p.2) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      cutoffLossDensity b f p ≤ (A^2*CutoffLipschitz.frequencyConstant q b)*H q p.2 := by
  have hp := bounded_pair_integrable (μ := μ) hq hA hfm hfn hfb
  filter_upwards [cutoff_loss_ae_eq_frequency hfm hfn hp b] with p he
  rw [he]
  have hν := CutoffLipschitz.frequency_bound hq hb
    (hfm.comp (measurable_const.prodMk measurable_id)) (fun v => hfn (p.1,v))
    (fun v => hfb (p.1,v)) p.2
  have hn := CutoffLipschitz.frequency_nonneg (fun v => hfn (p.1,v)) b p.2
  have hu := mul_le_mul (hfb p) hν hn (mul_nonneg hA (H_nonneg q p.2))
  convert hu using 1
  all_goals first | rfl | ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Entropy production for a positive bounded finite approximation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem bounded_log_gainLoss_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A B δ b : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ) (hb : 0 ≤ b)
    {f u : X × Velocity → ℝ} (hfm : Measurable f) (hum : Measurable u)
    (hfn : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ A*H q p.2)
    (hul : ∀ p, δ*Real.exp (-2*‖p.2‖^2) ≤ u p) (hub : ∀ p, u p ≤ B*H q p.2) :
    Integrable (fun p => Real.log (u p/maxwellian p.2)*KineticCollisionNullSets.gain b f p)
      (μ.prod volume) ∧
    Integrable (fun p => Real.log (u p/maxwellian p.2)*cutoffLossDensity b f p) (μ.prod volume) := by
  constructor
  · apply kinetic_log_product_integrable hq₁ hq₂ hB
      (mul_nonneg (sq_nonneg A) (HotApplication.realBound_pos q).le) hδ hum
      (KineticCollisionNullSets.measurable_gain hfm b) hul hub
    filter_upwards [bounded_cutoff_gain hcarleman hq₁ hq₂ hA hfm hfn hfb b] with p hp
    simpa only [abs_of_nonneg (cutoffGainDensity_nonneg hfn b p)] using hp
  · apply kinetic_log_product_integrable hq₁ hq₂ hB
      (mul_nonneg (sq_nonneg A) (CutoffLipschitz.frequencyConstant_nonneg hb q)) hδ hum
      (cutoffLossDensity_measurable hfm b) hul hub
    filter_upwards [bounded_cutoff_loss hq₂ hA hb hfm hfn hfb] with p hp
    simpa only [abs_of_nonneg (cutoffLossDensity_nonneg hfn b p)] using hp

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_RegularizedEntropyIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The finite-approximation entropy-production inequality, with vanishing error -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem bounded_log_source_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A B δ b : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ) (hb : 0 ≤ b)
    {f u : X × Velocity → ℝ} (hfm : Measurable f) (hum : Measurable u)
    (hfn : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ A*H q z.2)
    (hul : ∀ z, δ*Real.exp (-2*‖z.2‖^2) ≤ u z) (hub : ∀ z, u z ≤ B*H q z.2) :
    Integrable (fun z => Real.log (u z/maxwellian z.2)*collisionSource b f z) (μ.prod volume) := by
  have hpair := bounded_pair_integrable (μ := μ) hq₂ hA hfm hfn hfb
  have ht := bounded_log_gainLoss_integrable (μ := μ) hcarleman hq₁ hq₂ hA hB hδ hb
    hfm hum hfn hfb hul hub
  have hl : Integrable (fun z => Real.log (u z/maxwellian z.2)*
      (f z*KineticCollisionNullSets.frequency b f z)) (μ.prod volume) := by
    apply ht.2.congr
    filter_upwards [cutoff_loss_ae_eq_frequency hfm hfn hpair b] with z hz
    rw [hz]
  convert ht.1.sub hl using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [collisionSource,Pi.sub_apply]
  ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Finite relative entropy of a Gaussian-regularized bounded approximation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem regularized_relative_entropy_integrable {μ : Measure X} [IsFiniteMeasure μ]
    {q A δ : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hδ : 0 < δ) (hδone : δ ≤ 1)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hfb : ∀ z, f z ≤ A*H q z.2) :
    Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (gaussianRegularizedDensity δ f z))
      (μ.prod volume) := by
  let g := gaussianRegularizedDensity δ f
  have hgm : Measurable g := gaussianRegularizedDensity_measurable δ hfm
  have hgn : ∀ z, 0 ≤ g z := fun z => add_nonneg (hfn z) (mul_nonneg hδ.le (Real.exp_nonneg _))
  have hgb : ∀ z, g z ≤ (A+tiltConstant)*H q z.2 := fun z =>
    gaussianRegularization_bound hδ.le hδone (fun v => hfb (z.1,v)) z.2
  have hgl : ∀ z, δ*Real.exp (-2*‖z.2‖^2) ≤ g z := by
    intro z
    dsimp [g,gaussianRegularizedDensity]
    linarith [hfn z]
  have hgint : Integrable g (μ.prod (volume : Measure Velocity)) := by
    apply (((integrable_H hq₂).const_mul (A+tiltConstant)).comp_snd μ).mono' hgm.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (hgn z)]
    exact hgb z
  have hlog := kinetic_log_product_integrable (μ := μ) hq₁ hq₂
    (add_nonneg hA tiltConstant_pos.le) (add_nonneg hA tiltConstant_pos.le) hδ hgm hgm hgl hgb
    (Filter.Eventually.of_forall (fun z => by rw [abs_of_nonneg (hgn z)]; exact hgb z))
  have hM := integrable_maxwellian.comp_snd μ
  convert (hlog.sub hgint).add hM using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  rw [scalarRelativeEntropy_eq (maxwellian_pos z.2)]
  simp only [Pi.add_apply,Pi.sub_apply,g]
  ring

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalEntropyProduction
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The regularized entropy estimate in physical time-phase coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem physical_regularized_entropy_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {T q A δ b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    {F : Evolution} (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p) (hFb : ∀ t p, F t p ≤ A*H q p.2) :
    Integrable (fun z : ℝ × Phase =>
      Real.log ((F z.1 z.2+δ*Real.exp (-2*‖z.2.2‖^2))/maxwellian z.2.2)*cutoffPhysicalSource b F z)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  let g := kineticDensity F
  have hgm : Measurable g := hFm.comp MeasurableEquiv.prodAssoc.measurable
  have hgn : ∀ z, 0 ≤ g z := fun z => hFn _ _
  have hgb : ∀ z, g z ≤ A*H q z.2 := fun z => hFb _ _
  have hum := gaussianRegularizedDensity_measurable δ hgm
  have hul : ∀ z, δ*Real.exp (-2*‖z.2‖^2) ≤ gaussianRegularizedDensity δ g z := by
    intro z
    dsimp [gaussianRegularizedDensity]
    linarith [hgn z]
  have hub : ∀ z, gaussianRegularizedDensity δ g z ≤ (A+tiltConstant)*H q z.2 := fun z =>
    gaussianRegularization_bound hδ.le hδone (fun v => hgb (z.1,v)) z.2
  have hi := CollisionCompactness.bounded_log_source_integrable
    (μ := AnnularEnvelope.timePositionVolume T) hcarleman hq₁ hq₂ hA
    (add_nonneg hA tiltConstant_pos.le) hδ hb hgm hum hgn hgb hul hub
  exact (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable hi

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedCollisionBlocks
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrability of the finite cutoff source in Eulerian and characteristic coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

namespace CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem bounded_cutoff_source_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A b : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hfb : ∀ z, f z ≤ A*H q z.2) : Integrable (collisionSource b f) (μ.prod volume) := by
  have hgain : Integrable (KineticCollisionNullSets.gain b f) (μ.prod (volume : Measure Velocity)) := by
    apply (((integrable_H hq₂).const_mul (A^2*HotApplication.realBound q)).comp_snd μ).mono'
      (KineticCollisionNullSets.measurable_gain hfm b).aestronglyMeasurable
    filter_upwards [bounded_cutoff_gain hcarleman hq₁ hq₂ hA hfm hfn hfb b] with z hz
    rw [Real.norm_of_nonneg (cutoffGainDensity_nonneg hfn b z)]
    exact hz
  have hloss : Integrable (cutoffLossDensity b f) (μ.prod (volume : Measure Velocity)) := by
    apply (((integrable_H hq₂).const_mul (A^2*CutoffLipschitz.frequencyConstant q b)).comp_snd μ).mono'
      (cutoffLossDensity_measurable hfm b).aestronglyMeasurable
    filter_upwards [bounded_cutoff_loss hq₂ hA hb hfm hfn hfb] with z hz
    rw [Real.norm_of_nonneg (cutoffLossDensity_nonneg hfn b z)]
    exact hz
  have hpair := bounded_pair_integrable (μ := μ) hq₂ hA hfm hfn hfb
  apply (hgain.sub hloss).congr
  filter_upwards [cutoff_loss_ae_eq_frequency hfm hfn hpair b] with z hz
  change KineticCollisionNullSets.gain b f z-cutoffLossDensity b f z = _
  rw [hz]
  rfl

end CollisionCompactness

theorem cutoffPhysicalSource_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {T q A b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hb : 0 ≤ b)
    {F : Evolution} (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p) (hFb : ∀ t p, F t p ≤ A*H q p.2) :
    Integrable (cutoffPhysicalSource b F) ((volume.restrict (Icc 0 T)).prod volume) := by
  have h := CollisionCompactness.bounded_cutoff_source_integrable
    (μ := AnnularEnvelope.timePositionVolume T) (f := kineticDensity F) hcarleman hq₁ hq₂ hA hb
    (hFm.comp MeasurableEquiv.prodAssoc.measurable) (fun z => hFn _ _) (fun z => hFb _ _)
  exact (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable h

theorem cutoffCharacteristicSource_integrable (hcarleman : Published.GPV2009CarlemanInput)
    {T q A b : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hb : 0 ≤ b)
    {F : Evolution} (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p) (hFb : ∀ t p, F t p ≤ A*H q p.2) :
    Integrable (TorusFlight.along (cutoffPhysicalSource b F))
      ((volume.restrict (Icc 0 T)).prod volume) :=
  (TorusFlight.along_measurePreserving _).integrable_comp_of_integrable
    (cutoffPhysicalSource_integrable hcarleman hq₁ hq₂ hA hb hFm hFn hFb)

end BoltzmannNonuniqueness

end

end

section

/-! # The regularized entropy balance for a bounded mild cutoff solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem regularizedRelativeEntropyDensity_integrable {q A δ : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hδ : 0 < δ) (hδone : δ ≤ 1)
    {f : Density} (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ A*H q p.2) :
    Integrable (regularizedRelativeEntropyDensity δ f) := by
  rw [Measure.volume_eq_prod]
  exact regularized_relative_entropy_integrable hq₁ hq₂ hA hδ hδone hfm hfn hfb

theorem bounded_mild_entropy_balance (hcarleman : Published.GPV2009CarlemanInput)
    {T q A δ b : ℝ} (hT : 0 < T) (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    {F : Evolution} {a : Density}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p) (hFb : ∀ t p, F t p ≤ A*H q p.2)
    (ham : Measurable a) (han : ∀ p, 0 ≤ a p) (hab : ∀ p, a p ≤ A*H q p.2)
    (hchar : (fun z : ℝ × Phase => F z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
        (fun z => entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) z.1 z.2))
    (hcharT : (fun p => F T (TorusFlight.flight T p)) =ᵐ[volume]
      entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) T) :
    (∫ p, regularizedRelativeEntropyDensity δ (F T) p)-
      (∫ p, regularizedRelativeEntropyDensity δ a p) =
      ∫ z : ℝ × Phase, Real.log ((F z.1 z.2+δ*Real.exp (-2*‖z.2.2‖^2))/maxwellian z.2.2)*
        cutoffPhysicalSource b F z ∂(volume.restrict (Icc 0 T)).prod volume := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let r := TorusFlight.along (cutoffPhysicalSource b F)
  let m : Phase → ℝ := fun p => maxwellian p.2
  let e : Phase → ℝ := fun p => Real.exp (-2*‖p.2‖^2)
  let R : Phase → ℝ := fun p => A*H q p.2
  have hri : Integrable r (μ.prod volume) :=
    cutoffCharacteristicSource_integrable hcarleman hq₁ hq₂ hA hb hFm hFn hFb
  have hbounds : ∀ᵐ p : Phase, ∀ᵐ t ∂μ, entropyPath a r t p ∈ Icc 0 (R p) := by
    have hs := (Measure.measurePreserving_swap (μ := (volume : Measure Phase)) (ν := μ)).quasiMeasurePreserving.ae hchar
    filter_upwards [Measure.ae_ae_of_ae_prod hs] with p hp
    filter_upwards [hp] with t ht
    change F t (TorusFlight.flight t p) = entropyPath a r t p at ht
    rw [← ht]
    exact ⟨hFn _ _,hFb _ _⟩
  have hET' := regularizedRelativeEntropyDensity_integrable hq₁ hq₂ hA hδ hδone
    (hFm.comp (measurable_const.prodMk measurable_id)) (hFn T) (hFb T)
  have hET : Integrable (fun p => scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p)) := by
    have h := (TorusFlight.flight_measurePreserving T).integrable_comp_of_integrable hET'
    apply h.congr
    filter_upwards [hcharT] with p hp
    change scalarRelativeEntropy (maxwellian p.2) (F T (TorusFlight.flight T p)+δ*e p) = _
    rw [hp]
  have hE0 : Integrable (fun p => scalarRelativeEntropy (m p) (a p+δ*e p)) :=
    regularizedRelativeEntropyDensity_integrable hq₁ hq₂ hA hδ hδone ham han hab
  have hbase : Integrable (fun p => scalarRelativeEntropy (m p) (δ*e p)) := by
    have h := regularizedRelativeEntropyDensity_integrable hq₁ hq₂ (le_refl (0:ℝ)) hδ hδone
      (f := fun _ => 0) measurable_const (fun _ => le_refl _) (fun p => by simp)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp only [regularizedRelativeEntropyDensity,m,e,zero_add]
  let L : ℝ × Phase → ℝ := fun z =>
    Real.log ((F z.1 z.2+δ*Real.exp (-2*‖z.2.2‖^2))/maxwellian z.2.2)*cutoffPhysicalSource b F z
  have hL : Integrable L (μ.prod volume) :=
    physical_regularized_entropy_integrable hcarleman hq₁ hq₂ hA hδ hδone hb hFm hFn hFb
  have hLi : Integrable (fun z : ℝ × Phase =>
      Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z) (μ.prod volume) := by
    have h := (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hL
    apply h.congr
    filter_upwards [hchar] with z hz
    change Real.log ((F z.1 (TorusFlight.flight z.1 z.2)+δ*e z.2)/m z.2)*r z = _
    rw [hz]
  have hbal := scalar_entropy_integral_balance hT hδ a m e R r
    (fun p => maxwellian_pos p.2) (fun p => Real.exp_pos _) (fun p => mul_nonneg hA (H_nonneg q p.2))
    hri hbounds hET hE0 hbase integrable_maxwellian_phase hLi
  have hend : (∫ p, scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p)) =
      ∫ p, regularizedRelativeEntropyDensity δ (F T) p := by
    calc
      _ = ∫ p, regularizedRelativeEntropyDensity δ (F T) (TorusFlight.flight T p) := by
        apply integral_congr_ae
        filter_upwards [hcharT] with p hp
        change scalarRelativeEntropy (m p) (entropyPath a r T p+δ*e p) =
          scalarRelativeEntropy (m p) (F T (TorusFlight.flight T p)+δ*e p)
        rw [hp]
      _ = _ := TorusFlight.integral_flight _ T
  have hrhs : (∫ z : ℝ × Phase, Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z ∂μ.prod volume) =
      ∫ z, L z ∂μ.prod volume := by
    calc
      _ = ∫ z, TorusFlight.along L z ∂μ.prod volume := by
        apply integral_congr_ae
        filter_upwards [hchar] with z hz
        change Real.log ((entropyPath a r z.1 z.2+δ*e z.2)/m z.2)*r z =
          Real.log ((F z.1 (TorusFlight.flight z.1 z.2)+δ*e z.2)/m z.2)*r z
        rw [hz]
      _ = _ := by
        have hAlong : Integrable (TorusFlight.along L) (μ.prod volume) :=
          (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hL
        rw [integral_prod _ hAlong,integral_prod _ hL]
        apply integral_congr_ae
        filter_upwards [] with t
        exact TorusFlight.integral_flight (fun p => L (t,p)) t
  rw [hend,hrhs] at hbal
  exact hbal

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveComparisonBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Exact entropy dissipation for positive bounded cutoff densities -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem cutoff_relative_entropy_identity {μ : Measure X} [SFinite μ] (b : ℝ)
    (f : X × Velocity → ℝ)
    (hpre : Integrable (fun z => Real.log (f (z.1.1,z.1.2.1)/maxwellian z.1.2.1)*
      truncatedPreRate b f z) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => Real.log (f (z.1.1,z.1.2.1)/maxwellian z.1.2.1)*
      truncatedPostRate b f z) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ p, Real.log (f p/maxwellian p.2)*KineticCollisionNullSets.gain b f p ∂μ.prod volume)-
      (∫ p, Real.log (f p/maxwellian p.2)*cutoffLossDensity b f p ∂μ.prod volume) =
      -(∫ z, positiveCutoffProduction b f z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hp := (collision_test_marginal (truncatedPostRate b f)
    (fun p => Real.log (f p/maxwellian p.2)) hpost).2
  have hl := (collision_test_marginal (truncatedPreRate b f)
    (fun p => Real.log (f p/maxwellian p.2)) hpre).2
  simp only [← cutoffGain_eq_marginal] at hp
  simp only [← cutoffLoss_eq_marginal] at hl
  rw [hp,hl,cutoff_production_identity b f (fun p => Real.log (f p/maxwellian p.2)) hpre hpost]
  simp only [positiveCutoffProduction,mul_assoc,integral_const_mul]
  ring

theorem bounded_positive_entropy_identity (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A δ b : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hδ : 0 < δ) (hb : 0 ≤ b)
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hfl : ∀ p, δ*Real.exp (-2*‖p.2‖^2) ≤ f p) (hfb : ∀ p, f p ≤ A*H q p.2) :
    Integrable (positiveCutoffProduction b f)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    (∫ p, Real.log (f p/maxwellian p.2)*collisionSource b f p ∂μ.prod volume) =
      -(∫ z, positiveCutoffProduction b f z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hfn : ∀ p, 0 ≤ f p := fun p => (mul_pos hδ (Real.exp_pos _)).le.trans (hfl p)
  have hpair := bounded_pair_integrable (μ := μ) hq₂ hA hfm hfn hfb
  have hgL := bounded_log_gainLoss_integrable (μ := μ) hcarleman hq₁ hq₂ hA hA hδ hb hfm hfm hfn hfb hfl hfb
  have hlog : Measurable (fun p : X × Velocity => Real.log (f p/maxwellian p.2)) := by
    have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
    exact (hfm.div hm).log
  have hS : MeasurableSet {z : (X × (Velocity × Velocity)) × Sphere | ‖z.1.2.1-z.1.2.2‖ < b} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hprei := (preRate_integrable hfm hfn hpair).indicator hS
  have hposti := (postRate_integrable hfm hfn hpair).indicator hS
  have hpren : ∀ z, 0 ≤ truncatedPreRate b f z := fun z =>
    Set.indicator_nonneg (fun z _ => preRate_nonneg hfn z) z
  have hpostn : ∀ z, 0 ≤ truncatedPostRate b f z := fun z =>
    Set.indicator_nonneg (fun z _ => preRate_nonneg hfn (scatterTriple z)) z
  have hpre := collision_test_integrable_of_marginal (truncatedPreRate_measurable hfm b)
    hpren hprei hlog (by simpa only [← cutoffLoss_eq_marginal] using hgL.2)
  have hpost := collision_test_integrable_of_marginal (truncatedPostRate_measurable hfm b)
    hpostn hposti hlog (by simpa only [← cutoffGain_eq_marginal] using hgL.1)
  obtain ⟨hjpre,hjpost⟩ := collisionJump_integrable b f (fun p => Real.log (f p/maxwellian p.2)) hpre hpost
  constructor
  · convert (hjpost.sub hjpre).const_mul (1/4:ℝ) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    simp only [positiveCutoffProduction,Pi.sub_apply]
    ring
  · have hloss := cutoff_loss_ae_eq_frequency hfm hfn hpair b
    have hLi : Integrable (fun p => Real.log (f p/maxwellian p.2)*
        (f p*KineticCollisionNullSets.frequency b f p)) (μ.prod volume) := by
      apply hgL.2.congr
      filter_upwards [hloss] with p hp
      rw [hp]
    calc
      _ = (∫ p, Real.log (f p/maxwellian p.2)*KineticCollisionNullSets.gain b f p ∂μ.prod volume)-
          (∫ p, Real.log (f p/maxwellian p.2)*cutoffLossDensity b f p ∂μ.prod volume) := by
        simp_rw [collisionSource,mul_sub]
        rw [integral_sub hgL.1 hLi]
        congr 1
        apply integral_congr_ae
        filter_upwards [hloss] with p hp
        rw [hp]
      _ = _ := cutoff_relative_entropy_identity b f hpre hpost

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_RegularizedDissipationBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Retaining dissipation in the Gaussian regularization estimate -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem regularized_entropy_dissipation_bound (hcarleman : Published.GPV2009CarlemanInput)
    {μ : Measure X} [IsFiniteMeasure μ] {q A δ b p : ℝ}
    (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A) (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hfn : ∀ z, 0 ≤ f z) (hfb : ∀ z, f z ≤ A*H q z.2) :
    Integrable (positiveCutoffProduction b (gaussianRegularizedDensity δ f))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    (∫ z, Real.log (gaussianRegularizedDensity δ f z/maxwellian z.2)*collisionSource b f z
        ∂μ.prod volume) +
      (∫ z, positiveCutoffProduction b (gaussianRegularizedDensity δ f) z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
      (δ*entropyErrorCoefficient q A b)*∫ z : X × Velocity,
        logarithmicMajorant q (A+tiltConstant) p δ z.2 ∂μ.prod volume := by
  let u := gaussianRegularizedDensity δ f
  have hum : Measurable u := gaussianRegularizedDensity_measurable δ hfm
  have huB : ∀ z, u z ≤ (A+tiltConstant)*H q z.2 := fun z =>
    gaussianRegularization_bound hδ.le hδone (fun v => hfb (z.1,v)) z.2
  have huL : ∀ z, δ*Real.exp (-2*‖z.2‖^2) ≤ u z := by
    intro z
    dsimp [u,gaussianRegularizedDensity]
    linarith [hfn z]
  have hun : ∀ z, 0 ≤ u z := fun z => (mul_nonneg hδ.le (Real.exp_nonneg _)).trans (huL z)
  have hAB := add_nonneg hA tiltConstant_pos.le
  have hfi := bounded_log_source_integrable (μ := μ) hcarleman hq₁ hq₂ hA hAB hδ hb
    hfm hum hfn hfb huL huB
  have hui := bounded_log_source_integrable (μ := μ) hcarleman hq₁ hq₂ hAB hAB hδ hb
    hum hum hun huB huL huB
  have hidentity := bounded_positive_entropy_identity (μ := μ) hcarleman hq₁ hq₂ hAB hδ hb hum huL huB
  have hbnd := kinetic_log_integral_bound hq₂ hAB
    (mul_nonneg hδ.le (entropyErrorCoefficient_nonneg hA hb q)) hδ hp hpi huL huB
    (kinetic_regularization_error_bound (μ := μ) hcarleman hδ.le hδone hA hq₁ hq₂ hb hfm hfn hfb)
  have he : (∫ z, Real.log (u z/maxwellian z.2)*(collisionSource b u z-collisionSource b f z)
      ∂μ.prod volume) =
      (∫ z, Real.log (u z/maxwellian z.2)*collisionSource b u z ∂μ.prod volume)-
      (∫ z, Real.log (u z/maxwellian z.2)*collisionSource b f z ∂μ.prod volume) := by
    simp_rw [mul_sub]
    exact integral_sub hui hfi
  rw [he,hidentity.2] at hbnd
  refine ⟨hidentity.1,?_⟩
  linarith [neg_abs_le (-(∫ z, positiveCutoffProduction b u z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)-
      (∫ z, Real.log (u z/maxwellian z.2)*collisionSource b f z ∂μ.prod volume))]

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalDissipationBridge
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The regularized entropy-dissipation estimate in time-phase coordinates -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem physical_regularized_entropy_dissipation_bound (hcarleman : Published.GPV2009CarlemanInput)
    {T q A δ b p : ℝ} (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {F : Evolution} (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t z, 0 ≤ F t z) (hFb : ∀ t z, F t z ≤ A*H q z.2) :
    (∫ z : ℝ × Phase,
      Real.log ((F z.1 z.2+δ*Real.exp (-2*‖z.2.2‖^2))/maxwellian z.2.2)*cutoffPhysicalSource b F z
      ∂(volume.restrict (Icc 0 T)).prod volume) + regularizedKineticDissipation T b δ F ≤
      (δ*entropyErrorCoefficient q A b)*∫ z : (ℝ × Position) × Velocity,
        logarithmicMajorant q (A+tiltConstant) p δ z.2
        ∂(AnnularEnvelope.timePositionVolume T).prod volume := by
  have hbnd := (CollisionCompactness.regularized_entropy_dissipation_bound
    (μ := AnnularEnvelope.timePositionVolume T) hcarleman hq₁ hq₂ hA hδ hδone hb hp hpi
    (hFm.comp MeasurableEquiv.prodAssoc.measurable) (fun z => hFn _ _) (fun z => hFb _ _)).2
  have he := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integral_comp
    MeasurableEquiv.prodAssoc.symm.measurableEmbedding
    (fun z : (ℝ × Position) × Velocity =>
      Real.log (gaussianRegularizedDensity δ (kineticDensity F) z/maxwellian z.2)*
        CollisionCompactness.collisionSource b (kineticDensity F) z)
  exact (congrArg (fun x => x+regularizedKineticDissipation T b δ F) he).trans_le hbnd

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedMildEntropyLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Entropy with dissipation for a bounded mild cutoff solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem bounded_mild_entropy_dissipation_q80_oai (hcarleman : Published.GPV2009CarlemanInput)
    {T q A δ b p : ℝ} (hT : 0 < T) (hq₁ : 1 < q) (hq₂ : q < 2) (hA : 0 ≤ A)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hb : 0 ≤ b)
    (hp : 1 < p) (hpi : Integrable (fun v : Velocity => H q v^p))
    {F : Evolution} {a : Density}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t z, 0 ≤ F t z) (hFb : ∀ t z, F t z ≤ A*H q z.2)
    (ham : Measurable a) (han : ∀ z, 0 ≤ a z) (hab : ∀ z, a z ≤ A*H q z.2)
    (hchar : (fun z : ℝ × Phase => F z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
        (fun z => entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) z.1 z.2))
    (hcharT : (fun z => F T (TorusFlight.flight T z)) =ᵐ[volume]
      entropyPath a (TorusFlight.along (cutoffPhysicalSource b F)) T) :
    (∫ z, regularizedRelativeEntropyDensity δ (F T) z)-
      (∫ z, regularizedRelativeEntropyDensity δ a z)+regularizedKineticDissipation T b δ F ≤
      (δ*entropyErrorCoefficient q A b)*∫ z : (ℝ × Position) × Velocity,
        logarithmicMajorant q (A+tiltConstant) p δ z.2
        ∂(AnnularEnvelope.timePositionVolume T).prod volume := by
  have hbal := bounded_mild_entropy_balance hcarleman hT hq₁ hq₂ hA hδ hδone hb
    hFm hFn hFb ham han hab hchar hcharT
  have hprod := physical_regularized_entropy_dissipation_bound (T := T) hcarleman hq₁ hq₂ hA
    hδ hδone hb hp hpi hFm hFn hFb
  exact (congrArg (fun x => x+regularizedKineticDissipation T b δ F) hbal).trans_le hprod

end BoltzmannNonuniqueness

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_q80_oai := @OAI.BoltzmannNonuniqueness.bounded_mild_entropy_dissipation_q80_oai
