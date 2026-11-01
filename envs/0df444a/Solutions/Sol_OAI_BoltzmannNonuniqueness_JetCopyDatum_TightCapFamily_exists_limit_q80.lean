-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_limit_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:42:12.218394+00:00
-- url     : https://prove2.me/submissions/935c7794-db17-4a8b-b4ae-37fbcf1733d7

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_CompactCapFamily_weak_limit_moment_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_TightCapFamily_entropy_mild_limit_of_convergence_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_TightCapFamily_exists_mild_limit_with_traces_and_convergence_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_MildCollisionSolution_localAdmissible_q80

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

theorem H_nonneg (q : ℝ) (v : Velocity) : 0 ≤ H q v := by
  unfold H singularity
  positivity

end BoltzmannNonuniqueness.VelocityWeight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_TransverseAverage
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
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

end BoltzmannNonuniqueness.TransverseDisk

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DatumBounds
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

theorem scale_pow (s₀ η : ℝ) (j p : ℕ) :
    scale s₀ η j ^ p = s₀ ^ p * Real.exp (-((p : ℝ) * η) * j) := by
  rw [scale, mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

theorem log_scale {s₀ η : ℝ} (hs₀ : 0 < s₀) (j : ℕ) :
    Real.log (scale s₀ η j) = Real.log s₀ - (j : ℝ) * η := by
  rw [scale, Real.log_mul hs₀.ne' (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem abs_log_scale_le {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η) (j : ℕ) :
    |Real.log (scale s₀ η j)| ≤ |Real.log s₀| + (j : ℝ) * η := by
  rw [log_scale hs₀]
  calc
    |Real.log s₀ - (j : ℝ) * η| ≤ |Real.log s₀| + |(j : ℝ) * η| := abs_sub _ _
    _ = |Real.log s₀| + (j : ℝ) * η := by
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hη)]

/-- Polynomial factors in the index remain summable against every positive power of the
geometric scale. This is used with `p = 2` and index powers zero and one below. -/
theorem summable_scale_pow_mul_nat_pow (s₀ : ℝ) {η : ℝ} (hη : 0 < η)
    (p k : ℕ) (hp : 0 < p) :
    Summable (fun j : ℕ => scale s₀ η j ^ p * (j : ℝ) ^ k) := by
  have hrate : 0 < (p : ℝ) * η := mul_pos (by exact_mod_cast hp) hη
  have h := (Real.summable_pow_mul_exp_neg_nat_mul k hrate).mul_left (s₀ ^ p)
  apply h.congr
  intro j
  rw [scale_pow]
  ring

theorem summable_scale_pow (s₀ : ℝ) {η : ℝ} (hη : 0 < η)
    (p : ℕ) (hp : 0 < p) : Summable (fun j : ℕ => scale s₀ η j ^ p) := by
  simpa only [pow_zero, mul_one] using summable_scale_pow_mul_nat_pow s₀ hη p 0 hp

theorem summable_scale_sq (s₀ : ℝ) {η : ℝ} (hη : 0 < η) :
    Summable (fun j : ℕ => scale s₀ η j ^ 2) :=
  summable_scale_pow s₀ hη 2 (by norm_num)

/-- A positive scale power also absorbs the absolute logarithm; power four applies to the
vanishing hot-seed entropy estimate in the same datum lemma. -/
theorem summable_scale_pow_log {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (p : ℕ) (hp : 0 < p) :
    Summable (fun j : ℕ => scale s₀ η j ^ p * (1 + |Real.log (scale s₀ η j)|)) := by
  have hindex : Summable (fun j : ℕ => scale s₀ η j ^ p * (j : ℝ)) := by
    simpa only [pow_one] using summable_scale_pow_mul_nat_pow s₀ hη p 1 hp
  have hmajor := ((summable_scale_pow s₀ hη p hp).mul_right (1 + |Real.log s₀|)).add
    (hindex.mul_right η)
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hmajor
  · exact mul_nonneg (pow_nonneg (scale_pos (η := η) hs₀ j).le p) (by positivity)
  · have h := mul_le_mul_of_nonneg_left
      (add_le_add_left (abs_log_scale_le hs₀ hη.le j) 1)
      (pow_nonneg (scale_pos (η := η) hs₀ j).le p)
    nlinarith only [h]

theorem summable_entropyBound {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η) :
    Summable (entropyBound s₀ η) := by
  exact summable_scale_pow_log hs₀ hη 2 (by norm_num)

end BoltzmannNonuniqueness.DatumBounds

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetProfiles
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.instCountableLabel _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

theorem mask_subset_ball {η s : ℝ} (hη : 0 ≤ η) (a : Bool) :
    mask η s a ⊆ ball 0 (Real.exp η * s) := by
  intro y hy
  have hc : 0 ≤ gapCoefficient η := by
    unfold gapCoefficient
    have := Real.one_le_exp hη
    positivity
  have h := hy.1.2
  change ‖y‖ < Real.exp η * s - gapCoefficient η * s ^ 2 at h
  rw [mem_ball, dist_zero_right]
  exact h.trans_le (sub_le_self _ (mul_nonneg hc (sq_nonneg s)))

theorem mask_finite {η s : ℝ} (hη : 0 ≤ η) (a : Bool) : volume (mask η s a) < ∞ :=
  (measure_mono (mask_subset_ball (s := s) hη a)).trans_lt (measure_ball_lt_top ..)

theorem mask_area_le {η s : ℝ} (hη : 0 ≤ η) (hs : 0 ≤ s) (a : Bool) :
    volume.real (mask η s a) ≤ Real.pi * (Real.exp η * s) ^ 2 := by
  have h := measureReal_mono (μ := (volume : Measure Transverse)) (mask_subset_ball (s := s) hη a)
  rw [TransverseDisk.disk_volume_real 0 (mul_nonneg (Real.exp_pos η).le hs)] at h
  exact h

theorem mask_area_uniform {η s : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hs : 0 ≤ s) (a : Bool) : volume.real (mask η s a) ≤ 4 * Real.pi * s ^ 2 := by
  apply (mask_area_le hη hs a).trans
  have he : Real.exp η ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hηmax
  have hp := mul_le_mul_of_nonneg_right he hs
  have hsq : (Real.exp η * s) ^ 2 ≤ (2 * s) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hp
  nlinarith [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le]

theorem indicator_integrable {η s : ℝ} (hη : 0 ≤ η) (a : Bool) :
    Integrable ((mask η s a).indicator (fun _ => (1 : ℝ))) :=
  integrable_indicator_iff (measurableSet_mask η s a) |>.mpr
    (integrableOn_const (mask_finite hη a).ne)

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

theorem J_integrable : Integrable J := bump.integrable_normed

theorem J_integral : ∫ v, J v = 1 := bump.integral_normed

theorem J_support : Function.support J = ball 0 1 := bump.support_normed_eq

theorem J_zero {v : Velocity} (hv : 1 ≤ ‖v‖) : J v = 0 := by
  by_contra h
  have hs : v ∈ Function.support J := h
  rw [J_support, mem_ball, dist_zero_right] at hs
  exact not_lt_of_ge hv hs

theorem J_compact : HasCompactSupport J := bump.hasCompactSupport_normed

theorem bound_pos : 0 < bound := inv_pos.mpr bump.integral_pos

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

theorem integrable_scaled {f : Velocity → ℝ} (hf : Integrable f) {d : ℝ}
    (hd : 0 < d) (a : Velocity) : Integrable (scaled d a f) :=
  ((hf.comp_smul (inv_ne_zero hd.ne')).comp_sub_right a).const_mul _

theorem integral_scaled (f : Velocity → ℝ) {d : ℝ} (hd : 0 < d) (a : Velocity) :
    (∫ v, scaled d a f v) = ∫ v, f v := by
  unfold scaled
  rw [integral_const_mul]
  change (d ^ 3)⁻¹ * (∫ v, (fun w => f (d⁻¹ • w)) (v - a)) = _
  rw [integral_sub_right_eq_self (fun w => f (d⁻¹ • w)) a,
    Measure.integral_comp_inv_smul_of_nonneg volume f hd.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  field_simp

theorem density_nonneg {d : ℝ} (hd : 0 ≤ d) (a v : Velocity) : 0 ≤ density d a v :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hd _)) (J_nonneg _)

theorem density_integrable {d : ℝ} (hd : 0 < d) (a : Velocity) : Integrable (density d a) :=
  integrable_scaled J_integrable hd a

theorem density_mass {d : ℝ} (hd : 0 < d) (a : Velocity) : ∫ v, density d a v = 1 := by
  rw [density, integral_scaled J hd a, J_integral]

theorem density_zero {d : ℝ} (hd : 0 < d) (a v : Velocity) (hv : d ≤ ‖v - a‖) :
    density d a v = 0 := by
  have h : 1 ≤ ‖d⁻¹ • (v - a)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
    exact (one_le_inv_mul₀ hd).mpr hv
  simp only [density, scaled, J_zero h, mul_zero]

theorem density_velocity_bound {d : ℝ} (hd : 0 < d) {a v : Velocity}
    (hv : density d a v ≠ 0) : ‖v‖ < ‖a‖ + d := by
  have hdist : ‖v - a‖ < d := lt_of_not_ge (fun h => hv (density_zero hd a v h))
  have hnorm := norm_add_le (v - a) a
  rw [sub_add_cancel] at hnorm
  linarith

theorem integrable_J_entropy : Integrable (fun v => J v * |Real.log (J v)|) := by
  have hc : Continuous (fun v => |J v * Real.log (J v)|) :=
    (Real.continuous_mul_log.comp J_smooth.continuous).abs
  have hs : HasCompactSupport (fun v => |J v * Real.log (J v)|) := by
    apply J_compact.mono
    intro v hv
    by_contra hj
    have hz : J v = 0 := by simpa only [Function.mem_support, not_not] using hj
    simp only [Function.mem_support, hz, zero_mul, abs_zero, ne_eq, not_true_eq_false] at hv
  have hi : Integrable (fun v => |J v * Real.log (J v)|) :=
    hc.integrable_of_hasCompactSupport hs
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  rw [abs_mul, abs_of_nonneg (J_nonneg v)]

end BoltzmannNonuniqueness.JetThermalLaw

end

end

section

/-! # Absolute-entropy bounds under thermal scaling and translation -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetThermalKernel
open BoltzmannNonuniqueness.JetThermalLaw

namespace BoltzmannNonuniqueness.JetThermalEntropy

theorem entropy_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ entropy x :=
  mul_nonneg hx (abs_nonneg _)

theorem entropy_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    entropy (x * y) ≤ y * entropy x + x * entropy y := by
  obtain rfl | hx := hx.eq_or_lt
  · simp [entropy]
  obtain rfl | hy := hy.eq_or_lt
  · simp [entropy]
  have h := mul_le_mul_of_nonneg_left (abs_add_le (Real.log x) (Real.log y))
    (mul_nonneg hx.le hy.le)
  rw [← Real.log_mul hx.ne' hy.ne'] at h
  unfold entropy
  nlinarith only [h]

theorem continuous_entropy_comp {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) : Continuous (fun x => entropy (f x)) := by
  have he : (fun x => entropy (f x)) = fun x => |f x * Real.log (f x)| := by
    funext x
    simp only [entropy, abs_mul, abs_of_nonneg (hpos x)]
  rw [he]
  exact (Real.continuous_mul_log.comp hf).abs

/-- Pointwise bound with a constant independent of the profile center. -/
theorem density_entropy_bound {d : ℝ} (hd : 0 < d) (a v : Velocity) :
    entropy (density d a v) ≤ (3 * |Real.log d|) * density d a v +
      scaled d a (fun w => entropy (J w)) v := by
  have he := entropy_mul_le (inv_nonneg.mpr (pow_nonneg hd.le 3)) (J_nonneg (d⁻¹ • (v - a)))
  have hlog : |Real.log ((d ^ 3)⁻¹)| = 3 * |Real.log d| := by
    rw [Real.log_inv, Real.log_pow, abs_neg, abs_mul]
    norm_num
  unfold density scaled
  unfold entropy at he
  rw [hlog] at he
  unfold entropy
  nlinarith only [he]

theorem entropyConstant_nonneg : 0 ≤ entropyConstant :=
  integral_nonneg (fun w => entropy_nonneg (J_nonneg w))

end BoltzmannNonuniqueness.JetThermalEntropy

end

end

section

/-! # The integrable hyperbolic axial weight of the cold datum -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetAxialWeight

theorem intervalIntegral_S (a b : ℝ) :
    (∫ x in a..b, S x) = Real.tanh b - Real.tanh a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => tanh_derivative x)
    (continuous_S.intervalIntegrable a b)

theorem intervalIntegral_S_le_two (a b : ℝ) : (∫ x in a..b, S x) ≤ 2 := by
  rw [intervalIntegral_S]
  linarith [Real.tanh_lt_one b, Real.neg_one_lt_tanh a]

theorem integrable_S : Integrable S := by
  apply integrable_of_intervalIntegral_norm_bounded (2 : ℝ)
    (a := fun r : ℝ => -r) (b := fun r : ℝ => r)
    (l := atTop)
    (fun r => (continuous_S.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
    tendsto_neg_atTop_atBot tendsto_id
  apply Eventually.of_forall
  intro r
  have he : (fun x : ℝ => ‖S x‖) = S := by
    funext x
    exact Real.norm_of_nonneg (S_pos x).le
  rw [he]
  exact intervalIntegral_S_le_two _ _

theorem scaled_derivative (γ s x : ℝ) :
    HasDerivAt (fun z => Real.tanh (γ * z / s)) ((γ / s) * S (γ * x / s)) x := by
  have h := (tanh_derivative (γ * x / s)).comp x
    (((hasDerivAt_id x).const_mul γ).div_const s)
  have he : S (γ * x / s) * (γ * 1 / s) = (γ / s) * S (γ * x / s) := by ring
  rw [he] at h
  exact h

theorem scaled_intervalIntegral {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) (a b : ℝ) :
    (∫ z in a..b, S (γ * z / s)) =
      (s / γ) * (Real.tanh (γ * b / s) - Real.tanh (γ * a / s)) := by
  have hc : Continuous (fun z : ℝ => S (γ * z / s)) :=
    continuous_S.comp ((continuous_const.mul continuous_id).div_const s)
  have hd (x : ℝ) : HasDerivAt (fun z => (s / γ) * Real.tanh (γ * z / s))
      (S (γ * x / s)) x := by
    have h := (scaled_derivative γ s x).const_mul (s / γ)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hc.intervalIntegrable a b)]
  ring

theorem scaled_intervalIntegral_le {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) (a b : ℝ) :
    (∫ z in a..b, S (γ * z / s)) ≤ 2 * s / γ := by
  rw [scaled_intervalIntegral hγ hs]
  have hb : Real.tanh (γ * b / s) - Real.tanh (γ * a / s) ≤ 2 := by
    linarith [Real.tanh_lt_one (γ * b / s), Real.neg_one_lt_tanh (γ * a / s)]
  have h := mul_le_mul_of_nonneg_left hb (div_pos hs hγ).le
  exact h.trans_eq (by ring)

end BoltzmannNonuniqueness.JetAxialWeight

end

end

section

/-! # Exponential control of the cold datum's axial entropy -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetAxialEntropy

theorem integrable_exp_neg_abs : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Iic 0) := by
    apply (integrableOn_exp_Iic 0).congr_fun _ measurableSet_Iic
    intro x hx
    dsimp only
    change x ≤ 0 at hx
    rw [abs_of_nonpos hx, neg_neg]
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Ioi 0) := by
    apply (integrableOn_exp_neg_Ioi 0).congr_fun _ measurableSet_Ioi
    intro x hx
    dsimp only
    rw [abs_of_pos hx]
  have h := hneg.union hpos
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem cosh_lower (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  linarith [Real.exp_pos (-|x|)]

theorem cosh_upper (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h := Real.exp_le_exp.mpr (show -|x| ≤ |x| by linarith [abs_nonneg x])
  linarith

theorem S_exp_bound (x : ℝ) : S x ≤ 4 * Real.exp (-2 * |x|) := by
  have hi := (inv_le_inv₀ (Real.cosh_pos x) (by positivity : 0 < Real.exp |x| / 2)).mpr
    (cosh_lower x)
  have he : (Real.exp |x| / 2)⁻¹ = 2 * Real.exp (-|x|) := by
    rw [inv_div, Real.exp_neg]
    ring
  rw [he] at hi
  have hs := (sq_le_sq₀ (inv_nonneg.mpr (Real.cosh_pos x).le) (by positivity)).mpr hi
  change S x ≤ (2 * Real.exp (-|x|)) ^ 2 at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  rw [mul_pow, ← Real.exp_nat_mul]
  norm_num

theorem log_S_bound (x : ℝ) : |Real.log (S x)| ≤ 2 * |x| := by
  have hlog : 0 ≤ Real.log (Real.cosh x) := Real.log_nonneg (Real.one_le_cosh x)
  have hb : Real.log (Real.cosh x) ≤ |x| := by
    have h := Real.log_le_log (Real.cosh_pos x) (cosh_upper x)
    simpa only [Real.log_exp] using h
  simp only [S, Real.log_pow, Real.log_inv, abs_mul, abs_neg,
    abs_of_nonneg hlog]
  norm_num
  linarith

theorem entropy_exp_bound (x : ℝ) : S x * |Real.log (S x)| ≤ 8 * Real.exp (-|x|) := by
  have hb := mul_le_mul (S_exp_bound x) (log_S_bound x)
    (abs_nonneg _) (by positivity : 0 ≤ 4 * Real.exp (-2 * |x|))
  have he : |x| * Real.exp (-2 * |x|) ≤ Real.exp (-|x|) := by
    have hh : |x| ≤ Real.exp |x| :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp |x|)
    have h := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-2 * |x|)).le
    rw [← Real.exp_add] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  nlinarith

theorem integrable_axial_entropy : Integrable (fun x : ℝ => S x * |Real.log (S x)|) := by
  apply (integrable_exp_neg_abs.const_mul 8).mono'
  · exact (continuous_S.mul ((continuous_S.log (fun x => (S_pos x).ne')).abs)).aestronglyMeasurable
  · filter_upwards [] with x
    rw [Real.norm_of_nonneg (mul_nonneg (S_pos x).le (abs_nonneg _))]
    exact entropy_exp_bound x

end BoltzmannNonuniqueness.JetAxialEntropy

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_WeightAlgebra
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

theorem tiltConstant_pos : 0 < tiltConstant := by unfold tiltConstant; positivity

end BoltzmannNonuniqueness.VelocityWeight

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

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_Moments
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.sphereArea_isFiniteMeasure _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrable moments of finite-entropy data

The weighted entropy assumption from the manuscript controls mass, kinetic
energy, absolute entropy, and vector momentum. These conclusions use the actual
integrability assumption rather than any default value of a Bochner integral.
-/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem density_le_entropyMoment {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    f z ≤ entropyMoment f z := by
  unfold entropyMoment
  nlinarith [mul_nonneg hf (sq_nonneg ‖z.2‖),
    mul_nonneg hf (abs_nonneg (Real.log (f z)))]

theorem energyDensity_le_entropyMoment {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    ‖z.2‖ ^ 2 * f z ≤ entropyMoment f z := by
  unfold entropyMoment
  nlinarith [mul_nonneg hf (abs_nonneg (Real.log (f z)))]

theorem absEntropyDensity_le_entropyMoment {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    f z * |Real.log (f z)| ≤ entropyMoment f z := by
  unfold entropyMoment
  nlinarith [mul_nonneg hf (sq_nonneg ‖z.2‖)]

namespace FiniteEntropyDatum

variable {f : Density} (hf : FiniteEntropyDatum f)

include hf

/-- Finite weighted entropy gives finite mass. -/
theorem integrable : Integrable f := by
  apply hf.2.2.mono' hf.2.1
  filter_upwards [hf.1] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using density_le_entropyMoment hz

/-- The energy functional integrates an integrable density. -/
theorem integrable_energy : Integrable (fun z => ‖z.2‖ ^ 2 * f z) := by
  have hm : AEStronglyMeasurable (fun z : Phase => ‖z.2‖ ^ 2) := by fun_prop
  apply hf.2.2.mono' (hm.mul hf.2.1)
  filter_upwards [hf.1] with z hz
  rw [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hz)]
  exact energyDensity_le_entropyMoment hz

/-- This is absolute entropy, including the convention at zero from the model. -/
theorem integrable_absEntropy : Integrable (fun z => f z * |Real.log (f z)|) := by
  have hlog : AEStronglyMeasurable (fun z => Real.log (f z)) :=
    hf.2.1.aemeasurable.log.aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun z => f z * |Real.log (f z)|) := by
    simpa only [Pi.mul_def, Real.norm_eq_abs] using hf.2.1.mul hlog.norm
  apply hf.2.2.mono' hm
  filter_upwards [hf.1] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hz (abs_nonneg _))]
  exact absEntropyDensity_le_entropyMoment hz

theorem integrable_entropy : Integrable (fun z => f z * Real.log (f z)) := by
  have hlog : AEStronglyMeasurable (fun z => Real.log (f z)) :=
    hf.2.1.aemeasurable.log.aestronglyMeasurable
  apply hf.integrable_absEntropy.mono' (hf.2.1.mul hlog)
  filter_upwards [hf.1] with z hz
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hz, le_refl]

end FiniteEntropyDatum

end BoltzmannNonuniqueness

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

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianEstimates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.MassTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.TorusFlight.flight_neg _root_.OAI.BoltzmannNonuniqueness.TorusFlight.flight_zero _root_.OAI.BoltzmannNonuniqueness.TorusFlight.neg_flight _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

theorem relativeEntropyDensity_eq {f : Density} {z : Phase} (hz : 0 ≤ f z) :
    f z * Real.log (f z / maxwellian z.2) - f z + maxwellian z.2 =
      f z * Real.log (f z) + ((3 / 2 : ℝ) * Real.log (2 * Real.pi) - 1) * f z +
        (1 / 2 : ℝ) * (‖z.2‖ ^ 2 * f z) + maxwellian z.2 := by
  rcases hz.eq_or_lt with hz | hz
  · simp [← hz]
  · rw [Real.log_div hz.ne' (maxwellian_pos _).ne', log_maxwellian]
    ring

theorem FiniteEntropyDatum.integrable_relativeEntropy {f : Density} (hf : FiniteEntropyDatum f) :
    Integrable (fun z => f z * Real.log (f z / maxwellian z.2) - f z + maxwellian z.2) := by
  have h := ((hf.integrable_entropy.add
    (hf.integrable.const_mul ((3 / 2 : ℝ) * Real.log (2 * Real.pi) - 1))).add
    (hf.integrable_energy.const_mul (1 / 2 : ℝ))).add integrable_maxwellian_phase
  apply h.congr
  filter_upwards [hf.1] with z hz
  exact (relativeEntropyDensity_eq hz).symm

/-- The scalar relative entropy is nonnegative at every nonnegative density value. -/
theorem relativeEntropyDensity_nonneg {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    0 ≤ a * Real.log (a / m) - a + m := by
  rcases ha.eq_or_lt with ha | ha
  · simp [← ha, hm.le]
  · have h := Real.log_le_sub_one_of_pos (div_pos hm ha)
    have hlog : Real.log (m / a) = -Real.log (a / m) := by
      rw [Real.log_div hm.ne' ha.ne', Real.log_div ha.ne' hm.ne']
      ring
    rw [hlog] at h
    have hh := mul_le_mul_of_nonneg_left h ha.le
    have he : a * (m / a - 1) = m - a := by field_simp
    rw [he] at hh
    nlinarith only [hh]

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyIntegralBalance
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

end BoltzmannNonuniqueness

end

end

section

/-!
# Lower semicontinuity of entropy production

The extended scalar entropy production is lower semicontinuous along positive
approximations of nonnegative products. In particular its value is infinite
when exactly one limiting product vanishes. Weighted Fatou then passes this
production to a limit, without a domination hypothesis or a finite-production
assumption. The final specialization applies to positive regularizations of
four nonnegative factors.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem measurable_extendedEntropyProduction {X : Type*} [MeasurableSpace X]
    {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => extendedEntropyProduction (a x) (b x)) := by
  unfold extendedEntropyProduction
  apply Measurable.ite
    ((measurableSet_eq_fun ha measurable_const).inter
      (measurableSet_eq_fun hb measurable_const)) measurable_const
  exact Measurable.ite
    ((measurableSet_lt measurable_const ha).inter (measurableSet_lt measurable_const hb))
    ((ha.sub hb).mul ((ha.div hb).log)).ennreal_ofReal measurable_const

end BoltzmannNonuniqueness

end

end

section

/-! # A regularization-independent integrable bound for relative entropy -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem scalarRelativeEntropy_nonneg {m u : ℝ} (hm : 0 < m) (hu : 0 ≤ u) :
    0 ≤ scalarRelativeEntropy m u := by
  rw [scalarRelativeEntropy_eq hm]
  exact relativeEntropyDensity_nonneg hu hm

end BoltzmannNonuniqueness

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

/-! # Bounded dual tests for relative entropy -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem entropyDual_le {m u : ℝ} (hm : 0 < m) (hu : 0 ≤ u) (s : ℝ) :
    entropyDual m u s ≤ scalarRelativeEntropy m u := by
  by_cases hz : u = 0
  · subst u
    dsimp [entropyDual,scalarRelativeEntropy]
    nlinarith [Real.exp_pos s]
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have hr : 0 < u/m := div_pos hup hm
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s-Real.log (u/m))) hu
    rw [Real.exp_sub,Real.exp_log hr] at h
    have he : u*(Real.exp s/(u/m)) = m*Real.exp s := by field_simp
    rw [he] at h
    rw [scalarRelativeEntropy_eq hm]
    dsimp [entropyDual]
    nlinarith only [h]

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarriers
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

theorem axialAmplitude_integrable (K γ s : ℝ) : Integrable (axialAmplitude K γ s) := by
  apply integrable_indicator_iff measurableSet_Ioo |>.mpr
  exact (((continuous_const.mul (continuous_S.comp
    ((continuous_const.mul continuous_id).div_const s))).integrableOn_Icc).mono_set Ioo_subset_Icc_self)

theorem spatial_integrable {η : ℝ} (hη : 0 ≤ η) (K γ s : ℝ) (a : Bool) :
    Integrable (spatial η K γ s a) spaceVolume :=
  (indicator_integrable hη a).mul_prod (axialAmplitude_integrable K γ s)

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

theorem density_velocity_integral {d : ℝ} (hd : 0 < d)
    (η K α γ s : ℝ) (a : Bool) (x : Space) :
    (∫ v, density η K α γ s d a (x, v)) = spatial η K γ s a x := by
  simp only [density, integral_const_mul, JetThermalLaw.density_mass hd, mul_one]

theorem density_integrable {η K s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hs : 0 ≤ s) (hd : 0 < d) (α γ : ℝ) (a : Bool) :
    Integrable (density η K α γ s d a) (spaceVolume.prod volume) := by
  apply (integrable_prod_iff (measurable_density η K α γ s d a).aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    exact (JetThermalLaw.density_integrable hd (center α γ s a x.2)).const_mul
      (spatial η K γ s a x)
  · have he : (fun x : Space => ∫ v, ‖density η K α γ s d a (x, v)‖) =
        spatial η K γ s a := by
      funext x
      simp_rw [Real.norm_of_nonneg (density_nonneg hK hs hd.le η α γ a _)]
      exact density_velocity_integral hd η K α γ s a x
    rw [he]
    exact spatial_integrable hη K γ s a

theorem density_mass_eq {η K s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hs : 0 ≤ s) (hd : 0 < d) (α γ : ℝ) (a : Bool) :
    (∫ p, density η K α γ s d a p ∂spaceVolume.prod volume) =
      volume.real (mask η s a) * ((K / s) *
        ∫ z in Ioo (-(1 / 8 : ℝ)) (1 / 8), S (γ * z / s)) := by
  rw [integral_prod _ (density_integrable hη hK hs hd α γ a)]
  simp_rw [density_velocity_integral hd]
  unfold spatial spaceVolume
  rw [integral_prod_mul, integral_indicator (measurableSet_mask η s a), setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  unfold axialAmplitude
  rw [integral_indicator measurableSet_Ioo, integral_const_mul]

theorem density_mass_bound {η K γ s d : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    (∫ p, density η K α γ s d a p ∂spaceVolume.prod volume) ≤
      (8 * Real.pi * K / γ) * s ^ 2 := by
  rw [density_mass_eq hη hK hs.le hd]
  have hz : (∫ z in Ioo (-(1 / 8 : ℝ)) (1 / 8), S (γ * z / s)) ≤ 2 * s / γ := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num :
      -(1 / 8 : ℝ) ≤ 1 / 8)]
    exact scaled_intervalIntegral_le hγ hs _ _
  have hm := mul_le_mul_of_nonneg_left hz (div_nonneg hK hs.le)
  have ha := mask_area_uniform hη hηmax hs.le a
  calc
    _ ≤ volume.real (mask η s a) * ((K / s) * (2 * s / γ)) :=
      mul_le_mul_of_nonneg_left hm measureReal_nonneg
    _ ≤ (4 * Real.pi * s ^ 2) * ((K / s) * (2 * s / γ)) :=
      mul_le_mul_of_nonneg_right ha (by positivity)
    _ = _ := by field_simp <;> ring

end BoltzmannNonuniqueness.JetPrototype

end

end

section

/-! # Absolute entropy of the cold datum's spatial factor -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetAxialWeight
open BoltzmannNonuniqueness.JetAxialEntropy
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetMaskMeasure

namespace BoltzmannNonuniqueness.JetSpatialEntropy

theorem scalar_scaled_integrable {f : ℝ → ℝ} (hf : Integrable f) {γ s : ℝ}
    (hγ : 0 < γ) (hs : 0 < s) : Integrable (fun z => f (γ * z / s)) := by
  have h := hf.comp_mul_left' (div_ne_zero hγ.ne' hs.ne')
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  congr 1
  ring

theorem scalar_scaled_integral (f : ℝ → ℝ) {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) :
    (∫ z, f (γ * z / s)) = (s / γ) * ∫ z, f z := by
  have he : (fun z => f (γ * z / s)) = fun z => f ((γ / s) * z) := by
    funext z
    congr 1
    ring
  rw [he, Measure.integral_comp_mul_left, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (div_pos hγ hs)), inv_div]

theorem massConstant_nonneg : 0 ≤ massConstant := integral_nonneg (fun z => (S_pos z).le)

theorem entropyConstant_nonneg : 0 ≤ entropyConstant :=
  integral_nonneg (fun z => entropy_nonneg (S_pos z).le)

theorem axial_entropy_bound {K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (γ z : ℝ) :
    entropy (axialAmplitude K γ s z) ≤ axialMajorant K γ s z := by
  by_cases hz : z ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
  · rw [axialAmplitude, indicator_of_mem hz]
    exact entropy_mul_le (div_nonneg hK hs.le) (S_pos _).le
  · rw [axialAmplitude, indicator_of_notMem hz]
    simp only [entropy, zero_mul]
    exact add_nonneg (mul_nonneg (S_pos _).le (entropy_nonneg (div_nonneg hK hs.le)))
      (mul_nonneg (div_nonneg hK hs.le) (entropy_nonneg (S_pos _).le))

theorem axialMajorant_integrable {γ s : ℝ} (hγ : 0 < γ) (hs : 0 < s) (K : ℝ) :
    Integrable (axialMajorant K γ s) :=
  ((scalar_scaled_integrable integrable_S hγ hs).mul_const _).add
    ((scalar_scaled_integrable integrable_axial_entropy hγ hs).const_mul _)

theorem axial_entropy_integrable {K γ s : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) :
    Integrable (fun z => entropy (axialAmplitude K γ s z)) := by
  have he : (fun z => entropy (axialAmplitude K γ s z)) =
      (Ioo (-(1 / 8 : ℝ)) (1 / 8)).indicator (fun z => entropy ((K / s) * S (γ * z / s))) := by
    funext z
    by_cases hz : z ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
    · simp only [axialAmplitude, indicator_of_mem hz]
    · simp only [axialAmplitude, indicator_of_notMem hz, entropy, zero_mul]
  apply (axialMajorant_integrable hγ hs K).mono'
  · rw [he]
    apply Measurable.aestronglyMeasurable
    apply Measurable.indicator _ measurableSet_Ioo
    exact (continuous_entropy_comp (continuous_const.mul (continuous_S.comp
      ((continuous_const.mul continuous_id).div_const s)))
        (fun z => mul_nonneg (div_nonneg hK hs.le) (S_pos _).le)).measurable
  · filter_upwards [] with z
    rw [Real.norm_of_nonneg (entropy_nonneg (axialAmplitude_nonneg hK hs.le γ z))]
    exact axial_entropy_bound hK hs γ z

theorem axial_entropy_integral {K γ s : ℝ} (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) :
    (∫ z, entropy (axialAmplitude K γ s z)) ≤
      (s / γ) * (entropy (K / s) * massConstant + (K / s) * entropyConstant) := by
  apply (integral_mono (axial_entropy_integrable hK hγ hs)
    (axialMajorant_integrable hγ hs K) (axial_entropy_bound hK hs γ)).trans_eq
  have hS : Integrable (fun z => S (γ * z / s)) := scalar_scaled_integrable integrable_S hγ hs
  have hE : Integrable (fun z => entropy (S (γ * z / s))) :=
    scalar_scaled_integrable integrable_axial_entropy hγ hs
  have hEI : (∫ z, entropy (S (γ * z / s))) =
      (s / γ) * ∫ z, entropy (S z) :=
    scalar_scaled_integral (fun z => entropy (S z)) hγ hs
  unfold axialMajorant
  rw [integral_add (hS.mul_const _) (hE.const_mul _),
    integral_mul_const, integral_const_mul, scalar_scaled_integral _ hγ hs, hEI]
  unfold massConstant entropyConstant
  ring

theorem spatial_entropy_eq (η K γ s : ℝ) (a : Bool) :
    (fun x : Space => entropy (spatial η K γ s a x)) =
      fun x => (mask η s a).indicator (fun _ => (1 : ℝ)) x.1 *
        entropy (axialAmplitude K γ s x.2) := by
  funext x
  by_cases hx : x.1 ∈ mask η s a <;> simp [spatial, hx, entropy]

theorem spatial_entropy_integrable {η K γ s : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    Integrable (fun x : Space => entropy (spatial η K γ s a x)) spaceVolume := by
  rw [spatial_entropy_eq]
  exact (indicator_integrable hη a).mul_prod (axial_entropy_integrable hK hγ hs)

theorem spatial_entropy_integral {η K γ s : ℝ} (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    (∫ x : Space, entropy (spatial η K γ s a x) ∂spaceVolume) ≤
      volume.real (mask η s a) * (s / γ) *
        (entropy (K / s) * massConstant + (K / s) * entropyConstant) := by
  rw [spatial_entropy_eq]
  dsimp only [spaceVolume]
  rw [integral_prod_mul ((mask η s a).indicator (fun _ => (1 : ℝ)))
    (fun z => entropy (axialAmplitude K γ s z)), integral_indicator (measurableSet_mask η s a),
    setIntegral_const]
  simp only [smul_eq_mul, mul_one]
  have h := mul_le_mul_of_nonneg_left (axial_entropy_integral hK hγ hs)
    (measureReal_nonneg : 0 ≤ volume.real (mask η s a))
  simpa only [mul_assoc] using h

end BoltzmannNonuniqueness.JetSpatialEntropy

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

theorem center_norm (α γ s : ℝ) (a : Bool) (z : ℝ) :
    ‖center α γ s a z‖ = |AxialFlow.profile (sign a) α γ s z| := by
  have h := PlaneChart.norm_join_sq (0 : Transverse) (AxialFlow.profile (sign a) α γ s z)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at h
  change ‖center α γ s a z‖ ^ 2 = _ at h
  nlinarith [sq_abs (AxialFlow.profile (sign a) α γ s z), norm_nonneg (center α γ s a z),
    abs_nonneg (AxialFlow.profile (sign a) α γ s z)]

theorem abs_sign (a : Bool) : |sign a| = 1 := by cases a <;> norm_num [sign]

theorem center_norm_bound {α : ℝ} (hα : 0 ≤ α) (γ s : ℝ) (a : Bool) (z : ℝ) :
    ‖center α γ s a z‖ ≤ 1 + α := by
  rw [center_norm]
  have h := AxialFlow.profile_sub_center_le (σ := sign a) (γ := γ) (s := s) (z := z) hα
  have ht := abs_add_le (AxialFlow.profile (sign a) α γ s z - sign a) (sign a)
  rw [sub_add_cancel, abs_sign] at ht
  linarith

theorem density_velocity_bound {d α : ℝ} (hd : 0 < d) (hα : 0 ≤ α)
    (η K γ s : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : JetPrototype.density η K α γ s d a p ≠ 0) : ‖p.2‖ < 1 + α + d := by
  have hthermal : JetThermalLaw.density d (center α γ s a p.1.2) p.2 ≠ 0 :=
    right_ne_zero_of_mul hp
  exact (JetThermalLaw.density_velocity_bound hd hthermal).trans_le
    (add_le_add (center_norm_bound hα γ s a _) le_rfl)

theorem density_support_two {d α : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 64)
    (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) (η K γ s : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : JetPrototype.density η K α γ s d a p ≠ 0) : ‖p.2‖ < 2 := by
  have h := density_velocity_bound hd hα η K γ s a hp
  linarith

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

/-! # Self-collision and the uniform loss-frequency bound of the actual barrier -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetBarrierCollision

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusChart
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.MassTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A centered fundamental cube for the periodic spatial variable -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusChart

theorem coordinate_measurePreserving : MeasurePreserving coordinate volume (volume.restrict interval) := by
  have h := (measurePreserving_subtype_coe (μa := (volume : Measure ℝ))
    (s := Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)) measurableSet_Ioc).comp
    (AddCircle.measurePreserving_equivIoc (T := (1 : ℝ)) (a := -(1 / 2 : ℝ)))
  change MeasurePreserving (Subtype.val ∘ (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))))
    volume (volume.restrict interval)
  have he : Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) = interval := by norm_num [interval]
  rw [← he]
  exact h

theorem measurableSet_cube : MeasurableSet cube := by
  have he : cube = ⋂ i : Fin 3, {x : Velocity | x i ∈ interval} := by ext x; simp [cube]
  rw [he]
  exact MeasurableSet.iInter (fun i => measurableSet_Ioc.preimage
    (show Measurable (fun x : Velocity => x i) from (PiLp.continuous_apply 2 _ i).measurable))

theorem representative_measurePreserving :
    MeasurePreserving representative volume (volume.restrict cube) := by
  have hp := measurePreserving_pi (fun _ : Fin 3 => (volume : Measure (AddCircle (1 : ℝ))))
    (fun _ : Fin 3 => (volume : Measure ℝ).restrict interval) (fun _ => coordinate_measurePreserving)
  have he := (PiLp.volume_preserving_toLp (ι := Fin 3)).restrict_preimage measurableSet_cube
  have hpre : WithLp.toLp 2 ⁻¹' cube = Set.univ.pi (fun _ : Fin 3 => interval) := by
    ext x
    simp [cube, Set.mem_pi, interval]
  rw [hpre] at he
  change MeasurePreserving (WithLp.toLp 2)
    ((Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ))).restrict (Set.univ.pi (fun _ => interval)))
    (volume.restrict cube) at he
  rw [Measure.restrict_pi_pi] at he
  exact he.comp hp

theorem representative_mem (x : Position) : representative x ∈ cube := by
  intro i
  have h := ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) (x i)).property
  change -(1 / 2 : ℝ) < coordinate (x i) ∧ coordinate (x i) ≤ 1 / 2
  constructor
  · exact h.1
  · change ((AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ))) (x i) : ℝ) ≤ 1 / 2
    linarith [h.2]

theorem phase_measurePreserving : MeasurePreserving phaseRepresentative
    (volume : Measure Phase) ((volume : Measure (Velocity × Velocity)).restrict (cube ×ˢ univ)) := by
  change MeasurePreserving phaseRepresentative
    ((volume : Measure Position).prod (volume : Measure Velocity))
    (((volume : Measure Velocity).prod (volume : Measure Velocity)).restrict (cube ×ˢ univ))
  rw [← Measure.prod_restrict]
  have h := representative_measurePreserving.prod (MeasurePreserving.id (volume : Measure Velocity))
  simp only [Measure.restrict_univ]
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

end BoltzmannNonuniqueness.TorusChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetPeriodicDatum
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.instCountableLabel _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integration of spatial weights against the cold thermal kernel -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalLaw

namespace BoltzmannNonuniqueness.JetWeightedKernel

theorem weighted_nonneg {d : ℝ} (hd : 0 ≤ d) (α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : ∀ x, 0 ≤ w x) {f : Velocity → ℝ} (hf : ∀ v, 0 ≤ f v)
    (p : JetPrototype.Phase) : 0 ≤ weighted d α γ s a w f p := by
  exact mul_nonneg (hw _) (mul_nonneg (inv_nonneg.mpr (pow_nonneg hd 3)) (hf _))

theorem weighted_measurable (d α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : Measurable w) {f : Velocity → ℝ} (hf : Measurable f) :
    Measurable (weighted d α γ s a w f) := by
  have hc : Measurable (fun p : JetPrototype.Phase => center α γ s a p.1.2) :=
    (measurable_center α γ s a).comp (measurable_snd.comp measurable_fst)
  have harg : Measurable (fun p : JetPrototype.Phase => d⁻¹ • (p.2 - center α γ s a p.1.2)) :=
    (measurable_const : Measurable (fun _ : JetPrototype.Phase => d⁻¹)).smul (measurable_snd.sub hc)
  exact (hw.comp measurable_fst).mul (measurable_const.mul (hf.comp harg))

theorem weighted_velocity_integral {d : ℝ} (hd : 0 < d) (α γ s : ℝ) (a : Bool)
    (w : Space → ℝ) (f : Velocity → ℝ) (x : Space) :
    (∫ v, weighted d α γ s a w f (x, v)) = w x * ∫ v, f v := by
  change (∫ v, w x * scaled d (center α γ s a x.2) f v) = _
  rw [integral_const_mul, integral_scaled f hd]

theorem weighted_integrable {d : ℝ} (hd : 0 < d) (α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : Measurable w) (hwi : Integrable w spaceVolume) (hwp : ∀ x, 0 ≤ w x)
    {f : Velocity → ℝ} (hf : Measurable f) (hfi : Integrable f) (hfp : ∀ v, 0 ≤ f v) :
    Integrable (weighted d α γ s a w f) (spaceVolume.prod volume) := by
  apply (integrable_prod_iff (weighted_measurable d α γ s a hw hf).aestronglyMeasurable).mpr
  constructor
  · apply Filter.Eventually.of_forall
    intro x
    exact (integrable_scaled hfi hd (center α γ s a x.2)).const_mul (w x)
  · have he : (fun x : Space => ∫ v, ‖weighted d α γ s a w f (x, v)‖) =
        fun x => w x * ∫ v, f v := by
      funext x
      simp_rw [Real.norm_of_nonneg (weighted_nonneg hd.le α γ s a hwp hfp _)]
      exact weighted_velocity_integral hd α γ s a w f x
    rw [he]
    exact hwi.mul_const _

theorem weighted_integral {d : ℝ} (hd : 0 < d) (α γ s : ℝ) (a : Bool)
    {w : Space → ℝ} (hw : Measurable w) (hwi : Integrable w spaceVolume) (hwp : ∀ x, 0 ≤ w x)
    {f : Velocity → ℝ} (hf : Measurable f) (hfi : Integrable f) (hfp : ∀ v, 0 ≤ f v) :
    (∫ p, weighted d α γ s a w f p ∂spaceVolume.prod volume) =
      (∫ x, w x ∂spaceVolume) * ∫ v, f v := by
  rw [integral_prod _ (weighted_integrable hd α γ s a hw hwi hwp hf hfi hfp)]
  simp_rw [weighted_velocity_integral hd α γ s a]
  exact integral_mul_const _ _

end BoltzmannNonuniqueness.JetWeightedKernel

end

end

section

/-! # Absolute entropy of each actual cold-jet prototype -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalKernel
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetWeightedKernel

namespace BoltzmannNonuniqueness.JetPrototypeEntropy

theorem measurable_entropy {X : Type*} [MeasurableSpace X] {f : X → ℝ}
    (hf : Measurable f) : Measurable (fun x => entropy (f x)) :=
  hf.mul (Real.measurable_log.comp hf).abs

theorem spatialWeight_nonneg {K s : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s)
    (η γ d : ℝ) (a : Bool) (x : Space) : 0 ≤ spatialWeight η K γ s d a x :=
  add_nonneg (entropy_nonneg (spatial_nonneg hK hs η γ a x))
    (mul_nonneg (by positivity) (spatial_nonneg hK hs η γ a x))

theorem spatialWeight_measurable (η K γ s d : ℝ) (a : Bool) :
    Measurable (spatialWeight η K γ s d a) :=
  (measurable_entropy (measurable_spatial η K γ s a)).add
    (measurable_const.mul (measurable_spatial η K γ s a))

theorem spatialWeight_integrable {η K γ s : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (d : ℝ) (a : Bool) :
    Integrable (spatialWeight η K γ s d a) spaceVolume :=
  (JetSpatialEntropy.spatial_entropy_integrable hη hK hγ hs a).add
    ((spatial_integrable hη K γ s a).const_mul _)

theorem entropy_le_majorant {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s)
    (hd : 0 < d) (η α γ : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    entropy (density η K α γ s d a p) ≤ majorant η K α γ s d a p := by
  have hw := spatial_nonneg hK hs η γ a p.1
  have h₁ := entropy_mul_le hw
    (JetThermalLaw.density_nonneg hd.le (center α γ s a p.1.2) p.2)
  have h₂ := mul_le_mul_of_nonneg_left
    (density_entropy_bound hd (center α γ s a p.1.2) p.2) hw
  unfold density at *
  unfold JetThermalLaw.density at h₁ h₂
  unfold majorant weighted spatialWeight JetThermalLaw.density
  nlinarith only [h₁, h₂]

theorem majorant_integrable {η K γ s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    Integrable (majorant η K α γ s d a) (spaceVolume.prod volume) := by
  apply Integrable.add
  · exact weighted_integrable hd α γ s a (spatialWeight_measurable η K γ s d a)
      (spatialWeight_integrable hη hK hγ hs d a)
      (spatialWeight_nonneg hK hs.le η γ d a) J_smooth.continuous.measurable
      J_integrable J_nonneg
  · exact weighted_integrable hd α γ s a (measurable_spatial η K γ s a)
      (spatial_integrable hη K γ s a) (spatial_nonneg hK hs.le η γ a)
      (measurable_entropy J_smooth.continuous.measurable) JetThermalLaw.integrable_J_entropy
      (fun v => entropy_nonneg (J_nonneg v))

theorem density_entropy_integrable {η K γ s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    Integrable (fun p => entropy (density η K α γ s d a p))
      (spaceVolume.prod volume) := by
  apply (majorant_integrable hη hK hγ hs hd α a).mono'
  · exact (measurable_entropy (measurable_density η K α γ s d a)).aestronglyMeasurable
  · filter_upwards [] with p
    rw [Real.norm_of_nonneg (entropy_nonneg (density_nonneg hK hs.le hd.le η α γ a p))]
    exact entropy_le_majorant hK hs.le hd η α γ a p

theorem density_entropy_integral {η K γ s d : ℝ} (hη : 0 ≤ η) (hK : 0 ≤ K)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (α : ℝ) (a : Bool) :
    (∫ p, entropy (density η K α γ s d a p) ∂spaceVolume.prod volume) ≤
      (∫ x, entropy (spatial η K γ s a x) ∂spaceVolume) +
        (3 * |Real.log d| + JetThermalEntropy.entropyConstant) *
          ∫ x, spatial η K γ s a x ∂spaceVolume := by
  apply (integral_mono (density_entropy_integrable hη hK hγ hs hd α a)
    (majorant_integrable hη hK hγ hs hd α a)
    (entropy_le_majorant hK hs.le hd η α γ a)).trans_eq
  have hi₁ := weighted_integrable hd α γ s a (spatialWeight_measurable η K γ s d a)
    (spatialWeight_integrable hη hK hγ hs d a)
    (spatialWeight_nonneg hK hs.le η γ d a) J_smooth.continuous.measurable
    J_integrable J_nonneg
  have hi₂ := weighted_integrable hd α γ s a (measurable_spatial η K γ s a)
    (spatial_integrable hη K γ s a) (spatial_nonneg hK hs.le η γ a)
    (measurable_entropy J_smooth.continuous.measurable) JetThermalLaw.integrable_J_entropy
    (fun v => entropy_nonneg (J_nonneg v))
  unfold majorant
  rw [integral_add hi₁ hi₂,
    weighted_integral hd α γ s a (spatialWeight_measurable η K γ s d a)
      (spatialWeight_integrable hη hK hγ hs d a)
      (spatialWeight_nonneg hK hs.le η γ d a) J_smooth.continuous.measurable J_integrable J_nonneg,
    weighted_integral hd α γ s a (measurable_spatial η K γ s a)
      (spatial_integrable hη K γ s a) (spatial_nonneg hK hs.le η γ a)
      (measurable_entropy J_smooth.continuous.measurable) JetThermalLaw.integrable_J_entropy
      (fun v => entropy_nonneg (J_nonneg v)), J_integral, mul_one]
  unfold spatialWeight JetThermalEntropy.entropyConstant
  rw [integral_add (JetSpatialEntropy.spatial_entropy_integrable hη hK hγ hs a)
    ((spatial_integrable hη K γ s a).const_mul _), integral_const_mul]
  ring

end BoltzmannNonuniqueness.JetPrototypeEntropy

end

end

section

/-! # The scale-uniform, summable cold-jet entropy bound -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetMaskMeasure

namespace BoltzmannNonuniqueness.JetEntropyBound

theorem spatialConstant_nonneg {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 ≤ γ) :
    0 ≤ spatialConstant K γ := by
  have := JetSpatialEntropy.massConstant_nonneg
  have := JetSpatialEntropy.entropyConstant_nonneg
  unfold spatialConstant
  positivity

theorem constant_nonneg {K γ : ℝ} (hK : 0 ≤ K) (hγ : 0 ≤ γ) (d₀ : ℝ) :
    0 ≤ constant K γ d₀ := by
  have := spatialConstant_nonneg hK hγ
  have := JetThermalEntropy.entropyConstant_nonneg
  unfold constant
  positivity

theorem spatial_mass_bound {η K γ s : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    (∫ x, spatial η K γ s a x ∂spaceVolume) ≤ (8 * Real.pi * K / γ) * s ^ 2 := by
  have h := density_mass_bound hη hηmax hK hγ hs (show (0 : ℝ) < 1 by norm_num) 0 a
  rw [integral_prod _ (density_integrable hη hK hs.le (show (0 : ℝ) < 1 by norm_num) 0 γ a)] at h
  simpa only [density_velocity_integral (show (0 : ℝ) < 1 by norm_num)] using h

theorem spatial_entropy_bound {η K γ s : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hs : 0 < s) (a : Bool) :
    (∫ x, entropy (spatial η K γ s a x) ∂spaceVolume) ≤
      spatialConstant K γ * s ^ 2 * (1 + |Real.log s|) := by
  have hM := JetSpatialEntropy.massConstant_nonneg
  have hE := JetSpatialEntropy.entropyConstant_nonneg
  have hlog : |Real.log (K / s)| ≤ |Real.log K| + |Real.log s| := by
    rw [Real.log_div hK.ne' hs.ne']
    exact abs_sub _ _
  have heq : (s / γ) * (entropy (K / s) * JetSpatialEntropy.massConstant +
      (K / s) * JetSpatialEntropy.entropyConstant) =
      (K / γ) * (|Real.log (K / s)| * JetSpatialEntropy.massConstant +
        JetSpatialEntropy.entropyConstant) := by
    unfold entropy
    field_simp
  have hscalar : (|Real.log K| + |Real.log s|) * JetSpatialEntropy.massConstant +
      JetSpatialEntropy.entropyConstant ≤
      ((|Real.log K| + 1) * JetSpatialEntropy.massConstant + JetSpatialEntropy.entropyConstant) *
        (1 + |Real.log s|) := by
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (Real.log K)) hM) (abs_nonneg (Real.log s)),
      mul_nonneg hE (abs_nonneg (Real.log s))]
  calc
    _ ≤ volume.real (mask η s a) * ((s / γ) *
        (entropy (K / s) * JetSpatialEntropy.massConstant +
          (K / s) * JetSpatialEntropy.entropyConstant)) := by
      simpa only [mul_assoc] using JetSpatialEntropy.spatial_entropy_integral hK.le hγ hs a
    _ = volume.real (mask η s a) * (K / γ) *
        (|Real.log (K / s)| * JetSpatialEntropy.massConstant + JetSpatialEntropy.entropyConstant) := by
      rw [heq, mul_assoc]
    _ ≤ (4 * Real.pi * s ^ 2) * (K / γ) *
        ((|Real.log K| + |Real.log s|) * JetSpatialEntropy.massConstant +
          JetSpatialEntropy.entropyConstant) := by
      gcongr
      exact mask_area_uniform hη hηmax hs.le a
    _ ≤ (4 * Real.pi * s ^ 2) * (K / γ) *
        (((|Real.log K| + 1) * JetSpatialEntropy.massConstant +
          JetSpatialEntropy.entropyConstant) * (1 + |Real.log s|)) :=
      mul_le_mul_of_nonneg_left hscalar (by positivity)
    _ = _ := by unfold spatialConstant; ring

theorem thermal_log_bound {d₀ s : ℝ} (hd₀ : 0 < d₀) (hs : 0 < s) :
    3 * |Real.log (d₀ * s ^ 10)| + JetThermalEntropy.entropyConstant ≤
      (3 * (|Real.log d₀| + 10) + JetThermalEntropy.entropyConstant) * (1 + |Real.log s|) := by
  have hlog : |Real.log (d₀ * s ^ 10)| ≤ |Real.log d₀| + 10 * |Real.log s| := by
    rw [Real.log_mul hd₀.ne' (pow_ne_zero _ hs.ne'), Real.log_pow]
    have h := abs_add_le (Real.log d₀) (10 * Real.log s)
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10), Nat.cast_ofNat] using h
  have hE := JetThermalEntropy.entropyConstant_nonneg
  nlinarith [mul_nonneg (abs_nonneg (Real.log d₀)) (abs_nonneg (Real.log s)),
    mul_nonneg hE (abs_nonneg (Real.log s))]

/-- The constant depends only on the fixed parameters, and is independent of the annular scale. -/
theorem prototype_entropy_bound {η K γ s d₀ : ℝ} (hη : 0 ≤ η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hs : 0 < s) (hd₀ : 0 < d₀) (α : ℝ) (a : Bool) :
    (∫ p, entropy (density η K α γ s (d₀ * s ^ 10) a p) ∂spaceVolume.prod volume) ≤
      constant K γ d₀ * s ^ 2 * (1 + |Real.log s|) := by
  have hd : 0 < d₀ * s ^ 10 := mul_pos hd₀ (pow_pos hs _)
  have hsp := spatial_entropy_bound hη hηmax hK hγ hs a
  have hm := spatial_mass_bound hη hηmax hK.le hγ hs a
  have ht := thermal_log_bound hd₀ hs
  have hm0 : 0 ≤ ∫ x, spatial η K γ s a x ∂spaceVolume :=
    integral_nonneg (spatial_nonneg hK.le hs.le η γ a)
  calc
    _ ≤ (∫ x, entropy (spatial η K γ s a x) ∂spaceVolume) +
        (3 * |Real.log (d₀ * s ^ 10)| + JetThermalEntropy.entropyConstant) *
          ∫ x, spatial η K γ s a x ∂spaceVolume :=
      JetPrototypeEntropy.density_entropy_integral hη hK.le hγ hs hd α a
    _ ≤ spatialConstant K γ * s ^ 2 * (1 + |Real.log s|) +
        ((3 * (|Real.log d₀| + 10) + JetThermalEntropy.entropyConstant) * (1 + |Real.log s|)) *
          ((8 * Real.pi * K / γ) * s ^ 2) := by
      exact add_le_add hsp (mul_le_mul ht hm hm0 (by
        have := JetThermalEntropy.entropyConstant_nonneg
        positivity))
    _ = _ := by unfold constant; ring

end BoltzmannNonuniqueness.JetEntropyBound

end

end

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

theorem entropy_tsum {ι : Type*} {f : ι → ℝ}
    (hf : ∀ i j, i ≠ j → f i ≠ 0 → f j = 0) :
    entropy (∑' i, f i) = ∑' i, entropy (f i) := by
  classical
  by_cases h : ∃ i, f i ≠ 0
  · obtain ⟨i, hi⟩ := h
    have hz : ∀ j, j ≠ i → f j = 0 := fun j hj => hf i j hj.symm hi
    rw [tsum_eq_single i hz, tsum_eq_single i]
    intro j hj
    simp [hz j hj, entropy]
  · have hz : ∀ i, f i = 0 := fun i => not_ne_iff.mp (not_exists.mp h i)
    simp [hz, entropy]

theorem integrable_nonnegative_series {ι X : Type*} [Countable ι] [MeasurableSpace X]
    {μ : Measure X} {f : ι → X → ℝ}
    (hm : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (f i) μ)
    (hn : ∀ i x, 0 ≤ f i x) (hs : ∀ x, Summable (fun i => f i x))
    (hI : Summable (fun i => ∫ x, f i x ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  refine ⟨(Measurable.tsum hm).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun x => tsum_nonneg (fun i => hn i x)))).mpr
  have he : (∫⁻ x, ENNReal.ofReal (∑' i, f i x) ∂μ) =
      ∑' i, ENNReal.ofReal (∫ x, f i x ∂μ) := by
    simp_rw [ENNReal.ofReal_tsum_of_nonneg (fun i => hn i _) (hs _)]
    rw [lintegral_tsum (fun i => (hm i).ennreal_ofReal.aemeasurable)]
    congr 1
    funext i
    exact (ofReal_integral_eq_lintegral_ofReal (hi i)
      (Filter.Eventually.of_forall (hn i))).symm
  rw [he]
  exact hI.tsum_ofReal_lt_top

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

theorem term_integrable {s₀ η K d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η)
    (hK : 0 ≤ K) (hd₀ : 0 < d₀) (α γ : ℝ) (i : Index) :
    Integrable (term s₀ η K α γ d₀ i) (spaceVolume.prod volume) :=
  density_integrable hη hK (DatumBounds.scale_pos hs₀ _).le
    (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _)) α γ i.2

theorem term_entropy_integrable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 ≤ η)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) (i : Index) :
    Integrable (fun p => entropy (term s₀ η K α γ d₀ i p)) (spaceVolume.prod volume) :=
  JetPrototypeEntropy.density_entropy_integrable hη hK hγ (DatumBounds.scale_pos hs₀ _)
    (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _)) α i.2

theorem term_measurable (s₀ η K α γ d₀ : ℝ) (i : Index) :
    Measurable (term s₀ η K α γ d₀ i) := measurable_density _ _ _ _ _ _ _

private theorem in_enlargement {s₀ η K α γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    {i : Index} {p : JetPrototype.Phase} (hp : term s₀ η K α γ d₀ i p ≠ 0) :
    PlaneChart.join p.1.1 p.1.2 ∈ JetLattice.spatialEnlargement s₀ η 0 (label i) := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.1 + 1)
  have hsp := JetSupport.initial_spatial_support η K α γ _ _ i.2 hp
  constructor
  · change transverse (PlaneChart.join p.1.1 p.1.2) - JetLattice.transverseShift 0 ∈
      enlargement η (jetScale s₀ η i.1) i.2
    have hz : JetLattice.transverseShift 0 = 0 := by ext k; simp [JetLattice.transverseShift]
    rw [PlaneChart.transverse_join, hz, sub_zero]
    exact Metric.mem_cthickening_of_dist_le p.1.1 p.1.1 _ _ hsp.1
      (by simpa [jetScale] using (enlargementWidth_pos hη hs).le)
  · simpa [label, JetLattice.axialShift, PlaneChart.axial_join] using
      (show |p.1.2| ≤ 1 / 8 + 2 * (0 : ℝ) + 1 / 16 by linarith [hsp.2])

theorem term_disjoint {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase)
    (i j : Index) (hij : i ≠ j) (hi : term s₀ η K α γ d₀ i p ≠ 0) :
    term s₀ η K α γ d₀ j p = 0 := by
  by_contra hj
  have he := JetLattice.common_point_label hs₀ hsmax hη hηmax (by norm_num : (0 : ℝ) ≤ 1 / 32)
    (in_enlargement hs₀ hη hi) (in_enlargement hs₀ hη hj)
  apply hij
  exact Prod.ext (congrArg JetLattice.Label.annulus he) (congrArg JetLattice.Label.positive he)

theorem term_summable {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase) :
    Summable (fun i => term s₀ η K α γ d₀ i p) :=
  JetSeries.summable_single_support (term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p)

theorem entropy_datum {s₀ η : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (K α γ d₀ : ℝ) (p : JetPrototype.Phase) :
    entropy (datum s₀ η K α γ d₀ p) = ∑' i, entropy (term s₀ η K α γ d₀ i p) :=
  JetSeries.entropy_tsum (term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p)

theorem summable_bool_extension {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (hs : Summable f) :
    Summable (fun i : Index => f i.1) := by
  apply (summable_prod_of_nonneg (fun i => hf i.1)).mpr
  constructor
  · intro j
    exact summable_of_hasFiniteSupport (Set.toFinite _)
  · simpa only [tsum_fintype, Fintype.sum_bool] using hs.add hs

theorem mass_summable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) :
    Summable (fun i : Index => ∫ p, term s₀ η K α γ d₀ i p ∂spaceVolume.prod volume) := by
  have hs : Summable (fun j => (8 * Real.pi * K / γ) * jetScale s₀ η j ^ 2) := by
    exact ((summable_nat_add_iff 1).mpr (DatumBounds.summable_scale_sq s₀ hη)).mul_left _
  apply Summable.of_nonneg_of_le
    (fun i => integral_nonneg (term_nonneg hs₀ hK hd₀.le η α γ i))
    (fun i => density_mass_bound hη.le hηmax hK hγ (DatumBounds.scale_pos hs₀ _)
      (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _)) α i.2)
    (summable_bool_extension (fun j => by positivity) hs)

theorem entropy_summable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (α : ℝ) :
    Summable (fun i : Index => ∫ p, entropy (term s₀ η K α γ d₀ i p) ∂spaceVolume.prod volume) := by
  have hs : Summable (fun j => JetEntropyBound.constant K γ d₀ *
      (jetScale s₀ η j ^ 2 * (1 + |Real.log (jetScale s₀ η j)|))) := by
    exact ((summable_nat_add_iff 1).mpr (DatumBounds.summable_entropyBound hs₀ hη)).mul_left _
  apply Summable.of_nonneg_of_le
    (fun i => integral_nonneg (fun p => entropy_nonneg (term_nonneg hs₀ hK.le hd₀.le η α γ i p)))
    (fun i => ?_) (summable_bool_extension (fun j => by
      have := JetEntropyBound.constant_nonneg hK.le hγ.le d₀
      positivity) hs)
  simpa only [mul_assoc, term, jetScale] using JetEntropyBound.prototype_entropy_bound hη.le hηmax hK hγ
    (DatumBounds.scale_pos hs₀ _) hd₀ α i.2

theorem datum_integrable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (α : ℝ) : Integrable (datum s₀ η K α γ d₀) (spaceVolume.prod volume) :=
  JetSeries.integrable_nonnegative_series (term_measurable s₀ η K α γ d₀)
    (term_integrable hs₀ hη.le hK hd₀ α γ) (term_nonneg hs₀ hK hd₀.le η α γ)
    (term_summable hs₀ hsmax hη hηmax K α γ d₀) (mass_summable hs₀ hη hηmax hK hγ hd₀ α)

theorem datum_entropy_integrable {s₀ η K γ d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (α : ℝ) :
    Integrable (fun p => entropy (datum s₀ η K α γ d₀ p)) (spaceVolume.prod volume) := by
  simp_rw [entropy_datum hs₀ hsmax hη hηmax]
  apply JetSeries.integrable_nonnegative_series
    (fun i => JetPrototypeEntropy.measurable_entropy (term_measurable s₀ η K α γ d₀ i))
    (term_entropy_integrable hs₀ hη.le hK.le hγ hd₀ α)
    (fun i p => entropy_nonneg (term_nonneg hs₀ hK.le hd₀.le η α γ i p))
    (fun p => JetSeries.summable_single_support ?_)
    (entropy_summable hs₀ hη hηmax hK hγ hd₀ α)
  intro i j hij hi
  have ht : term s₀ η K α γ d₀ i p ≠ 0 := by
    intro h
    exact hi (by simp [h, entropy])
  simp [term_disjoint hs₀ hsmax hη hηmax K α γ d₀ p i j hij ht, entropy]

end BoltzmannNonuniqueness.JetDatum

end

end

section

/-! # Mass, energy, and entropy of the full cold datum -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetDatum

namespace BoltzmannNonuniqueness.JetDatumMoments

theorem datum_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η α γ : ℝ) (p : JetPrototype.Phase) : 0 ≤ datum s₀ η K α γ d₀ p :=
  tsum_nonneg (fun i => term_nonneg hs₀ hK hd₀ η α γ i p)

theorem thermal_width_le {s₀ η d₀ : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hd₀ : 0 ≤ d₀) (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (j : ℕ) :
    d₀ * jetScale s₀ η j ^ 10 ≤ 1 / 64 := by
  have hs : jetScale s₀ η j ≤ 1 / 8 := by
    change DatumBounds.scale s₀ η (j + 1) ≤ _
    calc
      _ ≤ DatumBounds.scale s₀ η 0 := scale_antitone hs₀.le hη (Nat.zero_le (j + 1))
      _ = s₀ := by simp [DatumBounds.scale]
      _ ≤ _ := hsmax
  exact (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (DatumBounds.scale_pos hs₀ _).le hs 10) hd₀).trans hwidth

theorem datum_support_two {s₀ η d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hd₀ : 0 < d₀) (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64)
    (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) (K γ : ℝ) (p : JetPrototype.Phase)
    (hp : 2 ≤ ‖p.2‖) : datum s₀ η K α γ d₀ p = 0 := by
  have hz : ∀ i, term s₀ η K α γ d₀ i p = 0 := by
    intro i
    by_contra hi
    have hv := JetSupport.density_support_two
      (mul_pos hd₀ (pow_pos (DatumBounds.scale_pos hs₀ _) _))
      (thermal_width_le hs₀ hsmax hη hd₀.le hwidth i.1) hα hαmax η K γ _ i.2 hi
    exact (not_lt_of_ge hp) hv
  simp only [datum, hz, tsum_zero]

theorem datum_energy_integrable {s₀ η K γ d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) :
    Integrable (fun p => datum s₀ η K α γ d₀ p * ‖p.2‖ ^ 2) (spaceVolume.prod volume) := by
  have hi := datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α
  apply (hi.mul_const 4).mono'
  · exact hi.aestronglyMeasurable.mul (continuous_snd.norm.pow 2).aestronglyMeasurable
  · filter_upwards [] with p
    have hn := datum_nonneg hs₀ hK hd₀.le η α γ p
    rw [Real.norm_of_nonneg (mul_nonneg hn (sq_nonneg _))]
    by_cases hv : 2 ≤ ‖p.2‖
    · rw [datum_support_two hs₀ hsmax hη.le hd₀ hwidth hα hαmax K γ p hv]
      simp
    · have hv' : ‖p.2‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg p.2]
      exact mul_le_mul_of_nonneg_left hv' hn

theorem datum_entropyMoment_integrable {s₀ η K γ d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) :
    Integrable (fun p => datum s₀ η K α γ d₀ p *
      (1 + ‖p.2‖ ^ 2 + |Real.log (datum s₀ η K α γ d₀ p)|)) (spaceVolume.prod volume) := by
  convert ((datum_integrable hs₀ hsmax hη hηmax hK.le hγ hd₀ α).add
    (datum_energy_integrable hs₀ hsmax hη hηmax hK.le hγ hd₀ hwidth hα hαmax)).add
    (datum_entropy_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α) using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [Pi.add_apply, entropy]
  ring

end BoltzmannNonuniqueness.JetDatumMoments

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

section

/-! # The cold datum on the actual unit spatial torus -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetPeriodicDatum

theorem integrable_pullback {f : JetPrototype.Phase → ℝ}
    (hf : Integrable f (spaceVolume.prod volume)) : Integrable (pullback f) := by
  have hl := phaseMap_measurePreserving.integrable_comp_of_integrable hf
  exact TorusChart.phase_measurePreserving.integrable_comp_of_integrable hl.restrict

theorem finiteEntropy {s₀ η K γ d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) :
    FiniteEntropyDatum (datum s₀ η K α γ d₀) := by
  refine ⟨Filter.Eventually.of_forall (fun p => ?_), ?_, ?_⟩
  · exact JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  · exact (integrable_pullback (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK.le hγ hd₀ α)).1
  · exact integrable_pullback
      (JetDatumMoments.datum_entropyMoment_integrable hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax)

end BoltzmannNonuniqueness.JetPeriodicDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_AnnularEnvelopes
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The integrable square of the cold annular time envelope -/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem time_square_continuous {s T : ℝ} (hs : 0 < s) (_hT : 0 ≤ T) :
    ContinuousOn (fun t : ℝ => s^2/(t+s)^2) (Icc 0 T) := by
  apply continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 2)
  intro t ht
  apply pow_ne_zero
  change t+s ≠ 0
  linarith [ht.1]

theorem time_square_integral {s T : ℝ} (hs : 0 < s) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, s^2/(t+s)^2) = s-s^2/(T+s) := by
  have hi : IntervalIntegrable (fun t : ℝ => s^2/(t+s)^2) volume 0 T :=
    (time_square_continuous hs hT).intervalIntegrable_of_Icc hT
  have hd (t : ℝ) (ht : t ∈ uIcc 0 T) :
      HasDerivAt (fun t : ℝ => -(s^2)/(t+s)) (s^2/(t+s)^2) t := by
    have ht0 : 0 ≤ t := ((uIcc_of_le hT) ▸ ht).1
    have hn : t+s ≠ 0 := by linarith
    have ha : HasDerivAt (fun u : ℝ => u+s) 1 t := (hasDerivAt_id t).add_const s
    have hb : HasDerivAt (fun _ : ℝ => -(s^2)) 0 t := hasDerivAt_const t _
    simpa only [zero_mul,mul_one,zero_sub,neg_neg] using hb.fun_div ha hn
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp only [zero_add]
  field_simp
  ring

theorem time_square_integral_le {s T : ℝ} (hs : 0 < s) (hT : 0 ≤ T) :
    (∫ t in (0:ℝ)..T, s^2/(t+s)^2) ≤ s := by
  rw [time_square_integral hs hT]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by linarith))


end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # Disjoint radial annuli and their scale-uniform area bounds -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem shell_measurable (s₀ η : ℝ) (j : ℕ) : MeasurableSet (shell s₀ η j) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

theorem shell_disjoint {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    {i j : ℕ} (hij : i ≠ j) : Disjoint (shell s₀ η i) (shell s₀ η j) := by
  apply disjoint_left.mpr
  intro y hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have ho := ordered_annuli hs₀ hη h
    exact not_lt_of_ge ho (hi.1.trans hj.2)
  · have ho := ordered_annuli hs₀ hη h
    exact not_lt_of_ge ho (hj.1.trans hi.2)

theorem shell_subset_ball (s₀ η : ℝ) (j : ℕ) :
    shell s₀ η j ⊆ ball 0 (Real.exp η*jetScale s₀ η j) := by
  intro y hy
  exact (mem_ball_zero_iff).mpr hy.2

theorem shell_finite (s₀ η : ℝ) (j : ℕ) : volume (shell s₀ η j) < ⊤ :=
  (measure_mono (shell_subset_ball s₀ η j)).trans_lt (measure_ball_lt_top ..)

theorem shell_area_le {s₀ η : ℝ} (hs₀ : 0 < s₀) (hηmax : η ≤ Real.log 2) (j : ℕ) :
    volume.real (shell s₀ η j) ≤ 4*Real.pi*(jetScale s₀ η j)^2 := by
  have hs : 0 ≤ jetScale s₀ η j := (DatumBounds.scale_pos hs₀ _).le
  have h := measureReal_mono (μ := (volume : Measure Transverse)) (shell_subset_ball s₀ η j)
  rw [TransverseDisk.disk_volume_real 0 (mul_nonneg (Real.exp_pos η).le hs)] at h
  have he : Real.exp η ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0:ℝ) < 2)] using Real.exp_le_exp.mpr hηmax
  have hp := mul_le_mul_of_nonneg_right he hs
  have hsq : (Real.exp η*jetScale s₀ η j)^2 ≤ (2*jetScale s₀ η j)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hp
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left hsq Real.pi_pos.le])

theorem term_measurable (s₀ η : ℝ) (j : ℕ) :
    Measurable (fun u : ℝ × Transverse => term s₀ η j u.1 u.2) := by
  have he : (fun u : ℝ × Transverse => term s₀ η j u.1 u.2) =
      ((Prod.snd ⁻¹' shell s₀ η j).indicator (fun u => 1/(u.1+jetScale s₀ η j))) := by
    funext u
    by_cases h : u.2 ∈ shell s₀ η j <;> simp [term,h]
  rw [he]
  exact (measurable_const.div (measurable_fst.add_const _)).indicator
    ((shell_measurable s₀ η j).preimage measurable_snd)

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # An integrable squared envelope for all finite annular truncations -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem inverse_square_integrable {s T : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => 1/(t+s)^2) (Icc 0 T) := by
  apply ContinuousOn.integrableOn_compact (K := Icc 0 T) isCompact_Icc
  apply continuousOn_const.div ((continuousOn_id.add continuousOn_const).pow 2)
  intro t ht
  apply pow_ne_zero
  change t+s ≠ 0
  linarith [ht.1]

theorem inverse_square_integral_le {s T : ℝ} (hs : 0 < s) (hT : 0 ≤ T) :
    (∫ t in Icc (0:ℝ) T, 1/(t+s)^2) ≤ 1/s := by
  have he : (∫ t in Icc (0:ℝ) T, 1/(t+s)^2)*s^2 =
      ∫ t in (0:ℝ)..T, s^2/(t+s)^2 := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hT,
      ← intervalIntegral.integral_mul_const]
    congr 1
    funext t
    ring
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hs)).mp
  calc
    s^2*(∫ t in Icc (0:ℝ) T, 1/(t+s)^2) =
        ∫ t in (0:ℝ)..T, s^2/(t+s)^2 := by rw [mul_comm,he]
    _ ≤ s := time_square_integral_le hs hT
    _ = s^2*(1/s) := by field_simp

theorem term_square_eq (s₀ η : ℝ) (j : ℕ) (u : ℝ × Transverse) :
    (term s₀ η j u.1 u.2)^2 =
      (1/(u.1+jetScale s₀ η j)^2)*((shell s₀ η j).indicator (fun _ => (1:ℝ)) u.2) := by
  by_cases h : u.2 ∈ shell s₀ η j <;> simp [term,h]

theorem term_square_integrable {s₀ η T : ℝ} (hs₀ : 0 < s₀) (j : ℕ) :
    Integrable (fun u : ℝ × Transverse => (term s₀ η j u.1 u.2)^2) (timeSpaceVolume T) := by
  have ht := inverse_square_integrable (T := T) (DatumBounds.scale_pos (η := η) hs₀ (j+1))
  have hy : Integrable ((shell s₀ η j).indicator (fun _ => (1:ℝ))) :=
    integrable_indicator_iff (shell_measurable s₀ η j) |>.mpr
      (integrableOn_const (shell_finite s₀ η j).ne)
  simpa only [term_square_eq,timeSpaceVolume,jetScale] using ht.mul_prod hy

theorem term_square_integral_le {s₀ η T : ℝ} (hs₀ : 0 < s₀) (hηmax : η ≤ Real.log 2)
    (hT : 0 ≤ T) (j : ℕ) :
    (∫ u : ℝ × Transverse, (term s₀ η j u.1 u.2)^2 ∂timeSpaceVolume T) ≤
      4*Real.pi*jetScale s₀ η j := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (j+1)
  simp only [term_square_eq,timeSpaceVolume]
  rw [integral_prod_mul (fun t : ℝ => 1/(t+jetScale s₀ η j)^2)
    ((shell s₀ η j).indicator (fun _ => (1:ℝ))),
    integral_indicator (shell_measurable s₀ η j),setIntegral_const,smul_eq_mul,mul_one]
  calc
    _ ≤ (1/jetScale s₀ η j)*(4*Real.pi*(jetScale s₀ η j)^2) :=
      mul_le_mul (inverse_square_integral_le hs hT) (shell_area_le hs₀ hηmax j)
        (measureReal_nonneg) (by positivity)
    _ = _ := by dsimp only [jetScale] at hs ⊢; field_simp

theorem term_square_summable {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η)
    (u : ℝ × Transverse) : Summable (fun j : ℕ => (term s₀ η j u.1 u.2)^2) := by
  apply JetSeries.summable_single_support
  intro i j hij hi
  have hy : u.2 ∈ shell s₀ η i := by
    by_contra h
    exact hi (by simp [term,indicator_of_notMem h])
  have hj : u.2 ∉ shell s₀ η j := fun hj => (disjoint_left.mp (shell_disjoint hs₀ hη hij)) hy hj
  simp [term,indicator_of_notMem hj]

theorem term_square_integrals_summable {s₀ η T : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) :
    Summable (fun j : ℕ => ∫ u : ℝ × Transverse, (term s₀ η j u.1 u.2)^2 ∂timeSpaceVolume T) := by
  have hbase : Summable (DatumBounds.scale s₀ η) := by
    simpa only [pow_one] using DatumBounds.summable_scale_pow s₀ hη 1 (by norm_num)
  have hshift : Summable (fun j : ℕ => DatumBounds.scale s₀ η (j+1)) :=
    (summable_nat_add_iff 1).mpr hbase
  have hs : Summable (fun j : ℕ => 4*Real.pi*jetScale s₀ η j) := hshift.mul_left _
  have hn (j : ℕ) : 0 ≤ ∫ u : ℝ × Transverse, (term s₀ η j u.1 u.2)^2 ∂timeSpaceVolume T :=
    integral_nonneg (fun u => sq_nonneg _)
  exact Summable.of_nonneg_of_le hn (term_square_integral_le hs₀ hηmax hT) hs

theorem squareEnvelope_integrable {s₀ η T : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) :
    Integrable (squareEnvelope s₀ η) (timeSpaceVolume T) := by
  have hm (j : ℕ) : Measurable (fun u : ℝ × Transverse => (term s₀ η j u.1 u.2)^2) :=
    (term_measurable s₀ η j).pow_const 2
  have hi (j : ℕ) : Integrable (fun u : ℝ × Transverse => (term s₀ η j u.1 u.2)^2) (timeSpaceVolume T) :=
    term_square_integrable hs₀ j
  have hsum : Summable (fun j : ℕ => ∫ u : ℝ × Transverse, (term s₀ η j u.1 u.2)^2 ∂timeSpaceVolume T) :=
    term_square_integrals_summable hs₀ hη hηmax hT
  exact JetSeries.integrable_nonnegative_series (μ := timeSpaceVolume T)
    (f := fun j (u : ℝ × Transverse) => (term s₀ η j u.1 u.2)^2)
    hm hi (fun j u => sq_nonneg _) (term_square_summable hs₀.le hη.le) hsum

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # Uniform integrability and vanishing scale tails of the annular square envelope -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem squareEnvelope_nonneg (s₀ η : ℝ) (u : ℝ × Transverse) :
    0 ≤ squareEnvelope s₀ η u := tsum_nonneg (fun _ => sq_nonneg _)

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

section

/-! # Uniform integrability of affine annular moment envelopes in a finite cell -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem momentMajorant_integrable {s₀ η T : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) (A B r : ℝ) :
    Integrable (momentMajorant s₀ η A B r) (timeSpaceVolume T) := by
  have ht : Integrable (fun _ : ℝ => (1:ℝ)) (volume.restrict (Icc (0:ℝ) T)) :=
    integrableOn_const (measure_Icc_lt_top.ne)
  have hy : Integrable ((Metric.ball (0:Transverse) r).indicator (fun _ => (1:ℝ))) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_const (measure_ball_lt_top.ne))
  have hc : Integrable ((cell r).indicator (fun _ => (1:ℝ))) (timeSpaceVolume T) := by
    change Integrable ((cell r).indicator (fun _ => (1:ℝ)))
      ((volume.restrict (Icc (0:ℝ) T)).prod volume)
    convert ht.mul_prod hy using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    by_cases h : u.2 ∈ Metric.ball (0:Transverse) r
    · rw [indicator_of_mem (show u ∈ cell r from h),indicator_of_mem h]
      norm_num
    · rw [indicator_of_notMem (show u ∉ cell r from h),indicator_of_notMem h]
      norm_num
  exact (hc.const_mul (2*A^2)).add
    ((squareEnvelope_integrable hs₀ hη hηmax hT).const_mul (2*B^2))

end BoltzmannNonuniqueness.AnnularEnvelope

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusAnnularIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.MassTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Lifting annular integrable bounds to time times the spatial torus -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem torusChart_measurable : Measurable torusChart := by
  have hm := TorusChart.representative_measurePreserving.measurable
  have ht : Measurable transverse := JetPeriodicDatum.spatialMap_measurePreserving.measurable.fst
  exact measurable_fst.prodMk (ht.comp (hm.comp measurable_snd))

theorem torus_lift_integrable {T : ℝ} {G : ℝ × Transverse → ℝ}
    (hG : Integrable G (timeSpaceVolume T)) :
    Integrable (fun u : ℝ × Position => G (torusChart u)) (timePositionVolume T) := by
  let μt : Measure ℝ := volume.restrict (Icc (0:ℝ) T)
  let a : ℝ → ℝ := (Icc (-1:ℝ) 1).indicator (fun _ => (1:ℝ))
  have ha : Integrable a := (integrable_indicator_iff measurableSet_Icc).mpr
    (integrableOn_const measure_Icc_lt_top.ne)
  have hprod : Integrable (fun z : (ℝ × Transverse) × ℝ => G z.1*a z.2)
      ((μt.prod volume).prod volume) := hG.mul_prod ha
  have he := (measurePreserving_prodAssoc μt (volume : Measure Transverse) (volume : Measure ℝ)).symm
  have hs := he.integrable_comp_of_integrable hprod
  have hv := ((MeasurePreserving.id μt).prod JetPeriodicDatum.spatialMap_measurePreserving).integrable_comp_of_integrable hs
  have hvr := hv.mono_measure (Measure.prod_mono le_rfl
    (Measure.restrict_le_self (μ := (volume : Measure Velocity)) (s := TorusChart.cube)))
  have hp := ((MeasurePreserving.id μt).prod TorusChart.representative_measurePreserving).integrable_comp_of_integrable hvr
  apply hp.congr
  filter_upwards [] with u
  have hc := TorusChart.representative_mem u.2 (Fin.last 2)
  have hac : axial (TorusChart.representative u.2) ∈ Icc (-1:ℝ) 1 := by
    change -(1/2:ℝ) < axial (TorusChart.representative u.2) ∧ axial (TorusChart.representative u.2) ≤ 1/2 at hc
    exact ⟨by linarith [hc.1],by linarith [hc.2]⟩
  change G (u.1,transverse (TorusChart.representative u.2))*a (axial (TorusChart.representative u.2)) = _
  rw [show a (axial (TorusChart.representative u.2)) = 1 from indicator_of_mem hac _,mul_one]
  rfl

theorem torusChart_mem_cell (u : ℝ × Position) : torusChart u ∈ cell 2 := by
  have hc := TorusChart.representative_mem u.2
  have h0 : |TorusChart.representative u.2 0| ≤ 1/2 := abs_le.mpr ⟨(hc 0).1.le,(hc 0).2⟩
  have h1 : |TorusChart.representative u.2 1| ≤ 1/2 := abs_le.mpr ⟨(hc 1).1.le,(hc 1).2⟩
  have hs0 : (TorusChart.representative u.2 0)^2 ≤ (1/2:ℝ)^2  := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr h0
  have hs1 : (TorusChart.representative u.2 1)^2 ≤ (1/2:ℝ)^2  := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr h1
  have hn := EuclideanSpace.real_norm_sq_eq (transverse (TorusChart.representative u.2))
  simp only [Fin.sum_univ_two,transverse,PiLp.toLp_apply] at hn
  change ‖transverse (TorusChart.representative u.2)‖^2 =
    (TorusChart.representative u.2 0)^2+(TorusChart.representative u.2 1)^2 at hn
  change transverse (TorusChart.representative u.2) ∈ Metric.ball 0 2
  rw [Metric.mem_ball,dist_zero_right]
  nlinarith [norm_nonneg (transverse (TorusChart.representative u.2))]

end BoltzmannNonuniqueness.AnnularEnvelope

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CommonMomentEnvelope
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common square-integrable envelope for all capped velocity moments -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.AnnularEnvelope

theorem squareEnvelope_measurable (s₀ η : ℝ) : Measurable (squareEnvelope s₀ η) :=
  Measurable.tsum (fun j => (term_measurable s₀ η j).pow_const 2)

theorem commonMoment_measurable (s₀ η A B : ℝ) : Measurable (commonMoment s₀ η A B) :=
  measurable_const.add (((squareEnvelope_measurable s₀ η).sqrt).const_mul B)

theorem commonMoment_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (s₀ η : ℝ) (u : ℝ × Transverse) : 0 ≤ commonMoment s₀ η A B u :=
  add_nonneg hA (mul_nonneg hB (Real.sqrt_nonneg _))

theorem commonMoment_square_le (s₀ η A B : ℝ) (u : ℝ × Transverse) :
    (commonMoment s₀ η A B u)^2 ≤ 2*A^2+2*B^2*squareEnvelope s₀ η u := by
  have hs := Real.sq_sqrt (squareEnvelope_nonneg s₀ η u)
  have hp := sq_nonneg (A-B*Real.sqrt (squareEnvelope s₀ η u))
  unfold commonMoment
  nlinarith

theorem torus_common_square_integrable {s₀ η T : ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hT : 0 ≤ T) (A B : ℝ) :
    Integrable (fun u : ℝ × Position => (commonMoment s₀ η A B (torusChart u))^2)
      (timePositionVolume T) := by
  have hG := torus_lift_integrable (momentMajorant_integrable hs₀ hη hηmax hT A B 2)
  apply hG.mono' (((commonMoment_measurable s₀ η A B).comp torusChart_measurable).pow_const 2).aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have he := commonMoment_square_le s₀ η A B (torusChart u)
  simpa only [Function.comp_apply,momentMajorant,indicator_of_mem (torusChart_mem_cell u),mul_one] using he

end BoltzmannNonuniqueness.AnnularEnvelope

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakL1Operations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Restricting a kinetic weak limit to any earlier time interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem timePositionVolume_mono {t T : ℝ} (ht : t ≤ T) :
    AnnularEnvelope.timePositionVolume t ≤ AnnularEnvelope.timePositionVolume T := by
  rw [AnnularEnvelope.timePositionVolume,AnnularEnvelope.timePositionVolume]
  exact Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl ht) le_rfl) le_rfl

end BoltzmannNonuniqueness

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

section

/-! # The real mixed-gain estimate for the main cold color -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetMainGain

theorem numerator_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ : ℝ) :
    0 ≤ K * max 1 (α * γ)⁻¹ * JetGaussianProduct.coefficient + JetRemainderSheet.uniformConstant K := by
  have hm : 0 ≤ max 1 (α * γ)⁻¹ := zero_le_one.trans (le_max_left _ _)
  have hJ := JetThermalKernel.bound_pos
  have hL := JetComparisonCoefficient.coefficient_ge_one hK
  unfold JetGaussianProduct.coefficient JetRemainderSheet.uniformConstant
  positivity

end BoltzmannNonuniqueness.JetMainGain

end

end

section

/-! # Scale-uniform mass and Gaussian velocity tails below a cold supersolution -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetEnvelopeGain

theorem momentConstant_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ : ℝ) : 0 ≤ momentConstant K α γ :=
  mul_nonneg (JetMainGain.numerator_nonneg hK α γ) (by positivity)

end BoltzmannNonuniqueness.JetEnvelopeGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HalfGaussianMoment
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

theorem hotConstant_nonneg (q : ℝ) : 0 ≤ hotConstant q :=
  integral_nonneg (fun v => mul_nonneg (weight_pos v).le (H_nonneg q v))

end BoltzmannNonuniqueness.VelocityMoment

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityPolynomialBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

theorem moment_tensor {f : Velocity → ℝ} (hfm : Measurable f) :
    (∫⁻ p : Velocity × Velocity, ENNReal.ofReal (weight p.1*f p.1)*
      ENNReal.ofReal (weight p.2*f p.2)) = moment f*moment f := by
  have hm : Measurable (fun v => ENNReal.ofReal (weight v*f v)) := by unfold weight; fun_prop
  rw [Measure.volume_eq_prod]
  exact MeasureTheory.lintegral_prod_mul hm.aemeasurable hm.aemeasurable

end BoltzmannNonuniqueness.VelocityMoment

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionWeakMarginals
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable physical gain and loss and their equal total mass -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_r80e008_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
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

section

/-! # Slice mass bounds for the physical gain and loss -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem gainDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (gainDensity f) :=
  ((preRate_measurable hf).comp (scatterTriple_measurable.comp
    collisionGrouping.symm.measurable)).stronglyMeasurable.integral_prod_right'.measurable

theorem lossDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (lossDensity f) :=
  ((preRate_measurable hf).comp
    collisionGrouping.symm.measurable).stronglyMeasurable.integral_prod_right'.measurable

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RawPairCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compactness bounds for the unweighted collision pair product -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem pairProduct_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (pairProduct f) := by unfold pairProduct; fun_prop

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PairRepresentative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Pair products depend only on the almost-everywhere density representative -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem pairProduct_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    pairProduct f =ᵐ[μ.prod (volume : Measure (Velocity × Velocity))] pairProduct g := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (pairProduct_measurable hfm) (pairProduct_measurable hgm))).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod he] with x hx
  have hl : ∀ᵐ (y : Velocity × Velocity) ∂((volume : Measure Velocity).prod (volume : Measure Velocity)), f (x,y.1) = g (x,y.1) :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Velocity))
      (ν := (volume : Measure Velocity))).ae hx
  have hr : ∀ᵐ (y : Velocity × Velocity) ∂((volume : Measure Velocity).prod (volume : Measure Velocity)), f (x,y.2) = g (x,y.2) :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Velocity))
      (ν := (volume : Measure Velocity))).ae hx
  rw [Measure.volume_eq_prod]
  filter_upwards [hl,hr] with y hy hz
  simp only [pairProduct,hy,hz]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionDissipation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Full collision terms are independent of the density representative -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_7_r80e008_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
theorem preRate_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    preRate f =ᵐ[(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea] preRate g := by
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := μ.prod (volume : Measure (Velocity × Velocity))) (ν := sphereArea)).ae
      (pairProduct_congr hfm hgm he)
  filter_upwards [hp] with z hz
  change f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) =
    g (z.1.1,z.1.2.1)*g (z.1.1,z.1.2.2) at hz
  simp only [preRate,mul_assoc,hz]

theorem postRate_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    postRate f =ᵐ[(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea] postRate g :=
  (scatterTriple_measurePreserving μ).quasiMeasurePreserving.ae (preRate_congr hfm hgm he)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteDepthKernelOrder
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Recovering the finite absolute-entropy datum class from relative entropy -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem FiniteEntropyDatum.of_relativeEntropy_integrable {f : Density}
    (hn : ∀ᵐ z, 0 ≤ f z) (hf : Integrable f)
    (hE : Integrable (fun z => ‖z.2‖^2*f z))
    (hH : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z))) :
    FiniteEntropyDatum f := by
  have hlog : Integrable (fun z => f z*Real.log (f z)) := by
    have h := ((hH.add (hf.const_mul (1-(3/2:ℝ)*Real.log (2*Real.pi)))).sub
      (hE.const_mul (1/2:ℝ))).sub integrable_maxwellian_phase
    apply h.congr
    filter_upwards [] with z
    simp only [Pi.sub_apply,Pi.add_apply,scalarRelativeEntropy,log_maxwellian]
    ring
  refine ⟨hn,hf.aestronglyMeasurable,?_⟩
  apply ((hf.add hE).add hlog.norm).congr
  filter_upwards [hn] with z hz
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg hz,entropyMoment]
  ring

end BoltzmannNonuniqueness

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

theorem back_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving (fun z : ℝ × Phase => (z.1,flight (-z.1) z.2))
      (μ.prod volume) (μ.prod volume) :=
  (MeasurePreserving.id μ).skew_product (g := fun t p => flight (-t) p)
    (measurable_flight.comp ((measurable_fst.neg).prodMk measurable_snd))
    (ae_of_all _ (fun t => (flight_measurePreserving (-t)).map_eq))

end BoltzmannNonuniqueness.TorusFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyDissipationAverage
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite Gaussian relative entropy controls the required datum class -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem entropyGaussian_integrable : Integrable entropyGaussian := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (by norm_num : 0 < ((1/4:ℂ)).re) 0 (0:Velocity)).norm
  have hg : Integrable (fun v : Velocity => Real.exp (-‖v‖^2/4)) := by
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    funext v
    simp only [zero_mul,add_zero,Complex.norm_exp]
    congr 1
    norm_num
    norm_cast
    ring
  convert hg.const_mul ((2*Real.pi)^(-(3/2:ℝ))*Real.exp (1/4)) using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  dsimp [entropyGaussian,maxwellian]
  simp only [mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem entropy_controls_mass_energy {u : ℝ} (hu : 0 ≤ u) (v : Velocity) :
    (1+‖v‖^2)*u ≤ 4*(scalarRelativeEntropy (maxwellian v) u+entropyGaussian v) := by
  have h := entropyDual_le (maxwellian_pos v) hu ((1+‖v‖^2)/4)
  dsimp [entropyDual,entropyGaussian] at *
  nlinarith [maxwellian_pos v]

theorem finiteEntropy_of_relativeEntropy_integrable {f : Density}
    (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hH : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z))) :
    FiniteEntropyDatum f := by
  have hmajor : Integrable (fun z : Phase =>
      4*(scalarRelativeEntropy (maxwellian z.2) (f z)+entropyGaussian z.2)) :=
    (hH.add (entropyGaussian_integrable.comp_snd volume)).const_mul 4
  have hweight : Integrable (fun z : Phase => (1+‖z.2‖^2)*f z) := by
    apply hmajor.mono' ((measurable_const.add (measurable_snd.norm.pow_const 2)).mul hfm).aestronglyMeasurable
    filter_upwards [] with z
    change ‖(1+‖z.2‖^2)*f z‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hfn z))]
    exact entropy_controls_mass_energy (hfn z) z.2
  have hfi : Integrable f := by
    apply hweight.mono' hfm.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (hfn z)]
    nlinarith [sq_nonneg ‖z.2‖,hfn z]
  have hEi : Integrable (fun z : Phase => ‖z.2‖^2*f z) := by
    apply hweight.mono' ((measurable_snd.norm.pow_const 2).mul hfm).aestronglyMeasurable
    filter_upwards [] with z
    change ‖‖z.2‖^2*f z‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hfn z))]
    nlinarith [hfn z]
  exact FiniteEntropyDatum.of_relativeEntropy_integrable (Filter.Eventually.of_forall hfn) hfi hEi hH

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetFamilyBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual periodic shooting data converge to the common cold datum in L¹ -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetPeriodicDatum

theorem measurable_pullback {f : JetPrototype.Phase → ℝ} (hf : Measurable f) :
    Measurable (pullback f) :=
  hf.comp (phaseMap_measurePreserving.measurable.comp TorusChart.phase_measurePreserving.measurable)

end BoltzmannNonuniqueness.JetPeriodicDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CappedDensitySequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A common velocity moment for the actual capped torus densities -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem momentBase_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (η α q : ℝ) : 0 ≤ momentBase s₀ η K α d₀ q :=
  mul_nonneg (add_nonneg (by norm_num) (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _))
    (hotConstant_nonneg q)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TimeSourceCumulative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The time primitive on the common closed time interval -/

noncomputable section

open MeasureTheory Set Filter

namespace BoltzmannNonuniqueness.Published

variable {P : Type*} [MeasurableSpace P]

omit [MeasurableSpace P] in
theorem timePrimitive_eq_interval {T t : ℝ} (ht : t ∈ Icc 0 T)
    (f : ℝ × P → ℝ) (p : P) :
    timePrimitive (volume.restrict (Icc 0 T)) f (t,p) = ∫ s in 0..t, f (s,p) := by
  change (∫ s, (Iic t).indicator (fun s => f (s,p)) s ∂volume.restrict (Icc 0 T)) = _
  rw [integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  have he : Iic t ∩ Icc 0 T = Icc 0 t := by
    ext s
    simp only [mem_inter_iff,mem_Iic,mem_Icc]
    constructor
    · rintro ⟨hs,h0,_⟩; exact ⟨h0,hs⟩
    · rintro ⟨h0,hs⟩; exact ⟨hs,h0,hs.trans ht.2⟩
  rw [he,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le ht.1]

theorem timePrimitive_measurable (μ : Measure ℝ) [SFinite μ] {f : ℝ × P → ℝ}
    (hf : Measurable f) : Measurable (timePrimitive μ f) := by
  have hm : Measurable (fun z : (ℝ × P) × ℝ => if z.2 ≤ z.1.1 then f (z.2,z.1.2) else 0) :=
    (hf.comp (measurable_snd.prodMk measurable_fst.snd)).ite
      (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CellLocalizedSource
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The finite spacetime measure of the fundamental cell -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusKineticChart

instance instIsFiniteMeasureSpaceTimeBaseVolume (T : ℝ) : IsFiniteMeasure (baseVolume T) := by
  have he := TorusChart.representative_measurePreserving.map_eq
  have : IsFiniteMeasure ((volume : Measure Velocity).restrict TorusChart.cube) := by
    rw [← he]
    exact Measure.isFiniteMeasure_map volume TorusChart.representative
  unfold baseVolume
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.TorusKineticChart

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildRenormalization
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A strongly continuous representative of the constructed local mild solution -/

noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem source_measurable (S : MildCollisionSolution T f₀ g) : Measurable (source g) :=
  (CollisionCompactness.gainDensity_measurable S.measurable).sub
    (CollisionCompactness.lossDensity_measurable S.measurable)

theorem characteristicSource_measurable (S : MildCollisionSolution T f₀ g) :
    Measurable (characteristicSource g) :=
  (S.source_measurable.comp MeasurableEquiv.prodAssoc.symm.measurable).comp
    (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).measurable

theorem evolution_eq_ae (S : MildCollisionSolution T f₀ g) :
    TorusFlight.regroup g =ᵐ[(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
      (fun z => evolution T f₀ g z.1 z.2) := by
  have h := (TorusFlight.back_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae
    S.characteristic
  filter_upwards [h] with z hz
  change TorusFlight.regroup g (z.1,TorusFlight.flight z.1 (TorusFlight.flight (-z.1) z.2)) = _ at hz
  rw [TorusFlight.neg_flight] at hz
  exact hz

theorem evolution_initial (hT : 0 ≤ T) (p : Phase) : evolution T f₀ g 0 p = f₀ p := by
  change f₀ (TorusFlight.flight (-0) p)+Published.timePrimitive (volume.restrict (Icc 0 T))
    (characteristicSource g) (0,TorusFlight.flight (-0) p) = f₀ p
  simp only [neg_zero,TorusFlight.flight_zero]
  rw [Published.timePrimitive_eq_interval ⟨le_rfl,hT⟩,intervalIntegral.integral_same,add_zero]

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveMildRepresentative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nonnegative strongly continuous representative with the exact initial trace -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem evolution_measurable (S : MildCollisionSolution T f₀ g) (hf₀ : Measurable f₀) :
    Measurable (fun z : ℝ × Phase => evolution T f₀ g z.1 z.2) := by
  have hm := (hf₀.comp measurable_snd).add
    (Published.timePrimitive_measurable (volume.restrict (Icc 0 T)) S.characteristicSource_measurable)
  exact hm.comp (TorusFlight.back_measurePreserving (volume.restrict (Icc 0 T))).measurable

theorem positiveEvolution_measurable (S : MildCollisionSolution T f₀ g) (hf₀ : Measurable f₀) :
    Measurable (fun z : ℝ × Phase => positiveEvolution T f₀ g z.1 z.2) :=
  (S.evolution_measurable hf₀).max measurable_const

theorem positiveEvolution_nonnegative (t : ℝ) (p : Phase) : 0 ≤ positiveEvolution T f₀ g t p :=
  le_max_right _ _

theorem positiveEvolution_eq_ae (S : MildCollisionSolution T f₀ g) :
    TorusFlight.regroup g =ᵐ[(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
      (fun z => positiveEvolution T f₀ g z.1 z.2) := by
  filter_upwards [S.evolution_eq_ae] with z hz
  change TorusFlight.regroup g z = max (evolution T f₀ g z.1 z.2) 0
  rw [← hz]
  exact (max_eq_left (S.nonnegative ((z.1,z.2.1),z.2.2))).symm

theorem positiveEvolution_initial (hT : 0 ≤ T) (hf₀ : ∀ p, 0 ≤ f₀ p) (p : Phase) :
    positiveEvolution T f₀ g 0 p = f₀ p := by
  rw [positiveEvolution,evolution_initial hT,max_eq_left (hf₀ p)]

end BoltzmannNonuniqueness.MildCollisionSolution

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_StrongMildRepresentative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collision integrability for the strong nonnegative mild representative -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem positiveDensity_measurable (S : MildCollisionSolution T f₀ g)
    (hf₀ : Measurable f₀) : Measurable (kineticDensity (positiveEvolution T f₀ g)) :=
  (S.positiveEvolution_measurable hf₀).comp MeasurableEquiv.prodAssoc.measurable

theorem positiveDensity_eq_ae (S : MildCollisionSolution T f₀ g) :
    g =ᵐ[(AnnularEnvelope.timePositionVolume T).prod volume]
      kineticDensity (positiveEvolution T f₀ g) :=
  (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae
    S.positiveEvolution_eq_ae

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ExponentialPairIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrable exponential collision pairs from the common squared moment envelope -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem exponentialPair_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (exponentialPair f) := by
  unfold exponentialPair VelocityMoment.weight
  fun_prop

omit [MeasurableSpace X] in
theorem exponentialPair_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : X × (Velocity × Velocity)) : 0 ≤ exponentialPair f z :=
  mul_nonneg (mul_nonneg (VelocityMoment.weight_pos _).le (hf _))
    (mul_nonneg (VelocityMoment.weight_pos _).le (hf _))

theorem exponentialPair_integrable {μ : Measure X} [SFinite μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    {M : X → ℝ} (hMn : ∀ x, 0 ≤ M x) (hMsq : Integrable (fun x => (M x)^2) μ)
    (hbound : ∀ᵐ x ∂μ, VelocityMoment.moment (fun v => f (x,v)) ≤ ENNReal.ofReal (M x)) :
    Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity))) := by
  have hm := exponentialPair_measurable hfm
  have hn := exponentialPair_nonneg hfn
  refine ⟨hm.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ hn)).mpr
  rw [lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  apply lt_of_le_of_lt (lintegral_mono_ae ?_)
    ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x => sq_nonneg (M x)))).mp hMsq.2)
  filter_upwards [hbound] with x hx
  have ht := VelocityMoment.moment_tensor (f := fun v => f (x,v))
    (hfm.comp (measurable_const.prodMk measurable_id))
  have he : (∫⁻ p : Velocity × Velocity, ENNReal.ofReal (exponentialPair f (x,p))) =
      VelocityMoment.moment (fun v => f (x,v))*VelocityMoment.moment (fun v => f (x,v)) := by
    simp only [exponentialPair,ENNReal.ofReal_mul
      (mul_nonneg (VelocityMoment.weight_pos _).le (hfn _))]
    exact ht
  rw [he,pow_two,ENNReal.ofReal_mul (hMn x)]
  exact mul_le_mul' hx hx

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ExtendedProductionScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homogeneity of the extended entropy production, including its infinite cases -/

noncomputable section

open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem extendedEntropyProduction_scale {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    extendedEntropyProduction (c*a) (c*b) = ENNReal.ofReal c*extendedEntropyProduction a b := by
  by_cases hcz : c = 0
  · subst c
    simp [extendedEntropyProduction]
  have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
  have hcn : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hcp)
  by_cases haz : a = 0
  · subst a
    by_cases hbz : b = 0
    · subst b
      simp [extendedEntropyProduction]
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
      simp [extendedEntropyProduction,hbz,(mul_pos hcp hbp).ne',hcn]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  by_cases hbz : b = 0
  · subst b
    simp [extendedEntropyProduction,haz,(mul_pos hcp hap).ne',hcn]
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
  have hcap := mul_pos hcp hap
  have hcbp := mul_pos hcp hbp
  simp only [extendedEntropyProduction,hap,hbp,hcap,hcbp,haz,hbz,hcap.ne',hcbp.ne',
    and_self,↓reduceIte]
  have hdiv : c*a/(c*b) = a/b := by field_simp
  rw [hdiv,← ENNReal.ofReal_mul hc]
  congr 1
  ring

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyDissipationCoordinates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The collision-rate dissipation is the physical entropy dissipation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea : SFinite ((volume : Measure BoltzmannNonuniqueness.Velocity).prod
    BoltzmannNonuniqueness.sphereArea) := Measure.prod.instSFinite

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem kernelEntropyProduction_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (kernelEntropyProduction f) := by
  have hpost : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      f (p.1,scatterLeft p.2.1 p.2.2.1 p.2.2.2)*
        f (p.1,scatterRight p.2.1 p.2.2.1 p.2.2.2)) := by
    unfold scatterLeft scatterRight normalComponent
    fun_prop
  have hpre : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      f (p.1,p.2.1)*f (p.1,p.2.2.1)) := by fun_prop
  have hK : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      collisionKernel p.2.1 p.2.2.1 p.2.2.2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact hK.ennreal_ofReal.mul (measurable_extendedEntropyProduction hpost hpre)

theorem collisionEntropyGrouping_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (collisionEntropyGrouping (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (μ.prod ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea))) :=
  (measurePreserving_prodAssoc μ (volume : Measure Velocity)
    ((volume : Measure Velocity).prod sphereArea)).comp (collisionGrouping_measurePreserving μ)

theorem rateProduction_eq_kernel {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    extendedEntropyProduction (postRate f z) (preRate f z) =
      kernelEntropyProduction f (collisionEntropyGrouping z) := by
  rw [postRate_formula]
  change extendedEntropyProduction
    (collisionKernel z.1.2.1 z.1.2.2 z.2*f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
      f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
    (collisionKernel z.1.2.1 z.1.2.2 z.2*f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)) =
    ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)*extendedEntropyProduction
      (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
      (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))
  simpa only [mul_assoc] using
    extendedEntropyProduction_scale (collisionKernel_nonneg z.1.2.1 z.1.2.2 z.2)
      (mul_nonneg (hf _) (hf _)) (mul_nonneg (hf _) (hf _))

theorem rateDissipation_eq_kernel {μ : Measure X} [SFinite μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    rateDissipation μ f = (4:ℝ≥0∞)⁻¹ * ∫⁻ p, kernelEntropyProduction f p
      ∂μ.prod ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) := by
  unfold rateDissipation
  simp_rw [rateProduction_eq_kernel hf]
  rw [(collisionEntropyGrouping_measurePreserving μ).lintegral_comp
    (kernelEntropyProduction_measurable hfm)]

theorem rateDissipation_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    rateDissipation μ f = rateDissipation μ g := by
  unfold rateDissipation
  congr 1
  apply lintegral_congr_ae
  filter_upwards [postRate_congr hfm hgm he,preRate_congr hfm hgm he] with z hp hq
  rw [hp,hq]

end BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness

theorem kineticDensity_rateDissipation {F : Evolution}
    (hFm : Measurable (fun p : ℝ × Phase => F p.1 p.2))
    (hFn : ∀ t z, 0 ≤ F t z) (T : ℝ) :
    CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume T) (kineticDensity F) =
      ∫⁻ t in Icc (0:ℝ) T, entropyDissipation (F t) := by
  have hkin : Measurable (kineticDensity F) := hFm.comp MeasurableEquiv.prodAssoc.measurable
  rw [CollisionCompactness.rateDissipation_eq_kernel hkin (fun p => hFn _ _)]
  let ν := (volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)
  let G : ℝ × (Position × (Velocity × (Velocity × Sphere))) → ℝ≥0∞ :=
    fun p => CollisionCompactness.kernelEntropyProduction (F p.1) p.2
  have hG : Measurable G := by
    have hm := CollisionCompactness.kernelEntropyProduction_measurable hkin
    change Measurable (fun p : ℝ × (Position × (Velocity × (Velocity × Sphere))) =>
      CollisionCompactness.kernelEntropyProduction (kineticDensity F) ((p.1,p.2.1),p.2.2))
    exact hm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  have he := (measurePreserving_prodAssoc (volume.restrict (Icc (0:ℝ) T))
    (volume : Measure Position) ν).lintegral_comp hG
  change (4:ℝ≥0∞)⁻¹ * ∫⁻ p, G (MeasurableEquiv.prodAssoc p)
    ∂((volume.restrict (Icc (0:ℝ) T)).prod (volume : Measure Position)).prod ν = _
  rw [he,lintegral_prod _ hG.aemeasurable]
  rw [← lintegral_const_mul' _ _ (by norm_num : (4:ℝ≥0∞)⁻¹ ≠ ⊤)]
  rfl

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildConservation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Entropy admissibility of the positive representative of a mild solution -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.MildCollisionSolution

theorem entropy_admissible {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}
    (S : MildCollisionSolution T f₀ g) (hT : 0 < T) (hf₀ : FiniteEntropyDatum f₀)
    (hm₀ : Measurable f₀) (hn₀ : ∀ z, 0 ≤ f₀ z)
    (hH : ∀ t ∈ Ioc 0 T,
      (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2) (positiveEvolution T f₀ g t z)))+
        CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume t) g ≤
          ENNReal.ofReal (relativeEntropy f₀)) :
    (∀ t ∈ Icc 0 T, FiniteEntropyDatum (positiveEvolution T f₀ g t)) ∧
    (∀ t ∈ Icc 0 T, ENNReal.ofReal (relativeEntropy (positiveEvolution T f₀ g t))+
      (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (positiveEvolution T f₀ g s)) ≤
        ENNReal.ofReal (relativeEntropy f₀)) := by
  let F := positiveEvolution T f₀ g
  have hFm := S.positiveEvolution_measurable hm₀
  have hFn : ∀ t z, 0 ≤ F t z := fun t z => positiveEvolution_nonnegative t z
  have hFi t : Measurable (F t) := hFm.comp (measurable_const.prodMk measurable_id)
  have hInitial : F 0 = f₀ := funext (positiveEvolution_initial hT.le hn₀)
  have hHintegrable {t : ℝ} (ht : t ∈ Icc 0 T) :
      Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (F t z)) := by
    by_cases ht0 : t = 0
    · rw [ht0,hInitial]
      exact hf₀.integrable_relativeEntropy.congr (ae_of_all _ (fun z =>
        (scalarRelativeEntropy_eq (maxwellian_pos z.2) _).symm))
    · have htt : t ∈ Ioc 0 T := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
      have hfin : (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2) (F t z))) ≤
          ENNReal.ofReal (relativeEntropy f₀) :=
        (le_add_of_nonneg_right zero_le).trans (hH t htt)
      have hmm : Measurable (fun z : Phase => maxwellian z.2) := by
        unfold maxwellian
        fun_prop
      have hm : Measurable (fun z => scalarRelativeEntropy (maxwellian z.2) (F t z)) := by
        unfold scalarRelativeEntropy
        exact (((hFi t).mul (hFi t).log).sub ((hFi t).mul
          (measurable_const.add hmm.log))).add hmm
      exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
        (ae_of_all _ (fun z => scalarRelativeEntropy_nonneg (maxwellian_pos z.2) (hFn t z)))).mp
          (ne_of_lt (hfin.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨fun t ht => finiteEntropy_of_relativeEntropy_integrable (hFi t) (hFn t) (hHintegrable ht),?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · change ENNReal.ofReal (relativeEntropy (F t))+_ ≤ _
    simp [ht0,hInitial]
  · have htt : t ∈ Ioc 0 T := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
    have he : relativeEntropy (F t) = ∫ z, scalarRelativeEntropy (maxwellian z.2) (F t z) :=
      integral_congr_ae (ae_of_all _ (fun z => (scalarRelativeEntropy_eq (maxwellian_pos z.2) _).symm))
    have hD : CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume t) g =
        CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume t) (kineticDensity F) :=
      CollisionCompactness.rateDissipation_congr S.measurable (S.positiveDensity_measurable hm₀)
        (S.positiveDensity_eq_ae.filter_mono (ae_mono
          (Measure.prod_mono (timePositionVolume_mono ht.2) le_rfl)))
    rw [kineticDensity_rateDissipation hFm hFn t] at hD
    change ENNReal.ofReal (relativeEntropy (F t))+_ ≤ _
    rw [he,ofReal_integral_eq_lintegral_ofReal (hHintegrable ht)
      (ae_of_all _ (fun z => scalarRelativeEntropy_nonneg (maxwellian_pos z.2) (hFn t z))),← hD]
    exact hH t htt

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapCoefficientExtraction
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # An admissible cap limit retaining its actual approximation sequence -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocalControl
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_limit_q80_oai
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (A : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2) :
    Nonempty (CapLocalLimit A) := by
  obtain ⟨φ,g,hφ,hg,S,hpair,htrace⟩ := A.exists_mild_limit_with_traces_and_convergence_q80
    hcarleman hGLPS hDP hs₀ hsmax hη hηmax hK.le hγ hd₀ hq₁ hq₂
  have hH := A.entropy_mild_limit_of_convergence_q80 hcarleman hs₀ hsmax hη hηmax hK hγ hd₀
    hwidth hα.le hαmax hq₁ hq₂ hφ S hpair htrace
  have hdatum := JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα.le hαmax
  have hm : Measurable (JetPeriodicDatum.datum s₀ η K α γ d₀) :=
    JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))
  have hn : ∀ p, 0 ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ p :=
    fun p => JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  obtain ⟨hfinite,hentropy⟩ := S.entropy_admissible A.time_pos hdatum hm hn hH
  have hbound := A.toCompactCapFamily.weak_limit_moment_q80 hs₀ hsmax hη hηmax hK.le hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ hg S.nonnegative
  have hbase := momentBase_nonneg hs₀ hK.le hd₀ η α q
  have hgain := JetEnvelopeGain.momentConstant_nonneg hK.le α γ
  have hE := CollisionCompactness.exponentialPair_integrable S.measurable S.nonnegative
    (fun u => AnnularEnvelope.commonMoment_nonneg hbase hgain s₀ η (AnnularEnvelope.torusChart u))
    (AnnularEnvelope.torus_common_square_integrable hs₀ hη hηmax A.time_pos.le
      (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)) hbound
  exact ⟨⟨φ,hφ,g,hg,S,S.localAdmissible_q80 A.time_pos hm hn hdatum hfinite hentropy hE⟩⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_limit_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.TightCapFamily.exists_limit_q80_oai
