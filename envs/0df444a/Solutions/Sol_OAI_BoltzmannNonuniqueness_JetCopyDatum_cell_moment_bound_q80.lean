-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.cell_moment_bound_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:49:20.664557+00:00
-- url     : https://prove2.me/submissions/25eb9d9d-5816-409e-a6ec-d071dc41f024

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

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

end BoltzmannNonuniqueness.DatumBounds

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
# The monotone implicit axial flow

The cold jet profile in Section 4 of the supplied manuscript is
`σ + α * tanh (γ * z / s)`. Its characteristic map is expanding,
giving a unique implicit velocity at every nonnegative time. The proof uses
continuity, the intermediate value theorem, and monotonicity. No differentiability or
unproved kinetic estimate is assumed.
-/

noncomputable section

open Set Function

namespace BoltzmannNonuniqueness.AxialFlow

/-- The inverse residual is 1-Lipschitz; this estimate does not require differentiation. -/
theorem residual_inverse_lipschitz {σ α γ s t z u v : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    |u - v| ≤ |residual σ α γ s t z u - residual σ α γ s t z v| := by
  rcases le_total u v with huv | hvu
  · have hd := residual_sub_ge (σ := σ) (z := z) hα hγ hs ht huv
    have hf := (residual_strictMono (σ := σ) (z := z) hα hγ hs ht).monotone huv
    rw [abs_of_nonpos (sub_nonpos.mpr huv), abs_of_nonpos (sub_nonpos.mpr hf)]
    linarith
  · have hd := residual_sub_ge (σ := σ) (z := z) hα hγ hs ht hvu
    have hf := (residual_strictMono (σ := σ) (z := z) hα hγ hs ht).monotone hvu
    rw [abs_of_nonneg (sub_nonneg.mpr hvu), abs_of_nonneg (sub_nonneg.mpr hf)]
    exact hd

/-- A thermal perturbation of the implicit equation perturbs the velocity by at most its
amplitude. This is the compressed axial velocity estimate used for cold cores. -/
theorem thermal_velocity_error {σ α γ s t z p δ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t)
    (hp : p = profile σ α γ s (z - t * p) + δ) :
    |p - velocity σ α γ s t z| ≤ |δ| := by
  have h := residual_inverse_lipschitz (σ := σ) (z := z)
    (u := p) (v := velocity σ α γ s t z)
    hα hγ hs ht
  have hp' : residual σ α γ s t z p = δ := by
    dsimp only [residual]
    linarith
  have hu' : residual σ α γ s t z (velocity σ α γ s t z) = 0 :=
    sub_eq_zero.mpr (velocity_spec hα)
  simpa only [hp', hu', sub_zero] using h

theorem foot_characteristic {σ α γ s t z : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    foot σ α γ s t (characteristic σ α γ s t z) = z := by
  apply (characteristic_strictMono hα hγ hs ht).injective
  exact characteristic_foot hα

/-- A particle launched with thermal velocity error `δ` stays within `t * |δ|` in the inverse
spatial coordinate. This is the axial-distance estimate in the transported cold-core barrier. -/
theorem free_flight_foot_error {σ α γ s t z δ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    |foot σ α γ s t (z + t * (profile σ α γ s z + δ)) - z| ≤ t * |δ| := by
  calc
    _ = |foot σ α γ s t (z + t * (profile σ α γ s z + δ)) -
        foot σ α γ s t (characteristic σ α γ s t z)| := by
          rw [foot_characteristic hα hγ hs ht]
    _ ≤ |z + t * (profile σ α γ s z + δ) - characteristic σ α γ s t z| :=
      foot_lipschitz hα hγ hs ht
    _ = |t * δ| := by congr 1; dsimp only [characteristic]; ring
    _ = t * |δ| := by rw [abs_mul, abs_of_nonneg ht]

end BoltzmannNonuniqueness.AxialFlow

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

theorem density_zero {d : ℝ} (hd : 0 < d) (a v : Velocity) (hv : d ≤ ‖v - a‖) :
    density d a v = 0 := by
  have h : 1 ≤ ‖d⁻¹ • (v - a)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
    exact (one_le_inv_mul₀ hd).mpr hv
  simp only [density, scaled, J_zero h, mul_zero]

theorem density_le {d : ℝ} (hd : 0 ≤ d) (a v : Velocity) :
    density d a v ≤ (d ^ 3)⁻¹ * bound :=
  mul_le_mul_of_nonneg_left (J_le _) (inv_nonneg.mpr (pow_nonneg hd _))

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

section

/-! # Explicit points in both stripe-annulus masks -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetMaskNonempty

theorem first_bounds {s : ℝ} (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) :
    0 ≤ first s a ∧ first s a ≤ s := by
  have hsq : s ^ 2 ≤ s / 8 := by nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hsmax)]
  cases a <;> simp only [first, Bool.false_eq_true, ↓reduceIte] <;> constructor <;> nlinarith [sq_nonneg s]

theorem radius_gt {η s : ℝ} (hη : 0 < η) (hs : 0 < s) : s < radius η s := by
  have he := mul_lt_mul_of_pos_right (Real.one_lt_exp_iff.mpr hη) hs
  unfold radius
  linarith

theorem point_norm {η s : ℝ} (hη : 0 < η) (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) :
    ‖point η s a‖ = radius η s := by
  have hfirst := first_bounds hs hsmax a
  have hr := radius_gt hη hs
  have hsqrt : 0 ≤ (radius η s) ^ 2 - (first s a) ^ 2 := by nlinarith
  have hn : ‖point η s a‖ ^ 2 = (radius η s) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [point, Fin.sum_univ_two, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Real.sq_sqrt hsqrt]
    ring
  nlinarith [norm_nonneg (point η s a)]

theorem point_mem {η s : ℝ} (hη : 0 < η) (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) :
    point η s a ∈ mask η s a := by
  have he : 0 < Real.exp η - 1 := by linarith [Real.one_lt_exp_iff.mpr hη]
  have hwidth : gapCoefficient η * s ^ 2 < (Real.exp η - 1) * s / 2 := by
    unfold gapCoefficient
    have hp : 0 < (Real.exp η - 1) * s := mul_pos he hs
    have hm := mul_le_mul_of_nonneg_left hsmax hp.le
    nlinarith
  constructor
  · change s + gapCoefficient η * s ^ 2 < ‖point η s a‖ ∧
      ‖point η s a‖ < Real.exp η * s - gapCoefficient η * s ^ 2
    rw [point_norm hη hs hsmax]
    unfold radius
    constructor <;> linarith
  · change ∃ k : ℤ, ((k : ℝ) + if a then 0 else 1 / 2) * s ^ 2 < (point η s a) 0 ∧
      (point η s a) 0 < ((k : ℝ) + (if a then 0 else 1 / 2) + 1 / 4) * s ^ 2
    refine ⟨0, ?_⟩
    have hs2 := sq_pos_of_pos hs
    cases a <;> simp only [point, first, PiLp.toLp_apply, Matrix.cons_val_zero, Int.cast_zero,
      Bool.false_eq_true, ↓reduceIte] <;> constructor <;> nlinarith

theorem mask_nonempty {η s : ℝ} (hη : 0 < η) (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) :
    (mask η s a).Nonempty := ⟨point η s a, point_mem hη hs hsmax a⟩

end BoltzmannNonuniqueness.JetMaskNonempty

end

end

section

/-! # A uniform Gaussian sum over integer copies in the fundamental cell -/

noncomputable section

open scoped BigOperators

namespace BoltzmannNonuniqueness.JetLatticeGaussian

theorem summable_exponential : Summable exponential := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa only [exponential, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
      Real.summable_exp_neg_nat
  · simpa only [exponential, Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
      Real.summable_exp_neg_nat

theorem pointwise_bound {b R ξ : ℝ} (hb : 1 ≤ b) (hR : R ≤ 1) (hξ : |ξ| ≤ 1) (n : ℤ) :
    gaussian b R ξ n ≤ Real.exp 3 * exponential n := by
  have hr : 0 ≤ max (|ξ - (n : ℝ)| - R) 0 := le_max_right _ _
  have hnr : |(n : ℝ)| ≤ max (|ξ - (n : ℝ)| - R) 0 + 2 := by
    have htri := abs_add_le ((n : ℝ) - ξ) ξ
    rw [sub_add_cancel, abs_sub_comm (n : ℝ) ξ] at htri
    have hm := le_max_left (|ξ - (n : ℝ)| - R) 0
    linarith
  have hsq : |(n : ℝ)| ≤ (max (|ξ - (n : ℝ)| - R) 0) ^ 2 + 3 := by
    nlinarith [sq_nonneg (max (|ξ - (n : ℝ)| - R) 0 - 1 / 2)]
  unfold gaussian exponential
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg (max (|ξ - (n : ℝ)| - R) 0))]

theorem summable_gaussian {b R ξ : ℝ} (hb : 1 ≤ b) (hR : R ≤ 1) (hξ : |ξ| ≤ 1) :
    Summable (gaussian b R ξ) :=
  Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (pointwise_bound hb hR hξ)
    (summable_exponential.mul_left _)

theorem sum_le {b R ξ : ℝ} (hb : 1 ≤ b) (hR : R ≤ 1) (hξ : |ξ| ≤ 1) :
    (∑' n : ℤ, gaussian b R ξ n) ≤ constant := by
  unfold constant
  rw [← tsum_mul_left]
  exact (summable_gaussian hb hR hξ).tsum_le_tsum (pointwise_bound hb hR hξ)
    (summable_exponential.mul_left _)

end BoltzmannNonuniqueness.JetLatticeGaussian

end

end

section

/-! # The three-dimensional integer-copy Gaussian bound -/

noncomputable section

open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetLatticeGaussian

namespace BoltzmannNonuniqueness.JetLatticeProduct


theorem product_eq_exp (b R : ℝ) (x : Fin 3 → ℝ) (n : Lattice) :
    product b R x n = Real.exp (-b * ∑ k : Fin 3, (max (|x k - (n k : ℝ)| - R) 0) ^ 2) := by
  simp only [product, JetLatticeGaussian.gaussian, Fin.sum_univ_three]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem sum_eq (b R : ℝ) (x : Fin 3 → ℝ) :
    (∑' n : Lattice, ENNReal.ofReal (product b R x n)) =
      (∑' n : ℤ, ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 0) n)) *
      (∑' n : ℤ, ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 1) n)) *
      (∑' n : ℤ, ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 2) n)) := by
  rw [← coordinates.symm.tsum_eq (fun n => ENNReal.ofReal (product b R x n))]
  change (∑' p : ℤ × (ℤ × ℤ), ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 0) p.1 *
    JetLatticeGaussian.gaussian b R (x 1) p.2.1 * JetLatticeGaussian.gaussian b R (x 2) p.2.2)) = _
  have he (p : ℤ × (ℤ × ℤ)) :
      ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 0) p.1 *
        JetLatticeGaussian.gaussian b R (x 1) p.2.1 * JetLatticeGaussian.gaussian b R (x 2) p.2.2) =
      ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 0) p.1) *
        ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 1) p.2.1) *
        ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x 2) p.2.2) := by
    have h0 : 0 ≤ JetLatticeGaussian.gaussian b R (x 0) p.1 := Real.exp_nonneg _
    have h1 : 0 ≤ JetLatticeGaussian.gaussian b R (x 1) p.2.1 := Real.exp_nonneg _
    rw [ENNReal.ofReal_mul (mul_nonneg h0 h1), ENNReal.ofReal_mul h0]
  simp_rw [he, ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

theorem sum_le {b R : ℝ} {x : Fin 3 → ℝ} (hb : 1 ≤ b) (hR : R ≤ 1)
    (hx : ∀ k, |x k| ≤ 1) :
    (∑' n : Lattice, ENNReal.ofReal (product b R x n)) ≤ ENNReal.ofReal (JetLatticeGaussian.constant ^ 3) := by
  have hsum (k : Fin 3) : (∑' n : ℤ, ENNReal.ofReal (JetLatticeGaussian.gaussian b R (x k) n)) ≤
      ENNReal.ofReal JetLatticeGaussian.constant := by
    have hn : ∀ n, 0 ≤ JetLatticeGaussian.gaussian b R (x k) n := fun _ => (Real.exp_pos _).le
    rw [← ENNReal.ofReal_tsum_of_nonneg hn (summable_gaussian hb hR (hx k))]
    exact ENNReal.ofReal_le_ofReal (JetLatticeGaussian.sum_le hb hR (hx k))
  have hC : 0 ≤ JetLatticeGaussian.constant := by
    unfold JetLatticeGaussian.constant exponential
    positivity
  rw [sum_eq, ENNReal.ofReal_pow hC]
  calc
    _ ≤ ENNReal.ofReal JetLatticeGaussian.constant * ENNReal.ofReal JetLatticeGaussian.constant *
        ENNReal.ofReal JetLatticeGaussian.constant := mul_le_mul' (mul_le_mul' (hsum 0) (hsum 1)) (hsum 2)
    _ = _ := by ring

end BoltzmannNonuniqueness.JetLatticeProduct

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

theorem tiltConstant_pos : 0 < tiltConstant := by unfold tiltConstant; positivity

theorem polynomial_le_gaussian (p : Velocity) :
    (1 + ‖p‖ ^ 2) ^ (50 : ℕ) ≤ tiltConstant * Real.exp (‖p‖ ^ 2) := by
  have hf : 0 < (Nat.factorial 50 : ℝ) := by positivity
  have h := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (1 + ‖p‖ ^ 2) (by positivity) 50)
  calc
    _ ≤ Real.exp (1 + ‖p‖ ^ 2) * (Nat.factorial 50 : ℝ) := h
    _ = _ := by unfold tiltConstant; rw [Real.exp_add]; ring

end BoltzmannNonuniqueness.VelocityWeight

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

theorem tiltedSheet_mass_le {d L : ℝ} (hd : 0 ≤ d) (hdmax : d ≤ 1 / 8)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (h : AxialMoment ρ L) :
    tiltedSheet d ρ univ ≤ ENNReal.ofReal (4 * L) := by
  have := sheetLaw_isProbabilityMeasure (by positivity : 0 ≤ 2 * d)
    (axialProbability ρ h : Measure ℝ)
  simpa using (tiltedSheet_le_probability hd hdmax h) univ

end BoltzmannNonuniqueness.SheetMeasures

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

end BoltzmannNonuniqueness.HotWeight

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

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarriers
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.JetFreeTransport.flight_zero _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

theorem abs_sign (a : Bool) : |sign a| = 1 := by cases a <;> norm_num [sign]

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

/-! # Thermal and distance bounds on actual free cold-core flights -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCoreFlight

theorem norm_sq_error (v : Velocity) (u : ℝ) :
    ‖v - PlaneChart.join 0 u‖ ^ 2 = ‖transverse v‖ ^ 2 + (axial v - u) ^ 2 := by
  rw [norm_sq_split, PlaneChart.transverse_sub, PlaneChart.transverse_join,
    sub_zero, PlaneChart.axial_sub, PlaneChart.axial_join]

theorem axial_error_bound {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (a : Bool) (p : JetPrototype.Phase) :
    |axial p.2 - axialCenter α γ s t a p| ≤
      |axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2| := by
  apply AxialFlow.thermal_velocity_error hα hγ hs ht
  have he : p.1.2 + t * axial p.2 - t * axial p.2 = p.1.2 := by ring
  rw [he]
  ring

theorem error_le_initial {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (a : Bool) (p : JetPrototype.Phase) :
    ‖error α γ s t a p‖ ≤ ‖p.2 - center α γ s a p.1.2‖ := by
  have h := axial_error_bound hα hγ hs ht a p
  have hsquare : (axial p.2 - axialCenter α γ s t a p) ^ 2 ≤
      (axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2) ^ 2 := by
    nlinarith [sq_abs (axial p.2 - axialCenter α γ s t a p),
      sq_abs (axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2),
      abs_nonneg (axial p.2 - axialCenter α γ s t a p)]
  have hn₁ := norm_sq_error p.2 (axialCenter α γ s t a p)
  have hn₂ := norm_sq_error p.2 (AxialFlow.profile (sign a) α γ s p.1.2)
  change ‖error α γ s t a p‖ ^ 2 = _ at hn₁
  change ‖p.2 - center α γ s a p.1.2‖ ^ 2 = _ at hn₂
  nlinarith [norm_nonneg (error α γ s t a p), norm_nonneg (p.2 - center α γ s a p.1.2)]

theorem error_lt_width {d α γ s t : ℝ} (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (η K : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : density η K α γ s d a p ≠ 0) : ‖error α γ s t a p‖ < d := by
  apply (error_le_initial hα hγ hs ht a p).trans_lt
  have hh : JetThermalLaw.density d (center α γ s a p.1.2) p.2 ≠ 0 := right_ne_zero_of_mul hp
  exact lt_of_not_ge (fun h => hh (JetThermalLaw.density_zero hd _ _ h))

theorem transverse_distance_bound {t : ℝ} (ht : 0 ≤ t) (η K α γ s d : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : density η K α γ s d a p ≠ 0) :
    infDist (p.1.1 + t • transverse p.2) (JetGeometry.mask η s a) ≤ t * ‖transverse p.2‖ := by
  have h := infDist_le_dist_of_mem (JetSupport.initial_spatial_support η K α γ s d a hp).1
    (x := p.1.1 + t • transverse p.2)
  simpa only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht] using h

theorem axial_distance_bound {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    (ht : 0 ≤ t) (η K d : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : density η K α γ s d a p ≠ 0) :
    infDist (AxialFlow.foot (sign a) α γ s t (p.1.2 + t * axial p.2)) (Icc (-(1 / 8 : ℝ)) (1 / 8)) ≤
      t * |axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2| := by
  have hz := (JetSupport.initial_spatial_support η K α γ s d a hp).2
  have hmem : p.1.2 ∈ Icc (-(1 / 8 : ℝ)) (1 / 8) :=
    ⟨(abs_lt.mp hz).1.le, (abs_lt.mp hz).2.le⟩
  have hdist := infDist_le_dist_of_mem hmem
    (x := AxialFlow.foot (sign a) α γ s t (p.1.2 + t * axial p.2))
  rw [Real.dist_eq] at hdist
  apply hdist.trans
  have h := AxialFlow.free_flight_foot_error (σ := sign a) (z := p.1.2)
    (δ := axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2) hα hγ hs ht
  simpa only [add_sub_cancel] using h

theorem distance_square_bound {d α γ s t : ℝ} (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (η K : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : density η K α γ s d a p ≠ 0) :
    infDist (p.1.1 + t • transverse p.2) (JetGeometry.mask η s a) ^ 2 +
      infDist (AxialFlow.foot (sign a) α γ s t (p.1.2 + t * axial p.2))
        (Icc (-(1 / 8 : ℝ)) (1 / 8)) ^ 2 ≤ t ^ 2 * d ^ 2 := by
  have hy := transverse_distance_bound ht η K α γ s d a hp
  have hz := axial_distance_bound hα hγ hs ht η K d a hp
  have hy2 : infDist (p.1.1 + t • transverse p.2) (JetGeometry.mask η s a) ^ 2 ≤
      (t * ‖transverse p.2‖) ^ 2 := by
    gcongr
    exact infDist_nonneg
  have hz2 : infDist (AxialFlow.foot (sign a) α γ s t (p.1.2 + t * axial p.2))
      (Icc (-(1 / 8 : ℝ)) (1 / 8)) ^ 2 ≤
      (t * |axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2|) ^ 2 := by
    gcongr
    exact infDist_nonneg
  have hh : JetThermalLaw.density d (center α γ s a p.1.2) p.2 ≠ 0 := right_ne_zero_of_mul hp
  have hn : ‖p.2 - center α γ s a p.1.2‖ < d :=
    lt_of_not_ge (fun h => hh (JetThermalLaw.density_zero hd _ _ h))
  have hsquare := norm_sq_error p.2 (AxialFlow.profile (sign a) α γ s p.1.2)
  change ‖p.2 - center α γ s a p.1.2‖ ^ 2 = _ at hsquare
  have hi : ‖transverse p.2‖ ^ 2 +
      (axial p.2 - AxialFlow.profile (sign a) α γ s p.1.2) ^ 2 ≤ d ^ 2 := by
    nlinarith [norm_nonneg (p.2 - center α γ s a p.1.2)]
  have hf := mul_le_mul_of_nonneg_left hi (sq_nonneg t)
  rw [mul_pow, sq_abs] at hz2
  nlinarith only [hy2, hz2, hf]

end BoltzmannNonuniqueness.JetCoreFlight

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

theorem spatial_le {K s : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (η γ : ℝ) (a : Bool) (x : Space) :
    spatial η K γ s a x ≤ K / s := by
  by_cases hy : x.1 ∈ JetGeometry.mask η s a
  · by_cases hz : x.2 ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8)
    · simpa only [spatial, axialAmplitude, indicator_of_mem hy, indicator_of_mem hz, one_mul] using
        mul_le_of_le_one_right (div_nonneg hK hs.le) (S_le_one (γ * x.2 / s))
    · simp only [spatial, axialAmplitude, indicator_of_notMem hz, mul_zero]
      exact div_nonneg hK hs.le
  · simp only [spatial, indicator_of_notMem hy, zero_mul]
    exact div_nonneg hK hs.le

theorem initial_density_bound {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 ≤ d)
    (η α γ : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    density η K α γ s d a p ≤ (K / s) * (d ^ 3)⁻¹ * JetThermalKernel.bound := by
  calc
    _ ≤ (K / s) * JetThermalLaw.density d (center α γ s a p.1.2) p.2 :=
      mul_le_mul_of_nonneg_right (spatial_le hK hs η γ a p.1) (JetThermalLaw.density_nonneg hd _ _)
    _ ≤ (K / s) * ((d ^ 3)⁻¹ * JetThermalKernel.bound) :=
      mul_le_mul_of_nonneg_left (JetThermalLaw.density_le hd _ _) (div_nonneg hK hs.le)
    _ = _ := by ring

theorem flight_exponent_lower {d α γ s t : ℝ} (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 < t) (htmax : t ≤ 2) (η K : ℝ) (a : Bool) {p : JetPrototype.Phase}
    (hp : density η K α γ s d a p ≠ 0) : -3 ≤ exponent η α γ s d t a (flight t p) := by
  have hr := error_lt_width hd hα hγ hs ht.le η K a hp
  have hp2 := distance_square_bound hd hα hγ hs ht.le η K a hp
  have hr2 : ‖error α γ s t a p‖ ^ 2 ≤ d ^ 2 := by
    nlinarith [norm_nonneg (error α γ s t a p)]
  have hk : (2 - t) * ‖error α γ s t a p‖ ^ 2 / d ^ 2 ≤ 2 - t := by
    apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    exact mul_le_mul_of_nonneg_left hr2 (sub_nonneg.mpr htmax)
  have hx : (1 / 8 : ℝ) * distanceSquared η α γ s t a (flight t p).1 / (d ^ 2 * t) ≤ t / 8 := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hd) ht)).mpr
    change (1 / 8 : ℝ) * (_ + _) ≤ _
    dsimp only [flight]
    nlinarith only [hp2]
  change -3 ≤ t - (2 - t) * ‖error α γ s t a p‖ ^ 2 / d ^ 2 - _
  nlinarith only [hk, hx, ht]

theorem barrier_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (η α γ t : ℝ) (a : Bool) (p : JetPrototype.Phase) : 0 ≤ barrier η K α γ s d t a p := by
  unfold barrier
  have := JetThermalKernel.bound_pos
  positivity

theorem free_core_le_barrier {K d α γ s t : ℝ} (hK : 0 ≤ K) (hd : 0 < d) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 < t) (htmax : t ≤ 2)
    (η : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    density η K α γ s d a p ≤ barrier η K α γ s d t a (flight t p) := by
  by_cases hp : density η K α γ s d a p = 0
  · rw [hp]
    exact barrier_nonneg hK hs.le hd.le η α γ t a _
  have he := Real.exp_le_exp.mpr (flight_exponent_lower hd hα hγ hs ht htmax η K a hp)
  have hc : 0 ≤ (Real.exp 3 * JetThermalKernel.bound) * (K / s) * (d ^ 3)⁻¹ := by
    have := JetThermalKernel.bound_pos
    positivity
  calc
    _ ≤ (K / s) * (d ^ 3)⁻¹ * JetThermalKernel.bound := initial_density_bound hK hs hd.le η α γ a p
    _ = (Real.exp 3 * JetThermalKernel.bound) * (K / s) * (d ^ 3)⁻¹ * Real.exp (-3) := by
      have hx : Real.exp (3 : ℝ) * Real.exp (-3) = 1 := by rw [← Real.exp_add]; norm_num
      calc
        _ = ((K / s) * (d ^ 3)⁻¹ * JetThermalKernel.bound) *
            (Real.exp 3 * Real.exp (-3)) := by rw [hx, mul_one]
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he hc

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

section

/-! # Gaussian decay of a cold barrier away from its spatial core -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetGaussianEscape

theorem centered_gaussian_le {b : ℝ} (hb : 8 ≤ b) (u v : Velocity) :
    Real.exp (-b * ‖v - u‖ ^ 2) ≤
      Real.exp (8 * ‖u‖ ^ 2) * Real.exp (-4 * ‖v‖ ^ 2) := by
  have hn : ‖v‖ ≤ ‖v - u‖ + ‖u‖ := by
    simpa only [sub_add_cancel] using norm_add_le (v - u) u
  have hs : ‖v‖ ^ 2 ≤ 2 * ‖v - u‖ ^ 2 + 2 * ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg v, norm_nonneg (v - u), norm_nonneg u,
      sq_nonneg (‖v - u‖ - ‖u‖)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v - u‖)]

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

theorem barrier_velocity_decay {K α s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1 / 16) (htmax : t ≤ 1)
    (η γ : ℝ) (a : Bool) (x : Space) (v : Velocity) :
    barrier η K α γ s d t a (x, v) ≤
      constant α * (K / s) * (d ^ 3)⁻¹ *
        Real.exp (-(1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t)) *
          Real.exp (-4 * ‖v‖ ^ 2) := by
  have hb : 8 ≤ (2 - t) / d ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
    nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hdmax)]
  have hsiga : |sign a| = 1 := by cases a <;> norm_num [sign]
  have hu := AxialTransport.velocity_abs_le (σ := sign a) (γ := γ) (s := s) (t := t) (z := x.2) hα
  rw [hsiga] at hu
  have hu2 : ‖centerVelocity α γ s t a x‖ ^ 2 ≤ (1 + α) ^ 2 := by
    rw [centerVelocity, PlaneChart.norm_join_sq, norm_zero, zero_pow (by norm_num), zero_add]
    nlinarith [sq_abs (AxialFlow.velocity (sign a) α γ s t x.2),
      abs_nonneg (AxialFlow.velocity (sign a) α γ s t x.2)]
  have he := (centered_gaussian_le hb (centerVelocity α γ s t a x) v).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith :
      8 * ‖centerVelocity α γ s t a x‖ ^ 2 ≤ 8 * (1 + α) ^ 2)) (Real.exp_nonneg _))
  rw [JetBarrierCollision.barrier_eq_density hd, GaussianFrequency.density_eq_gaussian hd]
  unfold gaussian
  apply (mul_le_mul_of_nonneg_left he (mul_nonneg
    (JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x) (by positivity))).trans
  unfold JetBarrierCollision.massScale constant
  have het : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr htmax
  rw [sub_eq_add_neg, Real.exp_add]
  have h4 : Real.exp 3 * Real.exp 1 = Real.exp 4 := by rw [← Real.exp_add]; norm_num
  calc
    _ = (Real.exp 3 * Real.exp t) * JetThermalKernel.bound * (K / s) * (d ^ 3)⁻¹ *
        Real.exp (-(1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t)) *
        Real.exp (8 * (1 + α) ^ 2) * Real.exp (-4 * ‖v‖ ^ 2) := by ring_nf
    _ ≤ (Real.exp 3 * Real.exp 1) * JetThermalKernel.bound * (K / s) * (d ^ 3)⁻¹ *
        Real.exp (-(1 / 8 : ℝ) * distanceSquared η α γ s t a x / (d ^ 2 * t)) *
        Real.exp (8 * (1 + α) ^ 2) * Real.exp (-4 * ‖v‖ ^ 2) := by
      gcongr
      exact JetThermalKernel.bound_pos.le
    _ = _ := by rw [h4]; ring

end BoltzmannNonuniqueness.JetGaussianEscape

end

end

section

/-! # Positive spatial distance for every nonmain cold label -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetEscapeGeometry

theorem transverse_distance {η s : ℝ} (hη : 0 < η) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (a : Bool) {y : Transverse} (hy : y ∉ enlargement η s a) :
    enlargementWidth η s ≤ infDist y (mask η s a) := by
  apply le_of_not_gt
  intro hd
  apply hy
  exact thickening_subset_cthickening (enlargementWidth η s) (mask η s a)
    ((mem_thickening_iff_infDist_lt
    (JetMaskNonempty.mask_nonempty hη hs hsmax a)).mpr hd)

theorem axial_distance {α t : ℝ} (hα : 0 ≤ α) (hαmax : α ≤ 1) (ht : 0 ≤ t)
    (γ s z : ℝ) (a : Bool) (hz : 1 / 8 + 2 * t + 1 / 16 < |z|) :
    (1 / 16 : ℝ) ≤ infDist (AxialFlow.foot (sign a) α γ s t z) (Icc (-(1 / 8 : ℝ)) (1 / 8)) := by
  have hsiga : |sign a| = 1 := by cases a <;> norm_num [sign]
  have hu := AxialTransport.velocity_abs_le (σ := sign a) (γ := γ) (s := s) (t := t) (z := z) hα
  rw [hsiga] at hu
  have hu' : t * |AxialFlow.velocity (sign a) α γ s t z| ≤ 2 * t := by
    nlinarith [mul_le_mul_of_nonneg_left hu ht, mul_le_mul_of_nonneg_left hαmax ht]
  have htri : |z| ≤ |AxialFlow.foot (sign a) α γ s t z| + t * |AxialFlow.velocity (sign a) α γ s t z| := by
    have h := abs_add_le (AxialFlow.foot (sign a) α γ s t z)
      (t * AxialFlow.velocity (sign a) α γ s t z)
    simp only [AxialFlow.foot, sub_add_cancel, abs_mul, abs_of_nonneg ht] at h
    exact h
  apply (le_infDist (show (Icc (-(1 / 8 : ℝ)) (1 / 8)).Nonempty from ⟨0, by norm_num⟩)).mpr
  intro r hr
  have hrabs : |r| ≤ (1 / 8 : ℝ) := abs_le.mpr hr
  have htri' := abs_add_le (AxialFlow.foot (sign a) α γ s t z - r) r
  rw [sub_add_cancel] at htri'
  rw [Real.dist_eq]
  linarith

theorem width_le {η s : ℝ} (hηmax : η ≤ Real.log 2)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) : enlargementWidth η s ≤ 1 / 16 := by
  have hc := gapCoefficient_le hηmax
  have hs2 : s ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hs.le hsmax 2
  unfold enlargementWidth
  calc
    _ ≤ ((1 / 16 : ℝ) / 4) * (1 / 8) ^ 2 :=
      mul_le_mul (div_le_div_of_nonneg_right hc (by norm_num)) hs2 (sq_nonneg s) (by norm_num)
    _ ≤ _ := by norm_num

theorem distance_lower_bound {η α s t : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8) (ht : 0 ≤ t)
    (γ : ℝ) (a : Bool) (x : Space)
    (hout : ¬(x.1 ∈ enlargement η s a ∧ |x.2| ≤ 1 / 8 + 2 * t + 1 / 16)) :
    (enlargementWidth η s) ^ 2 ≤ distanceSquared η α γ s t a x := by
  have hδ := (enlargementWidth_pos hη hs).le
  by_cases hy : x.1 ∈ enlargement η s a
  · have hz : 1 / 8 + 2 * t + 1 / 16 < |x.2| := lt_of_not_ge (fun hz => hout ⟨hy, hz⟩)
    have hd := (width_le hηmax hs hsmax).trans (axial_distance hα hαmax ht γ s x.2 a hz)
    unfold distanceSquared
    have hsq := (sq_le_sq₀ hδ (show 0 ≤ infDist (AxialFlow.foot (sign a) α γ s t x.2)
      (Icc (-(1 / 8 : ℝ)) (1 / 8)) from infDist_nonneg)).mpr hd
    nlinarith only [hsq, sq_nonneg (infDist x.1 (mask η s a))]
  · have hd := transverse_distance hη hs hsmax a hy
    unfold distanceSquared
    have hsq := (sq_le_sq₀ hδ (show 0 ≤ infDist x.1 (mask η s a) from infDist_nonneg)).mpr hd
    nlinarith only [hsq, sq_nonneg (infDist (AxialFlow.foot (sign a) α γ s t x.2)
      (Icc (-(1 / 8 : ℝ)) (1 / 8)))]

end BoltzmannNonuniqueness.JetEscapeGeometry

end

end

section

/-! # Arbitrary polynomial decay of the escaped-scale exponential -/

noncomputable section

namespace BoltzmannNonuniqueness.JetEscapePower

theorem exp_neg_le {x : ℝ} (hx : 0 < x) (m : ℕ) :
    Real.exp (-x) ≤ (m.factorial : ℝ) / x ^ m := by
  have hfact : 0 < (m.factorial : ℝ) := by positivity
  have hp := (div_le_iff₀ hfact).mp (Real.pow_div_factorial_le_exp x hx.le m)
  rw [Real.exp_neg]
  apply (le_div_iff₀ (pow_pos hx m)).mpr
  calc
    _ ≤ (Real.exp x)⁻¹ * (Real.exp x * (m.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_ne_zero x), one_mul]

theorem tail_nonneg {s : ℝ} (hs : 0 ≤ s) (β t : ℝ) : 0 ≤ tail β s t := by
  unfold tail
  positivity

theorem tail_bound {β s t : ℝ} (hβ : 0 < β) (hs : 0 < s) (ht : 0 < t)
    (m : ℕ) (hm : 31 ≤ 16 * m) :
    tail β s t ≤ ((m.factorial : ℝ) / β ^ m) * t ^ m * s ^ (16 * m - 31) := by
  have hx : 0 < β / (s ^ 16 * t) := by positivity
  have h := mul_le_mul_of_nonneg_left (exp_neg_le hx m) (by positivity : 0 ≤ (s ^ 31)⁻¹)
  rw [← neg_div] at h
  change tail β s t ≤ _ at h
  apply h.trans_eq
  rw [div_pow, mul_pow]
  have hpow : s ^ (16 * m) = s ^ (16 * m - 31) * s ^ 31 := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  rw [← pow_mul, hpow]
  field_simp


theorem summable_tails {β s₀ η t : ℝ} (hβ : 0 < β) (hs₀ : 0 < s₀)
    (hη : 0 < η) (ht : 0 < t) :
    Summable (fun j : ℕ => tail β (DatumBounds.scale s₀ η j) t) := by
  have hm := (DatumBounds.summable_scale_pow s₀ hη 1 (by norm_num)).mul_left
    (((2 : ℕ).factorial : ℝ) / β ^ 2 * t ^ 2)
  apply Summable.of_nonneg_of_le
    (fun j => tail_nonneg (DatumBounds.scale_pos (η := η) hs₀ j).le β t) _ hm
  intro j
  simpa only [Nat.factorial_two, Nat.cast_ofNat, Nat.reduceMul, Nat.reduceSub, pow_one] using
    tail_bound hβ (DatumBounds.scale_pos (η := η) hs₀ j) ht 2 (by norm_num)

end BoltzmannNonuniqueness.JetEscapePower

end

end

section

/-! # The escaped barrier has the actual s⁻³¹ exp(-β/(s¹⁶t)) tail -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetEscapedBarrier

theorem rate_pos {η d₀ : ℝ} (hη : 0 < η) (hd₀ : 0 < d₀) : 0 < rate η d₀ := by
  have := gapCoefficient_pos hη
  unfold rate
  positivity

end BoltzmannNonuniqueness.JetEscapedBarrier

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetPeriodicDatum
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A coordinate box lower bound for periodic barrier distances -/

noncomputable section

open Set Metric
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetSpatialBox

theorem mask_norm_le_one {η s : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) {y : Transverse} (hy : y ∈ mask η s a) :
    ‖y‖ ≤ 1 := by
  have hn := hy.1.2
  have hc := (gapCoefficient_pos hη).le
  have he : Real.exp η ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hηmax
  have he' := mul_le_mul_of_nonneg_right he hs.le
  nlinarith [sq_nonneg s, mul_nonneg hc (sq_nonneg s)]

theorem transverse_component {η s : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (a : Bool) (x : Transverse) (k : Fin 2) :
    max (|x k| - 1) 0 ≤ infDist x (mask η s a) := by
  apply (le_infDist (JetMaskNonempty.mask_nonempty hη hs hsmax a)).mpr
  intro y hy
  have hyc : |y k| ≤ 1 := by
    have h := PiLp.norm_apply_le y k
    rw [Real.norm_eq_abs] at h
    exact h.trans (mask_norm_le_one hη hηmax hs hsmax a hy)
  have hdc : |x k - y k| ≤ ‖x - y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x - y) k
  have htri := abs_add_le (x k - y k) (y k)
  rw [sub_add_cancel] at htri
  rw [dist_eq_norm]
  exact max_le (by linarith) (norm_nonneg _)

theorem axial_component {α t : ℝ} (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) (γ s z : ℝ) (a : Bool) :
    max (|z| - 1) 0 ≤ infDist (AxialFlow.foot (sign a) α γ s t z)
      (Icc (-(1 / 8 : ℝ)) (1 / 8)) := by
  have hsiga : |sign a| = 1 := by cases a <;> norm_num [sign]
  have hu := AxialTransport.velocity_abs_le (σ := sign a) (γ := γ) (s := s) (t := t) (z := z) hα
  rw [hsiga] at hu
  have hu' : t * |AxialFlow.velocity (sign a) α γ s t z| ≤ 2 * t := by
    nlinarith [mul_le_mul_of_nonneg_left hu ht, mul_le_mul_of_nonneg_left hαmax ht]
  have htri := abs_add_le (AxialFlow.foot (sign a) α γ s t z)
    (t * AxialFlow.velocity (sign a) α γ s t z)
  simp only [AxialFlow.foot, sub_add_cancel, abs_mul, abs_of_nonneg ht] at htri
  change |z| ≤ |AxialFlow.foot (sign a) α γ s t z| + t * |AxialFlow.velocity (sign a) α γ s t z| at htri
  apply (le_infDist (show (Icc (-(1 / 8 : ℝ)) (1 / 8)).Nonempty from ⟨0, by norm_num⟩)).mpr
  intro r hr
  have hrabs : |r| ≤ (1 / 8 : ℝ) := abs_le.mpr hr
  have htri' := abs_add_le (AxialFlow.foot (sign a) α γ s t z - r) r
  rw [sub_add_cancel] at htri'
  rw [Real.dist_eq]
  exact max_le (by linarith) (abs_nonneg _)

theorem coordinate_bound {η α s t : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) (γ : ℝ) (a : Bool) (x : Velocity) (n : Lattice) :
    (∑ k : Fin 3, (gap x n k) ^ 2) ≤ 2 * distanceSquared η α γ s t a (shifted x n) := by
  have h0 := transverse_component hη hηmax hs hsmax a (shifted x n).1 0
  have h1 := transverse_component hη hηmax hs hsmax a (shifted x n).1 1
  have h2 := axial_component hα hαmax ht htmax γ s (shifted x n).2 a
  change gap x n 0 ≤ infDist (shifted x n).1 (mask η s a) at h0
  change gap x n 1 ≤ infDist (shifted x n).1 (mask η s a) at h1
  change gap x n 2 ≤ infDist (AxialFlow.foot (sign a) α γ s t (shifted x n).2)
    (Icc (-(1 / 8 : ℝ)) (1 / 8)) at h2
  have h0sq := (sq_le_sq₀ (le_max_right _ _) (show 0 ≤ infDist (shifted x n).1 (mask η s a)
    from infDist_nonneg)).mpr h0
  have h1sq := (sq_le_sq₀ (le_max_right _ _) (show 0 ≤ infDist (shifted x n).1 (mask η s a)
    from infDist_nonneg)).mpr h1
  have h2sq := (sq_le_sq₀ (le_max_right _ _) (show 0 ≤ infDist (AxialFlow.foot (sign a) α γ s t (shifted x n).2)
    (Icc (-(1 / 8 : ℝ)) (1 / 8)) from infDist_nonneg)).mpr h2
  rw [Fin.sum_univ_three]
  unfold distanceSquared gap
  nlinarith only [h0sq, h1sq, h2sq, sq_nonneg (infDist (AxialFlow.foot (sign a) α γ s t (shifted x n).2)
    (Icc (-(1 / 8 : ℝ)) (1 / 8)))]

end BoltzmannNonuniqueness.JetSpatialBox

end

end

section

/-! # The free cold core in Eulerian coordinates -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetFreeTransport

theorem flight_add (t r : ℝ) (p : JetPrototype.Phase) :
    flight t (flight r p) = flight (t + r) p := by
  apply Prod.ext
  · apply Prod.ext
    · dsimp only [flight]
      module
    · dsimp only [flight]
      ring
  · rfl

@[simp] theorem flight_neg (t : ℝ) (p : JetPrototype.Phase) : flight t (flight (-t) p) = p := by
  rw [flight_add, add_neg_cancel, flight_zero]

@[simp] theorem neg_flight (t : ℝ) (p : JetPrototype.Phase) : flight (-t) (flight t p) = p := by
  rw [flight_add, neg_add_cancel, flight_zero]

theorem free_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hd : 0 ≤ d)
    (η α γ t : ℝ) (a : Bool) (p : JetPrototype.Phase) : 0 ≤ free η K α γ s d t a p :=
  density_nonneg hK hs hd η α γ a _

theorem free_le_barrier {K d α γ s t : ℝ} (hK : 0 ≤ K) (hd : 0 < d) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 < t) (htmax : t ≤ 2)
    (η : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    free η K α γ s d t a p ≤ barrier η K α γ s d t a p := by
  have h := free_core_le_barrier hK hd hα hγ hs ht htmax η a (flight (-t) p)
  simpa only [free, flight_neg] using h

theorem measurable_free (η K α γ s d t : ℝ) (a : Bool) :
    Measurable (free η K α γ s d t a) := by
  apply (measurable_density η K α γ s d a).comp
  unfold flight transverse axial
  fun_prop

end BoltzmannNonuniqueness.JetFreeTransport

end

end

section

/-! # Gaussian summation over the actual periodic-copy distances -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetSpatialBox
open BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetLatticeTail

theorem pointwise_bound {η α s t B : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) (hB : 0 ≤ B)
    (γ : ℝ) (a : Bool) (x : Velocity) (n : Lattice) :
    Real.exp (-B * distanceSquared η α γ s t a (shifted x n)) ≤
      JetLatticeProduct.product (B / 2) 1 x n := by
  rw [JetLatticeProduct.product_eq_exp]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left
    (coordinate_bound hη hηmax hα hαmax hs hsmax ht htmax γ a x n) hB
  unfold gap at h
  linarith

theorem sum_bound {η α s t B : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) (hB : 2 ≤ B)
    (γ : ℝ) (a : Bool) (x : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    (∑' n : Lattice, ENNReal.ofReal (Real.exp (-B * distanceSquared η α γ s t a (shifted x n)))) ≤
      ENNReal.ofReal (JetLatticeGaussian.constant ^ 3) := by
  apply (ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal
    (pointwise_bound hη hηmax hα hαmax hs hsmax ht htmax (by linarith) γ a x n))).trans
  exact JetLatticeProduct.sum_le (by linarith) (by norm_num) hx

theorem escaped_sum_bound {η α s t B : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) (hB : 2 ≤ B)
    (γ : ℝ) (a : Bool) (x : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    (∑' n : Lattice, {n | outside η s t a x n}.indicator
      (fun n => ENNReal.ofReal (Real.exp (-(2 * B) * distanceSquared η α γ s t a (shifted x n)))) n) ≤
      ENNReal.ofReal (Real.exp (-B * (enlargementWidth η s) ^ 2)) *
        ENNReal.ofReal (JetLatticeGaussian.constant ^ 3) := by
  have hpoint (n : Lattice) : {n | outside η s t a x n}.indicator
      (fun n => ENNReal.ofReal (Real.exp (-(2 * B) * distanceSquared η α γ s t a (shifted x n)))) n ≤
      ENNReal.ofReal (Real.exp (-B * (enlargementWidth η s) ^ 2)) *
        ENNReal.ofReal (Real.exp (-B * distanceSquared η α γ s t a (shifted x n))) := by
    by_cases hn : outside η s t a x n
    · rw [Set.indicator_of_mem hn, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hdist := JetEscapeGeometry.distance_lower_bound hη hηmax hα hαmax hs hsmax ht γ a (shifted x n) hn
      nlinarith [mul_le_mul_of_nonneg_left hdist (by linarith : 0 ≤ B)]
    · rw [Set.indicator_of_notMem hn]
      exact bot_le
  apply (ENNReal.tsum_le_tsum hpoint).trans
  rw [ENNReal.tsum_mul_left]
  exact mul_le_mul' le_rfl (sum_bound hη hηmax hα hαmax hs hsmax ht htmax hB γ a x hx)

end BoltzmannNonuniqueness.JetLatticeTail

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

/-! # The escaped Gaussian barrier summed over all periodic copies -/

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

namespace BoltzmannNonuniqueness.JetEscapedCopies

theorem halfRate_large {d t : ℝ} (hd : 0 < d) (hdmax : d ≤ 1 / 16)
    (ht : 0 < t) (htmax : t ≤ 1) : 2 ≤ halfRate d t := by
  unfold halfRate
  apply (le_div_iff₀ (by positivity : 0 < 16 * d ^ 2 * t)).mpr
  have hsq : d ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := pow_le_pow_left₀ hd.le hdmax 2
  have hprod := mul_le_mul hsq htmax ht.le (by norm_num : (0 : ℝ) ≤ (1 / 16) ^ 2)
  nlinarith

theorem rate_identity {d₀ s t : ℝ} (hd₀ : 0 < d₀) (hs : 0 < s) (ht : 0 < t) (η : ℝ) :
    halfRate (d₀ * s ^ 10) t * (enlargementWidth η s) ^ 2 =
      (JetEscapedBarrier.rate η d₀ / 2) / (s ^ 16 * t) := by
  unfold halfRate enlargementWidth JetEscapedBarrier.rate
  field_simp
  ring

theorem copy_sum_bound {η K α s d₀ t : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (hd₀ : 0 < d₀) (hwidth : d₀ * s ^ 10 ≤ 1 / 16) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (γ : ℝ) (a : Bool) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    (∑' n : Lattice, {n | outside η s t a x n}.indicator
      (fun n => ENNReal.ofReal (barrier η K α γ s (d₀ * s ^ 10) t a (shifted x n, v))) n) ≤
      ENNReal.ofReal (JetEscapedBarrier.coefficient α K d₀ *
        JetEscapePower.tail (JetEscapedBarrier.rate η d₀ / 2) s t * Real.exp (-4 * ‖v‖ ^ 2)) *
          ENNReal.ofReal (JetLatticeGaussian.constant ^ 3) := by
  have hd : 0 < d₀ * s ^ 10 := by positivity
  let B := halfRate (d₀ * s ^ 10) t
  let A := JetGaussianEscape.constant α * (K / s) * ((d₀ * s ^ 10) ^ 3)⁻¹ * Real.exp (-4 * ‖v‖ ^ 2)
  have hA : 0 ≤ A := by
    unfold A JetGaussianEscape.constant
    have := JetThermalKernel.bound_pos
    positivity
  have hB : 2 ≤ B := halfRate_large hd hwidth ht (by linarith)
  have he (D : ℝ) : -(1 / 8 : ℝ) * D / ((d₀ * s ^ 10) ^ 2 * t) = -(2 * B) * D := by
    unfold B halfRate
    field_simp
    ring
  have hpoint (n : Lattice) : {n | outside η s t a x n}.indicator
      (fun n => ENNReal.ofReal (barrier η K α γ s (d₀ * s ^ 10) t a (shifted x n, v))) n ≤
      ENNReal.ofReal A * {n | outside η s t a x n}.indicator
        (fun n => ENNReal.ofReal (Real.exp (-(2 * B) * distanceSquared η α γ s t a (shifted x n)))) n := by
    by_cases hn : outside η s t a x n
    · rw [indicator_of_mem hn, indicator_of_mem hn, ← ENNReal.ofReal_mul hA]
      apply ENNReal.ofReal_le_ofReal
      have hb := JetGaussianEscape.barrier_velocity_decay hK hα hs hd hwidth (by linarith : t ≤ 1)
        η γ a (shifted x n) v
      rw [he] at hb
      apply hb.trans_eq
      unfold A
      ring
    · have hn' : n ∉ {n | outside η s t a x n} := hn
      simp only [indicator_of_notMem hn', mul_zero, le_refl]
  apply (ENNReal.tsum_le_tsum hpoint).trans
  rw [ENNReal.tsum_mul_left]
  apply (mul_le_mul' le_rfl (escaped_sum_bound hη hηmax hα hαmax hs hsmax ht.le htmax hB γ a x hx)).trans_eq
  rw [← mul_assoc, ← ENNReal.ofReal_mul hA]
  congr 1
  congr 1
  rw [neg_mul, show B * (enlargementWidth η s) ^ 2 =
    (JetEscapedBarrier.rate η d₀ / 2) / (s ^ 16 * t) from rate_identity hd₀ hs ht η, ← neg_div]
  unfold A JetEscapedBarrier.coefficient JetEscapePower.tail
  field_simp

end BoltzmannNonuniqueness.JetEscapedCopies

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

theorem le_twice_barrier {K s d α γ t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : epsilon K s d ≤ 1) (η : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    U η K α γ s d t a p ≤ 2 * barrier η K α γ s d t a p := by
  have hf := free_le_barrier hK hd hα hγ hs ht (htmax.trans (by norm_num)) η a p
  have hm := mul_le_mul_of_nonneg_right hε (barrier_nonneg hK hs.le hd.le η α γ t a p)
  unfold U
  linarith

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

/-! # Replacing the annular part of the full oscillating mask -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem mask_indicator_factor (η s : ℝ) (a : Bool) (y : Transverse) :
    (mask η s a).indicator (fun _ => (1:ℝ)) y =
      (annularCore η s).indicator (fun _ => (1:ℝ)) y *
        (stripe s a).indicator (fun _ => (1:ℝ)) y := by
  by_cases hc : y ∈ annularCore η s <;> by_cases hs : y ∈ stripe s a <;>
    simp [mask,Set.indicator,hc,hs]

private theorem mask_error_le (η s μ : ℝ) (a : Bool) (y x : Transverse) :
    |(mask η s a).indicator (fun _ => (1:ℝ)) y -
        (scaleShell η μ).indicator (fun _ => (1:ℝ)) x *
          (stripe s a).indicator (fun _ => (1:ℝ)) y| ≤
      |(annularCore η s).indicator (fun _ => (1:ℝ)) y -
        (scaleShell η μ).indicator (fun _ => (1:ℝ)) x| := by
  rw [mask_indicator_factor,← sub_mul,abs_mul]
  by_cases h : y ∈ stripe s a
  · simp only [indicator_of_mem h,abs_one,mul_one,le_refl]
  · simp only [indicator_of_notMem h,abs_zero,mul_zero,abs_nonneg]

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Exponential velocity moments of the actual cold supersolutions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.SheetClass

theorem exponentialMoment_mono {μ ν : Measure Velocity} (h : μ ≤ ν) :
    exponentialMoment μ ≤ exponentialMoment ν := lintegral_mono' h le_rfl

theorem exponentialMoment_smul (a : ℝ≥0∞) (μ : Measure Velocity) :
    exponentialMoment (a • μ) = a*exponentialMoment μ := lintegral_smul_measure a _

theorem exponentialMoment_add (μ ν : Measure Velocity) :
    exponentialMoment (μ+ν) = exponentialMoment μ+exponentialMoment ν := lintegral_add_measure _ _ _

theorem elementary_exponentialMoment {L : ℝ} {μ : Measure Velocity} (h : IsElementary L μ) :
    exponentialMoment μ ≤ ENNReal.ofReal (4*L) := by
  obtain ⟨d,ρ,hd,hdmax,hprob,hρ,rfl⟩ := h
  let := hprob
  have he : exponentialMoment (SheetMeasures.sheetLaw d ρ) = SheetMeasures.tiltedSheet d ρ univ := by
    simp only [exponentialMoment,SheetMeasures.tiltedSheet,withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
  rw [he]
  exact SheetMeasures.tiltedSheet_mass_le hd hdmax hρ

theorem exponentialMoment_density {f : Velocity → ℝ} (hf : Measurable f) :
    exponentialMoment (volume.withDensity (fun v => ENNReal.ofReal (f v))) =
      ∫⁻ v, ENNReal.ofReal (Real.exp (2*‖v‖^2)*f v) := by
  have he : Measurable (fun v : Velocity => ENNReal.ofReal (Real.exp (2*‖v‖^2))) := by fun_prop
  rw [exponentialMoment,lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal he]
  apply lintegral_congr
  intro v
  change ENNReal.ofReal (f v)*ENNReal.ofReal (Real.exp (2*‖v‖^2)) = _
  rw [mul_comm,← ENNReal.ofReal_mul (Real.exp_pos _).le]

end BoltzmannNonuniqueness.SheetClass

namespace BoltzmannNonuniqueness.JetEnvelopeGain

theorem exponential_moment_le {K α γ s d t : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s)
    (hd : 0 < d) (hdmax : d ≤ 1/16) (ht : 0 ≤ t) (htmax : t ≤ 1)
    (η : ℝ) (a : Bool) (x : Space) :
    SheetClass.exponentialMoment
      (volume.withDensity (fun v => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x,v)))) ≤
      ENNReal.ofReal (amplitude η K α γ s d t a x * (8*Real.exp (16*(1+α)^2))) := by
  let L := 2*Real.exp (16*(1+α)^2)
  have hc : SheetClass.IsElementary L
      (SheetMeasures.sheetLaw d (JetAxialLaw.law (sign a) α γ s d t x.2)) := by
    have hp := JetAxialLaw.probability (sign a) α γ s d t x.2
    have hm := JetAxialLaw.moment hα.le hγ.le hs hd hdmax ht (sign a) x.2
    have he : |sign a| = 1 := JetSupport.abs_sign a
    rw [he] at hm
    exact ⟨d,_,hd.le,by linarith,hp,hm,rfl⟩
  have hr : SheetClass.IsElementary L
      (SheetMeasures.sheetLaw d
        (JetAxialLaw.law (AxialFlow.velocity (sign a) α γ s t x.2) 0 0 1 d 0 0)) :=
    ⟨d,_,hd.le,by linarith,JetAxialLaw.probability _ _ _ _ _ _ _,
      JetRemainderSheet.axial_moment hα.le hd hdmax γ s t x.2 a,rfl⟩
  have hcore : SheetClass.exponentialMoment
      (volume.withDensity (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x,v)))) ≤
      ENNReal.ofReal (JetCoreSheet.amplitude K α γ s t)*ENNReal.ofReal (4*L) := by
    calc
      _ ≤ SheetClass.exponentialMoment (ENNReal.ofReal (JetCoreSheet.amplitude K α γ s t) •
          SheetMeasures.sheetLaw d (JetAxialLaw.law (sign a) α γ s d t x.2)) :=
        SheetClass.exponentialMoment_mono (JetCoreSheet.measure_domination hK hα hγ hs hd ht η a x)
      _ = _ := SheetClass.exponentialMoment_smul _ _
      _ ≤ _ := mul_le_mul' le_rfl (SheetClass.elementary_exponentialMoment hc)
  have hrest : SheetClass.exponentialMoment
      (volume.withDensity (fun v => ENNReal.ofReal (JetRemainderSheet.remainder η K α γ s d t a x v))) ≤
      ENNReal.ofReal (JetRemainderSheet.amplitude η K α γ s d t a x)*ENNReal.ofReal (4*L) := by
    calc
      _ ≤ SheetClass.exponentialMoment (ENNReal.ofReal (JetRemainderSheet.amplitude η K α γ s d t a x) •
          SheetMeasures.sheetLaw d
            (JetAxialLaw.law (AxialFlow.velocity (sign a) α γ s t x.2) 0 0 1 d 0 0)) :=
        SheetClass.exponentialMoment_mono (JetRemainderSheet.measure_domination hK hs hd htmax η α γ a x)
      _ = _ := SheetClass.exponentialMoment_smul _ _
      _ ≤ _ := mul_le_mul' le_rfl (SheetClass.elementary_exponentialMoment hr)
  have hrc : 0 ≤ JetRemainderSheet.amplitude η K α γ s d t a x := by
    have he := JetSupersolution.epsilon_nonneg hK hs hd
    have hm := JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x
    unfold JetRemainderSheet.amplitude
    positivity
  rw [measure_eq hK hs hd,SheetClass.exponentialMoment_add]
  apply (add_le_add hcore hrest).trans_eq
  rw [← add_mul,← ENNReal.ofReal_add (JetCoreSheet.amplitude_nonneg hK hs ht α γ)
    hrc,← ENNReal.ofReal_mul]
  · congr 1
    dsimp [amplitude,L]
    ring
  · exact add_nonneg (JetCoreSheet.amplitude_nonneg hK hs ht α γ)
      hrc

end BoltzmannNonuniqueness.JetEnvelopeGain

end

end

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

theorem annulus_bound {η K α s d₀ t : ℝ} (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hs : 0 < s) (hsmax : s ≤ 1 / 8)
    (hd₀ : 0 < d₀) (hwidth : d₀ * s ^ 10 ≤ 1 / 16) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (γ : ℝ) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    annulus η K α γ s d₀ t x v ≤ ENNReal.ofReal (coefficient α K d₀ *
      JetEscapePower.tail (JetEscapedBarrier.rate η d₀ / 2) s t * Real.exp (-4 * ‖v‖ ^ 2)) := by
  have hc : 0 ≤ JetEscapedBarrier.coefficient α K d₀ := by
    unfold JetEscapedBarrier.coefficient JetGaussianEscape.constant
    have := JetThermalKernel.bound_pos
    positivity
  have ht0 := JetEscapePower.tail_nonneg hs.le (JetEscapedBarrier.rate η d₀ / 2) t
  have hL : 0 ≤ JetLatticeGaussian.constant ^ 3 := by
    unfold JetLatticeGaussian.constant JetLatticeGaussian.exponential
    positivity
  unfold annulus
  apply (ENNReal.tsum_le_tsum (fun a => JetEscapedCopies.copy_sum_bound hη hηmax hK hα hαmax
    hs hsmax hd₀ hwidth ht htmax γ a x v hx)).trans_eq
  simp only [tsum_fintype, Fintype.sum_bool]
  have hA : 0 ≤ JetEscapedBarrier.coefficient α K d₀ *
      JetEscapePower.tail (JetEscapedBarrier.rate η d₀ / 2) s t * Real.exp (-4 * ‖v‖ ^ 2) :=
    mul_nonneg (mul_nonneg hc ht0) (Real.exp_nonneg _)
  simp_rw [← ENNReal.ofReal_mul hA]
  rw [← ENNReal.ofReal_add (mul_nonneg hA hL) (mul_nonneg hA hL)]
  congr 1
  unfold coefficient
  ring

theorem scale_bound {s₀ η : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η) (j : ℕ) :
    jetScale s₀ η j ≤ s₀ := by
  have h := scale_antitone hs₀.le hη.le (show 0 ≤ j + 1 by omega)
  simpa only [jetScale, DatumBounds.scale, Nat.cast_zero, neg_zero, zero_mul, Real.exp_zero, mul_one] using h

theorem annular_tail_summable {β s₀ η t : ℝ} (hβ : 0 < β) (hs₀ : 0 < s₀)
    (hη : 0 < η) (ht : 0 < t) :
    Summable (fun j : ℕ => JetEscapePower.tail β (jetScale s₀ η j) t) := by
  exact (summable_nat_add_iff 1).mpr (JetEscapePower.summable_tails hβ hs₀ hη ht)

theorem annular_tail_bound {β s₀ η t : ℝ} (hβ : 0 < β) (hs₀ : 0 < s₀)
    (hη : 0 < η) (ht : 0 < t) (m : ℕ) (hm : 31 < 16 * m) :
    (∑' j : ℕ, JetEscapePower.tail β (jetScale s₀ η j) t) ≤
      ((m.factorial : ℝ) / β ^ m * t ^ m) * ∑' j : ℕ, jetScale s₀ η j ^ (16 * m - 31) := by
  have hp : 0 < 16 * m - 31 := Nat.sub_pos_of_lt hm
  have hsp := DatumBounds.summable_scale_pow s₀ hη (16 * m - 31) hp
  have hs : Summable (fun j : ℕ => jetScale s₀ η j ^ (16 * m - 31)) := by
    change Summable (fun j : ℕ => DatumBounds.scale s₀ η (j + 1) ^ (16 * m - 31))
    exact (summable_nat_add_iff (f := fun j : ℕ => DatumBounds.scale s₀ η j ^ (16 * m - 31)) 1).mpr hsp
  calc
    _ ≤ ∑' j : ℕ, ((m.factorial : ℝ) / β ^ m * t ^ m) * jetScale s₀ η j ^ (16 * m - 31) :=
      (annular_tail_summable hβ hs₀ hη ht).tsum_le_tsum
        (fun j => JetEscapePower.tail_bound hβ (DatumBounds.scale_pos (η := η) hs₀ (j + 1)) ht m hm.le)
        (hs.mul_left _)
    _ = _ := tsum_mul_left


theorem total_amplitude_bound {s₀ η K α d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (γ : ℝ) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    total s₀ η K α γ d₀ t x v ≤ ENNReal.ofReal (coefficient α K d₀ *
      (∑' j : ℕ, JetEscapePower.tail (JetEscapedBarrier.rate η d₀ / 2) (jetScale s₀ η j) t) *
        Real.exp (-4 * ‖v‖ ^ 2)) := by
  have hc := coefficient_nonneg hK hd₀ α
  have hs (j : ℕ) : 0 < jetScale s₀ η j := DatumBounds.scale_pos (η := η) hs₀ (j + 1)
  have hs' (j : ℕ) : jetScale s₀ η j ≤ 1 / 8 := (scale_bound hs₀ hη j).trans hsmax
  have hβ : 0 < JetEscapedBarrier.rate η d₀ / 2 := by
    exact div_pos (JetEscapedBarrier.rate_pos hη hd₀) (by norm_num)
  have htail := annular_tail_summable hβ hs₀ hη ht
  have hsum : Summable (fun j : ℕ => coefficient α K d₀ *
      JetEscapePower.tail (JetEscapedBarrier.rate η d₀ / 2) (jetScale s₀ η j) t * Real.exp (-4 * ‖v‖ ^ 2)) :=
    (htail.mul_left _).mul_right _
  unfold total
  apply (ENNReal.tsum_le_tsum (fun j => annulus_bound hη hηmax hK hα hαmax (hs j) (hs' j) hd₀
    (JetEnvelopeGain.thermal_width_le hd₀max (hs j).le (hs' j)) ht htmax γ x v hx)).trans_eq
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg
    (mul_nonneg hc (JetEscapePower.tail_nonneg (hs j).le _ t)) (Real.exp_nonneg _)) hsum]
  congr 1
  rw [tsum_mul_right, tsum_mul_left]

theorem powerConstant_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (η α : ℝ) (m : ℕ) : 0 ≤ powerConstant s₀ η α K d₀ m := by
  have hr : 0 ≤ JetEscapedBarrier.rate η d₀ := by
    unfold JetEscapedBarrier.rate
    positivity
  unfold powerConstant
  apply mul_nonneg (mul_nonneg (coefficient_nonneg hK hd₀ α) (by positivity))
  exact tsum_nonneg (fun j => pow_nonneg (DatumBounds.scale_pos (η := η) hs₀ (j + 1)).le _)

theorem arbitrary_power {s₀ η K α d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (m : ℕ) (hm : 31 < 16 * m) (γ : ℝ) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1) :
    total s₀ η K α γ d₀ t x v ≤
      ENNReal.ofReal (powerConstant s₀ η α K d₀ m * t ^ m * Real.exp (-4 * ‖v‖ ^ 2)) := by
  have hc := coefficient_nonneg hK hd₀ α
  have hβ : 0 < JetEscapedBarrier.rate η d₀ / 2 :=
    div_pos (JetEscapedBarrier.rate_pos hη hd₀) (by norm_num)
  apply (total_amplitude_bound hs₀ hsmax hη hηmax hK hα hαmax hd₀ hd₀max ht htmax γ x v hx).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ coefficient α K d₀ *
        (((m.factorial : ℝ) / (JetEscapedBarrier.rate η d₀ / 2) ^ m * t ^ m) *
          ∑' j : ℕ, jetScale s₀ η j ^ (16 * m - 31)) * Real.exp (-4 * ‖v‖ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (annular_tail_bound hβ hs₀ hη ht m hm) hc)
        (Real.exp_nonneg _)
    _ = _ := by unfold powerConstant; ring

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

theorem epsilon_eq {s : ℝ} (hs : 0 < s) (K d₀ : ℝ) :
    JetSupersolution.epsilon K s (d₀ * s ^ 10) =
      JetComparisonCoefficient.coefficient K * d₀ * s ^ 9 := by
  unfold JetSupersolution.epsilon
  field_simp

theorem epsilon_small {s₀ s K d₀ : ℝ} (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (hs : 0 < s) (hss : s ≤ s₀)
    (hsmall : JetComparisonCoefficient.coefficient K * d₀ * s₀ ^ 9 ≤ 1) :
    JetSupersolution.epsilon K s (d₀ * s ^ 10) ≤ 1 := by
  rw [epsilon_eq hs]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.le hss 9)
    (mul_nonneg (zero_le_one.trans (JetComparisonCoefficient.coefficient_ge_one hK)) hd₀)).trans hsmall

theorem sum_le_twice {s₀ η K α γ d₀ t : ℝ} (hs₀ : 0 < s₀) (hη : 0 < η)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (ht : 0 < t) (htmax : t ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K * d₀ * s₀ ^ 9 ≤ 1)
    (S : ℕ → Bool → Lattice → Prop) (F : ℕ → Bool → Lattice → ℝ)
    (x v : Velocity)
    (hF : ∀ j a n, S j a n → F j a n ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j) (d₀ * jetScale s₀ η j ^ 10) t a (shifted x n, v)) :
    escapedSum s₀ η t x S F ≤ 2 * JetEscapedTotal.total s₀ η K α γ d₀ t x v := by
  classical
  have hs (j : ℕ) : 0 < jetScale s₀ η j := DatumBounds.scale_pos (η := η) hs₀ (j + 1)
  calc
    _ ≤ ∑' j : ℕ, ∑' a : Bool, ∑' n : Lattice, (2 : ℝ≥0∞) *
        {n | outside η (jetScale s₀ η j) t a x n}.indicator
          (fun n => ENNReal.ofReal (JetBarrier.barrier η K α γ (jetScale s₀ η j)
            (d₀ * jetScale s₀ η j ^ 10) t a (shifted x n, v))) n := by
      apply ENNReal.tsum_le_tsum
      intro j
      apply ENNReal.tsum_le_tsum
      intro a
      apply ENNReal.tsum_le_tsum
      intro n
      by_cases hout : outside η (jetScale s₀ η j) t a x n
      · by_cases hS : S j a n
        · simp only [mem_ofPred_eq, hS, hout, and_self, indicator_of_mem]
          have hd : 0 < d₀ * jetScale s₀ η j ^ 10 := mul_pos hd₀ (pow_pos (hs j) _)
          have hb := (hF j a n hS).trans (JetSupersolution.le_twice_barrier hK (hs j) hd
            hα hγ ht htmax (epsilon_small hK hd₀.le (hs j)
              (JetEscapedTotal.scale_bound hs₀ hη j) hsmall) η a (shifted x n, v))
          simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using
            ENNReal.ofReal_le_ofReal hb
        · simp only [mem_ofPred_eq, hS, false_and, not_false_eq_true, indicator_of_notMem]
          exact bot_le
      · simp only [mem_ofPred_eq, hout, and_false, not_false_eq_true, indicator_of_notMem,
          mul_zero, le_refl]
    _ = _ := by
      simp_rw [ENNReal.tsum_mul_left]
      rfl

theorem constant_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (η α : ℝ) (m : ℕ) : 0 ≤ constant s₀ η α K d₀ m :=
  mul_nonneg (mul_nonneg (by norm_num) (JetEscapedTotal.powerConstant_nonneg hs₀ hK hd₀ η α m))
    tiltConstant_pos.le

theorem arbitrary_power {s₀ η K α γ d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (hsmall : JetComparisonCoefficient.coefficient K * d₀ * s₀ ^ 9 ≤ 1)
    (m : ℕ) (hm : 31 < 16 * m) (q : ℝ)
    (S : ℕ → Bool → Lattice → Prop) (F : ℕ → Bool → Lattice → ℝ)
    (x v : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (hF : ∀ j a n, S j a n → F j a n ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j) (d₀ * jetScale s₀ η j ^ 10) t a (shifted x n, v)) :
    escapedSum s₀ η t x S F ≤ ENNReal.ofReal (constant s₀ η α K d₀ m * t ^ m * H q v) := by
  have hp := JetEscapedTotal.powerConstant_nonneg hs₀ hK hd₀ η α m
  have hg : Real.exp (-4 * ‖v‖ ^ 2) ≤ tiltConstant * H q v := by
    apply (Real.exp_le_exp.mpr (show -4 * ‖v‖ ^ 2 ≤ -2 * ‖v‖ ^ 2 by nlinarith [sq_nonneg ‖v‖])).trans
    exact JetGaussianEscape.gaussian_le_hot q v
  calc
    _ ≤ 2 * JetEscapedTotal.total s₀ η K α γ d₀ t x v :=
      sum_le_twice hs₀ hη hK hα hγ hd₀ ht (htmax.trans (by norm_num)) hsmall S F x v hF
    _ ≤ 2 * ENNReal.ofReal (JetEscapedTotal.powerConstant s₀ η α K d₀ m * t ^ m *
        Real.exp (-4 * ‖v‖ ^ 2)) := mul_le_mul' le_rfl (JetEscapedTotal.arbitrary_power
          hs₀ hsmax hη hηmax hK hα hαmax hd₀ hd₀max ht htmax m hm γ x v hx)
    _ = ENNReal.ofReal (2 * (JetEscapedTotal.powerConstant s₀ η α K d₀ m * t ^ m *
        Real.exp (-4 * ‖v‖ ^ 2))) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ 2 * (JetEscapedTotal.powerConstant s₀ η α K d₀ m * t ^ m * (tiltConstant * H q v)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hg (mul_nonneg hp (pow_nonneg ht.le _)))
            (by norm_num)
        _ = _ := by unfold constant; ring

theorem exponent_large (A : ℝ) : 31 < 16 * exponent A := by
  unfold exponent
  omega

theorem le_exponent (A : ℝ) : A ≤ (exponent A : ℝ) := by
  have h := Nat.le_ceil A
  unfold exponent
  push_cast
  linarith

/-- The same constant works for every time, spatial point, and retained subset. -/
theorem real_power {s₀ η K α γ d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1 / 32)
    (hsmall : JetComparisonCoefficient.coefficient K * d₀ * s₀ ^ 9 ≤ 1) (A q : ℝ)
    (S : ℕ → Bool → Lattice → Prop) (F : ℕ → Bool → Lattice → ℝ)
    (x v : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (hF : ∀ j a n, S j a n → F j a n ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j) (d₀ * jetScale s₀ η j ^ 10) t a (shifted x n, v)) :
    escapedSum s₀ η t x S F ≤
      ENNReal.ofReal (constant s₀ η α K d₀ (exponent A) * t ^ A * H q v) := by
  apply (arbitrary_power hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max ht htmax hsmall
    (exponent A) (exponent_large A) q S F x v hx hF).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (H_nonneg q v)
  apply mul_le_mul_of_nonneg_left _ (constant_nonneg hs₀ hK hd₀ η α _)
  simpa only [Real.rpow_natCast] using
    Real.rpow_le_rpow_of_exponent_ge ht (htmax.trans (by norm_num)) (le_exponent A)

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

theorem exponential_moment_uniform {K α γ s d₀ t : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hsmax : s ≤ 1/8)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (η : ℝ) (a : Bool) (x : Space) :
    SheetClass.exponentialMoment (volume.withDensity (fun v =>
      ENNReal.ofReal (JetSupersolution.U η K α γ s (d₀*s^10) t a (x,v)))) ≤
        ENNReal.ofReal (momentConstant K α γ/(s+t)) := by
  have hd : 0 < d₀*s^10 := by positivity
  have hm := exponential_moment_le hK hα hγ hs hd (thermal_width_le hd₀max hs.le hsmax)
    ht.le (htmax.trans (by norm_num)) η a x
  apply hm.trans (ENNReal.ofReal_le_ofReal ?_)
  have ha := amplitude_bound (α := α) (γ := γ) hK hs hd ht (htmax.trans (by norm_num))
    (thermal_scale_small hd₀max hs hsmax ht.le htmax) η a x
  calc
    _ ≤ ((K*max 1 (α*γ)⁻¹*JetGaussianProduct.coefficient+JetRemainderSheet.uniformConstant K)/(s+t))*
        (8*Real.exp (16*(1+α)^2)) := mul_le_mul_of_nonneg_right ha (by positivity)
    _ = _ := by unfold momentConstant; ring

theorem dominated_exponential_moment {K α γ s d₀ t : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (hsmax : s ≤ 1/8)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (η : ℝ) (a : Bool) (x : Space) {f : Velocity → ℝ}
    (hf : ∀ v, f v ≤ JetSupersolution.U η K α γ s (d₀*s^10) t a (x,v)) :
    SheetClass.exponentialMoment (volume.withDensity (fun v => ENNReal.ofReal (f v))) ≤
      ENNReal.ofReal (momentConstant K α γ/(s+t)) :=
  (SheetClass.exponentialMoment_mono (withDensity_mono (ae_of_all _
    (fun v => ENNReal.ofReal_le_ofReal (hf v))))).trans
      (exponential_moment_uniform hK hα hγ hs hsmax hd₀ hd₀max ht htmax η a x)

end BoltzmannNonuniqueness.JetEnvelopeGain

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
theorem weight_le (v : Velocity) : weight v ≤ Real.exp (2*‖v‖^2) := by
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ‖v‖]

theorem moment_mono_ae {f g : Velocity → ℝ} (h : ∀ᵐ v, f v ≤ g v) : moment f ≤ moment g := by
  apply lintegral_mono_ae
  filter_upwards [h] with v hv
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hv (weight_pos v).le)

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

theorem moment_add {f g : Velocity → ℝ} (hfm : Measurable f)
    (hf : ∀ v, 0 ≤ f v) (hg : ∀ v, 0 ≤ g v) :
    moment (fun v => f v+g v) = moment f+moment g := by
  unfold moment
  simp_rw [mul_add,ENNReal.ofReal_add (mul_nonneg (weight_pos _).le (hf _))
    (mul_nonneg (weight_pos _).le (hg _))]
  apply lintegral_add_left
  have hm : Measurable (fun v => ENNReal.ofReal (weight v*f v)) := by
    unfold weight
    fun_prop
  exact hm

theorem moment_le_exponential {f : Velocity → ℝ} (hfm : Measurable f) (hf : ∀ v, 0 ≤ f v) :
    moment f ≤ SheetClass.exponentialMoment (volume.withDensity (fun v => ENNReal.ofReal (f v))) := by
  rw [SheetClass.exponentialMoment_density hfm]
  exact lintegral_mono (fun v => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (weight_le v) (hf v)))

end BoltzmannNonuniqueness.VelocityMoment

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

/-! # The escaped-family estimate in the actual label indexing -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem tsum_labels (f : Label → ℝ≥0∞) :
    (∑' i, f i) = ∑' j : ℕ, ∑' a : Bool, ∑' n : Lattice, f ⟨j,a,n⟩ := by
  rw [← coordinates.symm.tsum_eq f]
  change (∑' p : ℕ × (Bool × Lattice), f ⟨p.1,p.2.1,p.2.2⟩) = _
  rw [ENNReal.tsum_prod']
  simp_rw [ENNReal.tsum_prod']

theorem escaped_bound {s₀ η K α γ d₀ t : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1)
    (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (A q : ℝ) (N : ℕ)
    (f : Label → ℝ) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (hf : ∀ i, 0 ≤ f i) (hfs : Summable f)
    (hfU : ∀ i, i.annulus < N → f i ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,v)) :
    (∑' i, escaped s₀ η t N x f i) ≤
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A*VelocityWeight.H q v := by
  classical
  have hnon (i) : 0 ≤ escaped s₀ η t N x f i := by
    unfold escaped
    split_ifs
    · exact hf i
    · exact le_rfl
  have hle (i) : escaped s₀ η t N x f i ≤ f i := by
    unfold escaped
    split_ifs
    · exact le_rfl
    · exact hf i
  have hsum : Summable (escaped s₀ η t N x f) := Summable.of_nonneg_of_le hnon hle hfs
  have h := JetEscapedEnvelope.real_power hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    ht htmax hsmall A q (fun j _ _ => j < N) (fun j a n => f ⟨j,a,n⟩) x v hx
    (fun j a n hj => hfU ⟨j,a,n⟩ hj)
  have he : (∑' i, ENNReal.ofReal (escaped s₀ η t N x f i)) =
      JetEscapedEnvelope.escapedSum s₀ η t x (fun j _ _ => j < N) (fun j a n => f ⟨j,a,n⟩) := by
    rw [tsum_labels]
    unfold escaped JetEscapedEnvelope.escapedSum
    simp only [Set.indicator_apply,Set.mem_ofPred_eq,apply_ite ENNReal.ofReal,ENNReal.ofReal_zero]
  rw [← he, ← ENNReal.ofReal_tsum_of_nonneg hnon hsum] at h
  have hB : 0 ≤ JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*
      t^A*VelocityWeight.H q v := by
    have hc := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α (JetEscapedEnvelope.exponent A)
    exact mul_nonneg (mul_nonneg hc (Real.rpow_nonneg ht.le A)) (VelocityWeight.H_nonneg q v)
  simpa only [ENNReal.toReal_ofReal (tsum_nonneg hnon),ENNReal.toReal_ofReal hB] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

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

section

/-! # Weighted tails and absent labels of the actual cold family -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem normalized_escaped_bound {s₀ η K α γ d₀ t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (A q : ℝ) (N : ℕ)
    (f : Label → ℝ) (x v : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (hf : ∀ i, 0 ≤ f i) (hfs : Summable f)
    (hfU : ∀ i, i.annulus < N → VelocityWeight.H q v*f i ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,v)) :
    (∑' i, escaped s₀ η t N x f i) ≤
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A := by
  have h := escaped_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max ht htmax hsmall A q N
    (fun i => VelocityWeight.H q v*f i) x v hx
    (fun i => mul_nonneg (VelocityWeight.H_nonneg q v) (hf i))
    (hfs.mul_left (VelocityWeight.H q v)) hfU
  have he (i) : escaped s₀ η t N x (fun j => VelocityWeight.H q v*f j) i =
      VelocityWeight.H q v*escaped s₀ η t N x f i := by
    unfold escaped
    split_ifs <;> simp only [mul_zero]
  simp_rw [he] at h
  rw [tsum_mul_left] at h
  have hh : VelocityWeight.H q v*(∑' i, escaped s₀ η t N x f i) ≤
      VelocityWeight.H q v*(JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A) :=
    h.trans_eq (mul_comm _ _)
  exact (mul_le_mul_iff_of_pos_left (VelocityWeight.H_pos q v)).mp hh

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Spatial localization of the unique cold core in the central periodic cube -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem enlargement_central_lattice {s₀ η t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (htmax : t ≤ 1/32)
    {x : Velocity} (hx : x ∈ TorusChart.cube) {i : Label}
    (hi : x ∈ spatialEnlargement s₀ η t i) : i.lattice = 0 := by
  have hn := enlargement_inside_baseBall hs₀ hη i.annulus i.positive hi.1
  rw [Metric.mem_ball,dist_zero_right] at hn
  have hclose {r : ℝ} {n : ℤ} (hr : r ∈ TorusChart.interval)
      (h : |r-(n:ℝ)| ≤ 1/4) : n = 0 := by
    by_contra hne
    have hd := integer_distance hne
    have ha : |r| ≤ 1/2 := abs_le.mpr ⟨hr.1.le,hr.2⟩
    have hb := abs_add_le ((n:ℝ)-r) r
    rw [sub_add_cancel,abs_sub_comm] at hb
    simp only [Int.cast_zero,sub_zero] at hd
    linarith
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · apply hclose (hx (Fin.last 2))
    have hb := hi.2
    change |x (Fin.last 2)-(i.lattice (Fin.last 2):ℝ)| ≤ 1/8+2*t+1/16 at hb
    linarith
  · apply hclose (hx j.castSucc)
    have hb := PiLp.norm_apply_le (transverse x-transverseShift i.lattice) j
    change ‖x j.castSucc-(i.lattice j.castSucc:ℝ)‖ ≤ _ at hb
    rw [Real.norm_eq_abs] at hb
    linarith

theorem enlargement_central_shell {s₀ η t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (htmax : t ≤ 1/32)
    {x : Velocity} (hx : x ∈ TorusChart.cube) {i : Label}
    (hi : x ∈ spatialEnlargement s₀ η t i) :
    transverse x ∈ AnnularEnvelope.shell s₀ η i.annulus := by
  have hz := enlargement_central_lattice hs₀ hsmax hη htmax hx hi
  have he := hi.1
  rw [hz] at he
  have hshift : transverseShift (0 : Lattice) = 0 := by ext k; simp [transverseShift]
  rw [hshift,sub_zero] at he
  exact enlargement_subset_annulus hη (DatumBounds.scale_pos hs₀ _) i.positive he

theorem main_coefficient_le {s₀ η t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (ht : 0 ≤ t) (htmax : t ≤ 1/32)
    {N : ℕ} {x : Velocity} (hx : x ∈ TorusChart.cube) {i : Label}
    (hiN : i.annulus < N) (hi : x ∈ spatialEnlargement s₀ η t i) :
    1/(jetScale s₀ η i.annulus+t) ≤
      AnnularEnvelope.finiteEnvelope s₀ η (Finset.range N) t (transverse x) := by
  have hs (j : ℕ) : 0 < jetScale s₀ η j := DatumBounds.scale_pos hs₀ _
  have hn (j : ℕ) (_hj : j ∈ Finset.range N) :
      0 ≤ AnnularEnvelope.term s₀ η j t (transverse x) := by
    apply indicator_nonneg
    intro _ _
    exact div_nonneg zero_le_one (add_nonneg ht (hs j).le)
  have he := Finset.single_le_sum hn (Finset.mem_range.mpr hiN)
  have hshell := enlargement_central_shell hs₀ hsmax hη htmax hx hi
  simpa only [AnnularEnvelope.finiteEnvelope,AnnularEnvelope.term,indicator_of_mem hshell,add_comm] using he

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Annular half-Gaussian moment bound for the periodic geometric decomposition -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cell_moment_bound_q80_oai {s₀ η K α γ d₀ q t Z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hq : q < 2) (hZ : 0 ≤ Z)
    (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ) (x : Velocity) (hx : x ∈ TorusChart.cube)
    (F : Velocity → ℝ) (c : Label → Velocity → ℝ)
    (hcm : ∀ i, Measurable (c i)) (hcn : ∀ i v, 0 ≤ c i v)
    (hcs : ∀ v, Summable (fun i => c i v))
    (hzero : ∀ i, ¬i.annulus < N → ∀ v, c i v = 0)
    (hU : ∀ i v, H q v*c i v ≤ JetSupersolution.U η K α γ (jetScale s₀ η i.annulus)
      (d₀*jetScale s₀ η i.annulus^10) t i.positive (JetSpatialBox.shifted x i.lattice,v))
    (hhot : ∀ᵐ v, F v-∑' i, c i v ≤ Z) :
    moment (fun v => H q v*F v) ≤ ENNReal.ofReal
      ((Z+escapedConstant s₀ η K α d₀)*hotConstant q+
        JetEnvelopeGain.momentConstant K α γ*
          AnnularEnvelope.finiteEnvelope s₀ η (Finset.range N) t (transverse x)) := by
  let E := escapedConstant s₀ η K α d₀
  have hE : 0 ≤ E := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _
  have hZE : 0 ≤ Z+E := add_nonneg hZ hE
  have hx1 (k) : |x k| ≤ 1 := by
    have h := hx k
    exact (abs_le.mpr ⟨h.1.le,h.2⟩).trans (by norm_num)
  have he (v) : (∑' i, escaped s₀ η t N x (fun j => c j v) i) ≤ E := by
    simpa only [Real.rpow_zero,mul_one,E,escapedConstant] using
      normalized_escaped_bound hs₀ hsmax hη hηmax hK hα.le hαmax hγ.le hd₀ hd₀max ht htmax
        hsmall 0 q N (fun j => c j v) x v hx1 (fun i => hcn i v) (hcs v)
        (fun i _ => hU i v)
  have hmeas : Measurable (fun v => (Z+E)*H q v) := by unfold H singularity; fun_prop
  have hnonneg (v) : 0 ≤ (Z+E)*H q v := mul_nonneg hZE (H_nonneg q v)
  have hbase := hot_moment hq hZE
  have henvnonneg : 0 ≤ JetEnvelopeGain.momentConstant K α γ*
      AnnularEnvelope.finiteEnvelope s₀ η (Finset.range N) t (transverse x) := by
    apply mul_nonneg (JetEnvelopeGain.momentConstant_nonneg hK α γ)
    apply Finset.sum_nonneg
    intro j _
    apply indicator_nonneg
    intro _ _
    exact div_nonneg zero_le_one (add_nonneg ht.le (DatumBounds.scale_pos hs₀ _).le)
  rcases main_or_outside hs₀ hsmax hη hηmax htmax N x with ⟨i,hiN,hi,hout⟩ | hout
  · have hdom : ∀ᵐ v, H q v*F v ≤ (Z+E)*H q v+H q v*c i v := by
      filter_upwards [hhot] with v hv
      have hs := sum_sub_main (hcs v) (fun j hj => hzero j hj v) i hi hout
      have hc := he v
      have hn : F v ≤ Z+E+c i v := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hn (H_nonneg q v)]
    have him : Measurable (fun v => H q v*c i v) := by unfold H singularity; fun_prop
    have hin (v) : 0 ≤ H q v*c i v := mul_nonneg (H_nonneg q v) (hcn i v)
    have hb := (moment_le_exponential him hin).trans
      (JetEnvelopeGain.dominated_exponential_moment hK hα hγ (DatumBounds.scale_pos hs₀ _)
        ((JetEscapedTotal.scale_bound hs₀ hη _).trans hsmax) hd₀ hd₀max ht htmax η i.positive
        (JetSpatialBox.shifted x i.lattice) (hU i))
    have hcoef := mul_le_mul_of_nonneg_left (main_coefficient_le hs₀ hsmax hη ht.le htmax hx hiN hi)
      (JetEnvelopeGain.momentConstant_nonneg hK α γ)
    have hcore : moment (fun v => H q v*c i v) ≤ ENNReal.ofReal
        (JetEnvelopeGain.momentConstant K α γ*AnnularEnvelope.finiteEnvelope s₀ η
          (Finset.range N) t (transverse x)) := by
      apply hb.trans (ENNReal.ofReal_le_ofReal ?_)
      simpa only [div_eq_mul_inv,one_mul,jetScale] using hcoef
    calc
      _ ≤ moment (fun v => (Z+E)*H q v+H q v*c i v) := moment_mono_ae hdom
      _ = _ := moment_add hmeas hnonneg hin
      _ ≤ _ := add_le_add (le_of_eq hbase) hcore
      _ = _ := (ENNReal.ofReal_add (mul_nonneg hZE (hotConstant_nonneg q)) henvnonneg).symm
  · have hdom : ∀ᵐ v, H q v*F v ≤ (Z+E)*H q v := by
      filter_upwards [hhot] with v hv
      have hs := sum_all_escaped (fun j hj => hzero j hj v) hout
      have hc := he v
      have hn : F v ≤ Z+E := by rw [hs] at hv; linarith
      nlinarith [mul_le_mul_of_nonneg_left hn (H_nonneg q v)]
    calc
      _ ≤ moment (fun v => (Z+E)*H q v) := moment_mono_ae hdom
      _ = _ := hbase
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right henvnonneg)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.cell_moment_bound_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.cell_moment_bound_q80_oai
