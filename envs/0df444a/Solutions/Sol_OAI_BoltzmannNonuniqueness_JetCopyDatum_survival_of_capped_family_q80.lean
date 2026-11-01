-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.survival_of_capped_family_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:06:39.423246+00:00
-- url     : https://prove2.me/submissions/74e6404b-4a7a-4605-9a21-6762b581f770

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LossIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Loss frequency and its first-moment bound

The angular normalization gives the loss-frequency formula from Section 2,
equation `eq:frequency`. Fubini is used only with an explicit integrability
hypothesis for the original collision integrand. Separate first-moment
conditions ensure that the frequency integral itself is finite.
-/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem frequency_integrand_norm_le (f : Density) (x : Position) (v w : Velocity) :
    ‖‖v - w‖ * f (x, w)‖ ≤
      ‖v‖ * |f (x, w)| + ‖w‖ * |f (x, w)| := by
  rw [Real.norm_eq_abs, abs_mul, abs_norm]
  calc
    ‖v - w‖ * |f (x, w)| ≤ (‖v‖ + ‖w‖) * |f (x, w)| :=
      mul_le_mul_of_nonneg_right (norm_sub_le v w) (abs_nonneg _)
    _ = _ := by ring

theorem integrable_abs_firstMoment (f : Density) (x : Position)
    (hm : Integrable (fun w : Velocity => ‖w‖ * f (x, w))) :
    Integrable (fun w : Velocity => ‖w‖ * |f (x, w)|) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using hm.norm

/-- Finite mass and first absolute velocity moment make the frequency integrable. -/
theorem integrable_frequency_integrand (f : Density) (x : Position) (v : Velocity)
    (hf : Integrable (fun w : Velocity => f (x, w)))
    (hm : Integrable (fun w : Velocity => ‖w‖ * f (x, w))) :
    Integrable (fun w : Velocity => ‖v - w‖ * f (x, w)) := by
  have hfa : Integrable (fun w : Velocity => |f (x, w)|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hb := (hfa.const_mul ‖v‖).add (integrable_abs_firstMoment f x hm)
  apply hb.mono' ((by fun_prop : AEStronglyMeasurable (fun w : Velocity => ‖v - w‖)).mul
    hf.aestronglyMeasurable)
  filter_upwards [] with w
  exact frequency_integrand_norm_le f x v w

/-- An absolute bound valid for signed densities as well as nonnegative ones. -/
theorem abs_frequency_le (f : Density) (x : Position) (v : Velocity)
    (hf : Integrable (fun w : Velocity => f (x, w)))
    (hm : Integrable (fun w : Velocity => ‖w‖ * f (x, w))) :
    |frequency f x v| ≤ 2 * Real.pi *
      (‖v‖ * (∫ w : Velocity, |f (x, w)|) +
        ∫ w : Velocity, ‖w‖ * |f (x, w)|) := by
  have hfa : Integrable (fun w : Velocity => |f (x, w)|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hma := integrable_abs_firstMoment f x hm
  have hi := integrable_frequency_integrand f x v hf hm
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  calc
    |frequency f x v| = 2 * Real.pi * |∫ w : Velocity, ‖v - w‖ * f (x, w)| := by
      rw [frequency, abs_mul, abs_of_nonneg hπ]
    _ ≤ 2 * Real.pi * (∫ w : Velocity, ‖‖v - w‖ * f (x, w)‖) :=
      mul_le_mul_of_nonneg_left (by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun w : Velocity => ‖v - w‖ * f (x, w))) hπ
    _ ≤ 2 * Real.pi * (∫ w : Velocity,
        ‖v‖ * |f (x, w)| + ‖w‖ * |f (x, w)|) := by
      apply mul_le_mul_of_nonneg_left _ hπ
      exact integral_mono_ae hi.norm ((hfa.const_mul ‖v‖).add hma)
        (Filter.Eventually.of_forall (frequency_integrand_norm_le f x v))
    _ = _ := by rw [integral_add (hfa.const_mul ‖v‖) hma, integral_const_mul]

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

/-- The majorant has every natural polynomial velocity moment. -/
theorem integrable_moment_H {q : ℝ} (hq : q < 2) (n : ℕ) :
    Integrable (fun v : Velocity => ‖v‖ ^ n * H q v) := by
  have hn : AEStronglyMeasurable (fun v : Velocity => ‖v‖ ^ n) := by fun_prop
  apply ((integrable_H hq).add (integrable_even_moment_H hq n)).mono'
    (hn.mul (integrable_H hq).aestronglyMeasurable)
  filter_upwards [] with v
  have hpow : ‖v‖ ^ n ≤ 1 + ‖v‖ ^ (2 * n) := by
    rw [mul_comm 2 n, pow_mul]
    nlinarith [sq_nonneg (‖v‖ ^ n - (1 / 2 : ℝ))]
  rw [Pi.mul_apply, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (H_nonneg q v))]
  calc
    ‖v‖ ^ n * H q v ≤ (1 + ‖v‖ ^ (2 * n)) * H q v :=
      mul_le_mul_of_nonneg_right hpow (H_nonneg q v)
    _ = _ := by simp only [Pi.add_apply] <;> ring

end BoltzmannNonuniqueness.VelocityWeight

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

private theorem radial_integrable {b r : ℝ} (hb : 0 < b) (hr : -3 < r) :
    Integrable (fun v : Velocity => ‖v‖ ^ r * kernel b v) := by
  apply (integrable_fun_norm_addHaar (volume : Measure Velocity)
    (f := fun t : ℝ => t ^ r * Real.exp (-b * t ^ 2))).mpr
  have hi : IntegrableOn (fun t : ℝ => t ^ (r + 2) * Real.exp (-b * t ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hb (by linarith)
  apply hi.congr_fun _ measurableSet_Ioi
  intro t ht
  have ht' : 0 < t := ht
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  rw [Real.rpow_add ht' r 2, Real.rpow_two]
  ring

theorem kernel_integrable {b : ℝ} (hb : 0 < b) : Integrable (kernel b) := by
  simpa only [Real.rpow_zero, one_mul] using radial_integrable (r := 0) hb (by norm_num)

theorem moment_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : Velocity => ‖v‖ * kernel b v) := by
  simpa only [Real.rpow_one] using radial_integrable (r := 1) hb (by norm_num)

theorem mass_nonneg : 0 ≤ mass := integral_nonneg (fun _ => (Real.exp_pos _).le)
theorem moment_nonneg : 0 ≤ moment := integral_nonneg (fun _ => by
  exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)

theorem kernel_le {b : ℝ} (hb : 1 ≤ b) (v : Velocity) : kernel b v ≤ kernel 1 v := by
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ‖v‖]

theorem integral_kernel_le {b : ℝ} (hb : 1 ≤ b) : (∫ v, kernel b v) ≤ mass :=
  integral_mono (kernel_integrable (lt_of_lt_of_le zero_lt_one hb))
    (kernel_integrable zero_lt_one) (kernel_le hb)

theorem integral_moment_le {b : ℝ} (hb : 1 ≤ b) :
    (∫ v : Velocity, ‖v‖ * kernel b v) ≤ moment :=
  integral_mono (moment_integrable (lt_of_lt_of_le zero_lt_one hb))
    (moment_integrable zero_lt_one)
    (fun v => mul_le_mul_of_nonneg_left (kernel_le hb v) (norm_nonneg v))

theorem centered_scaled_eq {d : ℝ} (hd : 0 < d) (b : ℝ) (u v : Velocity) :
    ‖v - u‖ * JetThermalLaw.scaled d u (kernel b) v =
      d * JetThermalLaw.scaled d u (fun w => ‖w‖ * kernel b w) v := by
  unfold JetThermalLaw.scaled
  dsimp only
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  field_simp

theorem centered_scaled_integrable {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (u : Velocity) :
    Integrable (fun v => ‖v - u‖ * JetThermalLaw.scaled d u (kernel b) v) := by
  simpa only [centered_scaled_eq hd b u] using
    (JetThermalLaw.integrable_scaled (moment_integrable hb) hd u).const_mul d

theorem integral_centered_scaled {d : ℝ} (hd : 0 < d) (b : ℝ) (u : Velocity) :
    (∫ v, ‖v - u‖ * JetThermalLaw.scaled d u (kernel b) v) =
      d * (∫ v : Velocity, ‖v‖ * kernel b v) := by
  simp_rw [centered_scaled_eq hd b u]
  rw [integral_const_mul, JetThermalLaw.integral_scaled _ hd u]

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

theorem nonneg {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (b : ℝ) (u v : Velocity) :
    0 ≤ density c b d u v := by
  unfold density JetThermalLaw.scaled kernel
  positivity

theorem integrable {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (c : ℝ) (u : Velocity) :
    Integrable (density c b d u) :=
  (JetThermalLaw.integrable_scaled (kernel_integrable hb) hd u).const_mul c

theorem centered_integrable {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (c : ℝ) (u : Velocity) :
    Integrable (fun v => ‖v - u‖ * density c b d u v) := by
  convert (centered_scaled_integrable hb hd u).const_mul c using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  unfold density
  ring

theorem mass_le {c b d : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b) (hd : 0 < d) (u : Velocity) :
    (∫ v, density c b d u v) ≤ c * mass := by
  simp only [density]
  rw [integral_const_mul, JetThermalLaw.integral_scaled _ hd u]
  exact mul_le_mul_of_nonneg_left (integral_kernel_le hb) hc

theorem centered_moment_le {c b d : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b) (hd : 0 < d)
    (u : Velocity) : (∫ v, ‖v - u‖ * density c b d u v) ≤ c * d * moment := by
  calc
    _ = c * (∫ v, ‖v - u‖ * JetThermalLaw.scaled d u (kernel b) v) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with v
      unfold density
      ring
    _ = c * d * (∫ v : Velocity, ‖v‖ * kernel b v) := by
      rw [integral_centered_scaled hd]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_moment_le hb) (mul_nonneg hc hd.le)

theorem first_moment_integrable {c b d : ℝ} (hc : 0 ≤ c) (hb : 0 < b) (hd : 0 < d)
    (u : Velocity) : Integrable (fun v => ‖v‖ * density c b d u v) := by
  apply ((integrable hb hd c u).const_mul ‖u‖ |>.add (centered_integrable hb hd c u)).mono'
    ((by fun_prop : AEStronglyMeasurable (fun v : Velocity => ‖v‖)).mul
      (integrable hb hd c u).aestronglyMeasurable)
  filter_upwards [] with v
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (nonneg hc hd.le b u v))]
  have hnorm : ‖v‖ ≤ ‖u‖ + ‖v - u‖ := by
    have := norm_add_le u (v - u)
    simpa only [add_sub_cancel, add_comm] using this
  simpa only [Pi.add_apply, add_mul] using mul_le_mul_of_nonneg_right hnorm (nonneg hc hd.le b u v)

theorem frequency_le {c b d : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b) (hd : 0 < d)
    (u v : Velocity) (x : Position) :
    frequency (fun p => density c b d u p.2) x v ≤
      2 * Real.pi * c * (mass * ‖v - u‖ + moment * d) := by
  have hbpos := lt_of_lt_of_le zero_lt_one hb
  have hi := integrable_frequency_integrand (fun p => density c b d u p.2) x v
    (integrable hbpos hd c u) (first_moment_integrable hc hbpos hd u)
  have hmaj := ((integrable hbpos hd c u).const_mul ‖v - u‖).add
    (centered_integrable hbpos hd c u)
  have hbound : (∫ w, ‖v - w‖ * density c b d u w) ≤
      ‖v - u‖ * (∫ w, density c b d u w) + ∫ w, ‖w - u‖ * density c b d u w := by
    calc
      _ ≤ ∫ w, ‖v - u‖ * density c b d u w + ‖w - u‖ * density c b d u w := by
        apply integral_mono hi hmaj
        intro w
        have hnorm : ‖v - w‖ ≤ ‖v - u‖ + ‖w - u‖ := by
          simpa only [sub_sub_sub_cancel_right, norm_sub_rev] using norm_sub_le (v - u) (w - u)
        simpa only [Pi.add_apply, add_mul] using mul_le_mul_of_nonneg_right hnorm (nonneg hc hd.le b u w)
      _ = _ := by rw [integral_add ((integrable hbpos hd c u).const_mul _) (centered_integrable hbpos hd c u), integral_const_mul]
  have hm := mul_le_mul_of_nonneg_left (mass_le hc hb hd u) (norm_nonneg (v - u))
  have hj := centered_moment_le hc hb hd u
  unfold frequency
  calc
    _ ≤ 2 * Real.pi * (‖v - u‖ * (c * mass) + c * d * moment) :=
      mul_le_mul_of_nonneg_left (hbound.trans (add_le_add hm hj)) (by positivity)
    _ = _ := by ring

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ChartPointLift
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

end BoltzmannNonuniqueness.ChartKernel

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarriers
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

theorem transverse_velocity_bound {d : ℝ} (hd : 0 < d) (η K α γ s : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : JetPrototype.density η K α γ s d a p ≠ 0) :
    ‖transverse p.2‖ < d := by
  have hthermal : JetThermalLaw.density d (center α γ s a p.1.2) p.2 ≠ 0 :=
    right_ne_zero_of_mul hp
  have hdist : ‖p.2 - center α γ s a p.1.2‖ < d :=
    lt_of_not_ge (fun h => hthermal (JetThermalLaw.density_zero hd _ _ h))
  have hn := norm_sq_split (p.2 - center α γ s a p.1.2)
  have he : transverse (p.2 - center α γ s a p.1.2) = transverse p.2 := by
    rw [PlaneChart.transverse_sub, JetPrototype.center, PlaneChart.transverse_join, sub_zero]
  rw [he] at hn
  have hle : ‖transverse p.2‖ ≤ ‖p.2 - center α γ s a p.1.2‖ := by
    nlinarith [norm_nonneg (transverse p.2), norm_nonneg (p.2 - center α γ s a p.1.2),
      sq_nonneg (axial (p.2 - center α γ s a p.1.2))]
  exact hle.trans_lt hdist

/-- A free core remains in the transverse enlargement once `t d ≤ δ_s`. -/
theorem free_core_transverse {t d η s : ℝ} (ht : 0 ≤ t) (hd : 0 < d)
    (hwidth : t * d ≤ enlargementWidth η s) (K α γ : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : JetPrototype.density η K α γ s d a p ≠ 0) :
    p.1.1 + t • transverse p.2 ∈ enlargement η s a := by
  have hmask := (initial_spatial_support η K α γ s d a hp).1
  apply mem_cthickening_of_dist_le _ p.1.1 _ _ hmask
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_left (transverse_velocity_bound hd η K α γ s a hp).le ht).trans hwidth

/-- Axial free flight stays inside the manuscript's interval enlargement. -/
theorem free_core_axial {t d α : ℝ} (ht : 0 ≤ t) (hd : 0 < d) (hdmax : d ≤ 1 / 64)
    (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4) (η K γ s : ℝ) (a : Bool)
    {p : JetPrototype.Phase} (hp : JetPrototype.density η K α γ s d a p ≠ 0) :
    |p.1.2 + t * axial p.2| ≤ 1 / 8 + 2 * t + 1 / 16 := by
  have hz := (initial_spatial_support η K α γ s d a hp).2
  have hv := density_support_two hd hdmax hα hαmax η K γ s a hp
  have hn := norm_sq_split p.2
  have ha : |axial p.2| ≤ ‖p.2‖ := by
    nlinarith [sq_abs (axial p.2), abs_nonneg (axial p.2), norm_nonneg p.2,
      sq_nonneg ‖transverse p.2‖]
  have htri := abs_add_le p.1.2 (t * axial p.2)
  rw [abs_mul, abs_of_nonneg ht] at htri
  have htime := mul_le_mul_of_nonneg_left (ha.trans hv.le) ht
  linarith

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

/-- The constant is independent of the jet label, thermal width and position. -/
theorem frequency_bound {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space)
    (z : Position) (v : Velocity) :
    frequency (fun p => barrier η K α γ s d t a (x, p.2)) z v ≤
      frequencyConstant * (K / s) * (d + ‖v - centerVelocity α γ s t a x‖) := by
  have hc := massScale_nonneg hK hs η α γ d t a x
  have hcle := massScale_le hK hs hd ht htmax η α γ a x
  have hb : 1 ≤ 2 - t := by linarith
  simp_rw [barrier_eq_density hd]
  have hf := GaussianFrequency.frequency_le hc hb hd (centerVelocity α γ s t a x) v z
  have hlinear : JetGaussianMoments.mass * ‖v - centerVelocity α γ s t a x‖ +
      JetGaussianMoments.moment * d ≤
      (JetGaussianMoments.mass + JetGaussianMoments.moment) *
        (d + ‖v - centerVelocity α γ s t a x‖) := by
    nlinarith [mul_nonneg JetGaussianMoments.mass_nonneg hd.le,
      mul_nonneg JetGaussianMoments.moment_nonneg (norm_nonneg (v - centerVelocity α γ s t a x))]
  calc
    _ ≤ _ := hf
    _ ≤ 2 * Real.pi * massScale η K α γ s d t a x *
        ((JetGaussianMoments.mass + JetGaussianMoments.moment) *
          (d + ‖v - centerVelocity α γ s t a x‖)) :=
      mul_le_mul_of_nonneg_left hlinear (mul_nonneg (by positivity) hc)
    _ ≤ 2 * Real.pi * (Real.exp 4 * JetThermalKernel.bound * (K / s)) *
        ((JetGaussianMoments.mass + JetGaussianMoments.moment) *
          (d + ‖v - centerVelocity α γ s t a x‖)) := by
      apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcle (by positivity))
      exact mul_nonneg (add_nonneg JetGaussianMoments.mass_nonneg JetGaussianMoments.moment_nonneg)
        (add_nonneg hd.le (norm_nonneg _))
    _ = _ := by unfold frequencyConstant; ring

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

/-! # The full unperiodized cold datum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy

namespace BoltzmannNonuniqueness.JetDatum

theorem term_measurable (s₀ η K α γ d₀ : ℝ) (i : Index) :
    Measurable (term s₀ η K α γ d₀ i) := measurable_density _ _ _ _ _ _ _

end BoltzmannNonuniqueness.JetDatum

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

theorem free_le_barrier {K d α γ s t : ℝ} (hK : 0 ≤ K) (hd : 0 < d) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 < t) (htmax : t ≤ 2)
    (η : ℝ) (a : Bool) (p : JetPrototype.Phase) :
    free η K α γ s d t a p ≤ barrier η K α γ s d t a p := by
  have h := free_core_le_barrier hK hd hα hγ hs ht htmax η a (flight (-t) p)
  simpa only [free, flight_neg] using h

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd
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

/-! # Cutoff-independent loss bounds on a cold free core -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness
namespace CollisionCutoff

theorem frequency_le_majorant_ae (b : ℝ) {f g : Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ w, 0 ≤ f w) (hfg : ∀ᵐ w, f w ≤ g w)
    (v : Velocity) (hg : Integrable (fun w => ‖v-w‖*g w)) :
    frequency b f v ≤ 2*Real.pi*(∫ w, ‖v-w‖*g w) := by
  have hn (w : Velocity) : 0 ≤ rate b v w*f w := mul_nonneg (rate_nonneg b v w) (hfn w)
  have hb : ∀ᵐ w, rate b v w*f w ≤ ‖v-w‖*g w := by
    filter_upwards [hfg] with w hw
    have hr : rate b v w ≤ ‖v-w‖ := by
      unfold rate
      split_ifs <;> simp only [le_refl,norm_nonneg]
    exact (mul_le_mul_of_nonneg_right hr (hfn w)).trans
      (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
  have hi : Integrable (fun w => rate b v w*f w) := by
    apply hg.mono' ((measurable_rate b v).mul hfm).aestronglyMeasurable
    filter_upwards [hb] with w hw
    change ‖rate b v w*f w‖ ≤ ‖v-w‖*g w
    rwa [Real.norm_of_nonneg (hn w)]
  exact mul_le_mul_of_nonneg_left (integral_mono_ae hi hg hb) (by positivity)

end CollisionCutoff

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetCoreConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Mixed gain of the complete cold supersolution -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetEnvelopeGain

theorem thermal_width_le {d₀ s : ℝ} (hd₀max : d₀ ≤ 1) (hs : 0 ≤ s) (hsmax : s ≤ 1 / 8) :
    d₀ * s ^ 10 ≤ 1 / 16 := by
  calc
    _ ≤ 1 * (1 / 8 : ℝ) ^ 10 := mul_le_mul hd₀max (pow_le_pow_left₀ hs hsmax 10)
      (pow_nonneg hs _) (by norm_num)
    _ ≤ _ := by norm_num

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedBranchingBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # Weak calculus for the actual damped characteristic formula -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

theorem damped_eq (L c : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    damped L c g t = Real.exp (-L*t)*c +
      ∫ r in 0..t, Real.exp (-L*(t-r))*g r := by
  unfold damped
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  dsimp
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Quantitative survival for positive characteristic equations -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

theorem survival_of_derivative_bound {a b : ℝ} (hab : a ≤ b)
    {f r E k : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hE : ContDiff ℝ 1 E) (hE' : ∀ t, HasDerivAt E (k t) t)
    (hr : ∀ᵐ t, t ∈ Icc a b → HasDerivAt f (r t) t)
    (hb : ∀ᵐ t, t ∈ Icc a b → -k t*f t ≤ r t) :
    Real.exp (E a-E b)*f a ≤ f b := by
  let W : ℝ → ℝ := fun t => Real.exp (E t)*f t
  have hExp : ContDiff ℝ 1 (fun t => Real.exp (E t)) := Real.contDiff_exp.comp hE
  have hW : AbsolutelyContinuousOnInterval W a b :=
    hExp.contDiffOn.absolutelyContinuousOnInterval.mul hf
  have hd : ∀ᵐ t, t ∈ Icc a b → 0 ≤ deriv W t := by
    filter_upwards [hr,hb] with t ht hb htmem
    have h := ((hE' t).exp).mul (ht htmem)
    change HasDerivAt W _ t at h
    rw [h.deriv]
    have hp := mul_le_mul_of_nonneg_left (hb htmem) (Real.exp_pos (E t)).le
    nlinarith only [hp]
  have hi : 0 ≤ ∫ t in a..b, deriv W t := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    filter_upwards [ae_restrict_of_ae hd,ae_restrict_mem measurableSet_Icc] with t ht hm
    exact ht hm
  rw [hW.integral_deriv_eq_sub] at hi
  have hh : Real.exp (E a)*f a ≤ Real.exp (E b)*f b := sub_nonneg.mp hi
  have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-E b)).le
  have hleft : Real.exp (-E b)*(Real.exp (E a)*f a) = Real.exp (E a-E b)*f a := by
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hright : Real.exp (-E b)*(Real.exp (E b)*f b) = f b := by
    rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]
  rwa [hleft,hright] at hh'

theorem damped_absolutelyContinuous {T L c : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T) :
    AbsolutelyContinuousOnInterval (damped L c g) 0 T := by
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-L*t)) := by fun_prop
  have hi : IntervalIntegrable (fun r => Real.exp (L*r)*g r) volume 0 T :=
    hg.continuousOn_mul (by fun_prop)
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 T := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  exact he.contDiffOn.absolutelyContinuousOnInterval.mul (hc.add hp)

theorem damped_derivative_ae {T L c : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T) :
    ∀ᵐ t, t ∈ uIcc (0:ℝ) T →
      HasDerivAt (damped L c g) (g t-L*damped L c g t) t := by
  have hi : IntervalIntegrable (fun r => Real.exp (L*r)*g r) volume 0 T :=
    hg.continuousOn_mul (by fun_prop)
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht hm
  have hp := (ht hm 0 left_mem_uIcc).const_add c
  have he := ((hasDerivAt_id t).const_mul (-L)).exp
  have hd := he.mul hp
  have hexp : Real.exp (-L*t)*Real.exp (L*t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  refine hd.congr_deriv (Eq.symm ?_)
  · dsimp only [damped]
    dsimp only [id_eq] at hexp ⊢
    nlinarith only [congrArg (fun x : ℝ => x*g t) hexp]

theorem damped_survival {T L c : ℝ} (hT : 0 ≤ T) {g E k : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T)
    (hE : ContDiff ℝ 1 E) (hE' : ∀ t, HasDerivAt E (k t) t)
    (hb : ∀ᵐ t, t ∈ Icc 0 T →
      (L-k t)*damped L c g t ≤ g t) :
    Real.exp (E 0-E T)*c ≤ damped L c g T := by
  have hr : ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (damped L c g) (g t-L*damped L c g t) t := by
    simpa only [uIcc_of_le hT] using damped_derivative_ae hg
  have hb' : ∀ᵐ t, t ∈ Icc 0 T →
      -k t*damped L c g t ≤ g t-L*damped L c g t := by
    filter_upwards [hb] with t ht hm
    nlinarith only [ht hm]
  have h := survival_of_derivative_bound hT (damped_absolutelyContinuous hg) hE hE' hr hb'
  simpa only [damped,intervalIntegral.integral_same,add_zero,mul_zero,Real.exp_zero,one_mul] using h

end BoltzmannNonuniqueness.TransportPrimitive

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

/-! # Uniform frequency control by a cold core and the cap weight -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem H_frequency_integrable {q : ℝ} (hq : q < 2) (v : Velocity) :
    Integrable (fun w => ‖v-w‖*H q w) :=
  integrable_frequency_integrand (fun p => H q p.2) 0 v (integrable_H hq)
    (by simpa only [pow_one] using integrable_moment_H hq 1)

theorem H_frequency_le {q V : ℝ} (hq : q < 2) {v : Velocity} (hv : ‖v‖ ≤ V) :
    frequency (fun p => H q p.2) 0 v ≤ weightFrequencyConstant q V := by
  have h := abs_frequency_le (fun p => H q p.2) 0 v (integrable_H hq)
    (by simpa only [pow_one] using integrable_moment_H hq 1)
  simp only [abs_of_nonneg (H_nonneg q _)] at h
  apply (le_abs_self _).trans (h.trans ?_)
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right hv (integral_nonneg (H_nonneg q))) le_rfl)
    (by positivity)

theorem integral_rate_sum (f g : Velocity → ℝ) (v : Velocity) (A : ℝ)
    (hf : Integrable (fun w => ‖v-w‖*f w))
    (hg : Integrable (fun w => ‖v-w‖*g w)) :
    2*Real.pi*(∫ w, ‖v-w‖*(2*f w+A*g w)) =
      2*frequency (fun p => f p.2) 0 v+A*frequency (fun p => g p.2) 0 v := by
  have he : (fun w => ‖v-w‖*(2*f w+A*g w)) =
      (fun w => 2*(‖v-w‖*f w)+A*(‖v-w‖*g w)) := by
    funext w
    ring
  rw [he,integral_add (hf.const_mul 2) (hg.const_mul A),integral_const_mul,integral_const_mul]
  unfold frequency
  ring

namespace JetSupersolution

theorem core_add_weight_frequency_bound_ae {K s d α γ t q A V : ℝ}
    (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (ht : 0 < t) (htmax : t ≤ 1) (hε : epsilon K s d ≤ 1)
    (hq : q < 2) (hA : 0 ≤ A) (η b : ℝ) (a : Bool) (x : JetPrototype.Space)
    {f : Velocity → ℝ} (hfm : Measurable f) (hfn : ∀ w, 0 ≤ f w)
    (hfU : ∀ᵐ w, f w ≤ U η K α γ s d t a (x,w)+A*H q w)
    {v : Velocity} (hv : ‖v-JetBarrier.centerVelocity α γ s t a x‖ ≤ d)
    (hvV : ‖v‖ ≤ V) :
    CollisionCutoff.frequency b f v ≤ 4*JetBarrierCollision.frequencyConstant*K*d/s+
      A*weightFrequencyConstant q V := by
  let B : Velocity → ℝ := fun w => JetBarrier.barrier η K α γ s d t a (x,w)
  have hc := JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x
  have hβ : 0 < 2-t := by linarith
  have hBi : Integrable (fun w => ‖v-w‖*B w) := by
    apply integrable_frequency_integrand (fun p => B p.2) 0 v
    · simpa only [B,JetBarrierCollision.barrier_eq_density hd] using
        GaussianFrequency.integrable hβ hd
          (JetBarrierCollision.massScale η K α γ s d t a x)
          (JetBarrier.centerVelocity α γ s t a x)
    · simpa only [B,JetBarrierCollision.barrier_eq_density hd] using
        GaussianFrequency.first_moment_integrable hc hβ hd
          (JetBarrier.centerVelocity α γ s t a x)
  have hHi := H_frequency_integrable hq v
  have hsum : Integrable (fun w => ‖v-w‖*(2*B w+A*H q w)) := by
    convert (hBi.const_mul 2).add (hHi.const_mul A) using 1
    all_goals try with_reducible_and_instances rfl
    funext w
    simp only [Pi.add_apply]
    ring
  have hfg : ∀ᵐ w, f w ≤ 2*B w+A*H q w := by
    filter_upwards [hfU] with w hw
    exact hw.trans (add_le_add
      (le_twice_barrier hK hs hd hα hγ ht htmax hε η a (x,w)) le_rfl)
  have hf := CollisionCutoff.frequency_le_majorant_ae b hfm hfn hfg v hsum
  rw [integral_rate_sum B (H q) v A hBi hHi] at hf
  have hbar := JetBarrierCollision.frequency_bound hK hs hd ht htmax η α γ a x 0 v
  change frequency (fun p => B p.2) 0 v ≤ _ at hbar
  have hcoef : 0 ≤ JetBarrierCollision.frequencyConstant*(K/s) :=
    mul_nonneg JetBarrierCollision.frequencyConstant_nonneg (div_nonneg hK hs.le)
  have hcore : 2*frequency (fun p => B p.2) 0 v ≤
      4*JetBarrierCollision.frequencyConstant*K*d/s := by
    have hb' := hbar.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hv) hcoef)
    calc
      _ ≤ 2*(JetBarrierCollision.frequencyConstant*(K/s)*(d+d)) := by linarith only [hb']
      _ = _ := by ring
  exact hf.trans (add_le_add hcore (mul_le_mul_of_nonneg_left (H_frequency_le hq hvV) hA))

end JetSupersolution
end BoltzmannNonuniqueness

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ColdMildRepresentative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The polynomial optical depth used in the cold-core survival estimate -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem coldOpticalDepth_zero (B A δ D : ℝ) (m : ℕ) :
    coldOpticalDepth B A δ D m 0 = 0 := by
  simp [coldOpticalDepth]

theorem coldOpticalDepth_derivative (B A δ D : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (coldOpticalDepth B A δ D m) (B+A*(t+δ)+D*t^m) t := by
  have hB : HasDerivAt (fun t : ℝ => B*t) B t := by
    simpa using (hasDerivAt_id t).const_mul B
  have hA : HasDerivAt (fun t : ℝ => A*(t^2/2+δ*t)) (A*(t+δ)) t := by
    refine (((((hasDerivAt_id t).pow 2).div_const 2 |>.add
      ((hasDerivAt_id t).const_mul δ)).const_mul A).congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)).congr_deriv (Eq.symm ?_)
    · beta_reduce
      simp only [Pi.add_apply,Pi.pow_apply,id_eq]
    · simp only [id_eq]
      ring
  have hD : HasDerivAt (fun t : ℝ => D*t^(m+1)/(m+1)) (D*t^m) t := by
    refine (((((hasDerivAt_id t).pow (m+1)).const_mul D).div_const (m+1:ℝ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => ?_)).congr_deriv (Eq.symm ?_)
    · beta_reduce
      simp only [Pi.pow_apply,id_eq]
    · simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_one,id_eq]
      field_simp
  exact (hB.add hA).add hD

end BoltzmannNonuniqueness

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

end BoltzmannNonuniqueness.JetCopyDatum

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

/-! # Separating the main cold color from escaped colors and the hot cap -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem frequency_at_main {s₀ η K α γ d₀ q t z e V : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (ht : 0 < t) (htmax : t ≤ 1/32) (hq : q < 2) (hz : 0 ≤ z) (he : 0 ≤ e)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ) (x : Velocity) (i : Label) (hi : x ∈ spatialEnlargement s₀ η t i)
    {F : Velocity → ℝ} (hFm : Measurable F) (hFn : ∀ w, 0 ≤ F w)
    (c : Label → Velocity → ℝ) (hcs : ∀ w, Summable (fun j => c j w))
    (hzero : ∀ j, ¬j.annulus < N → ∀ w, c j w = 0)
    (hhot : ∀ᵐ w, F w-(∑' j, c j w) ≤ z)
    (htail : ∀ w, (∑' j, escaped s₀ η t N x (fun k => c k w) j) ≤ e)
    (hcU : ∀ w, H q w*c i w ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
      (JetSpatialBox.shifted x i.lattice,w)) (b : ℝ) {v : Velocity}
    (hv : ‖v-JetBarrier.centerVelocity α γ (jetScale s₀ η i.annulus) t i.positive
      (JetSpatialBox.shifted x i.lattice)‖ ≤ d₀*jetScale s₀ η i.annulus^10)
    (hvV : ‖v‖ ≤ V) :
    CollisionCutoff.frequency b (fun w => H q w*F w) v ≤
      4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9+
        (z+e)*weightFrequencyConstant q V := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
  have hout (j : Label) (_hj : j.annulus < N) (hji : j ≠ i) :
      JetLatticeTail.outside η (jetScale s₀ η j.annulus) t j.positive x j.lattice := by
    apply (outside_iff_not_mem s₀ η t x j).mpr
    intro hj
    exact hji (common_point_label hs₀ hsmax hη hηmax htmax hj hi)
  have hrem : ∀ᵐ w, F w-c i w ≤ z+e := by
    filter_upwards [hhot] with w hw
    have he := sum_sub_main (hcs w) (fun j hj => hzero j hj w) i hi hout
    linarith only [he,hw,htail w]
  have hupper : ∀ᵐ w, H q w*F w ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10) t i.positive
      (JetSpatialBox.shifted x i.lattice,w)+(z+e)*H q w := by
    filter_upwards [hrem] with w hw
    have hh := mul_le_mul_of_nonneg_left hw (H_nonneg q w)
    nlinarith only [hh,hcU w]
  have hf := JetSupersolution.core_add_weight_frequency_bound_ae hK hs (by positivity) hα hγ
    ht (htmax.trans (by norm_num))
    (JetEscapedEnvelope.epsilon_small hK hd₀.le hs (JetEscapedTotal.scale_bound hs₀ hη _) hsmall)
    hq (add_nonneg hz he) η b i.positive (JetSpatialBox.shifted x i.lattice)
    ((ChartKernel.measurable_H q).mul hFm) (fun w => mul_nonneg (H_nonneg q w) (hFn w))
    hupper hv hvV
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [jetScale]
  field_simp

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Every retained free-core flight stays in its own main color -/

noncomputable section

open Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem color_initial_core {s₀ η K α γ d₀ q : ℝ} {N : ℕ} {i : Label}
    {p : JetPrototype.Phase} (hp : color s₀ η K α γ d₀ q N i p ≠ 0) :
    JetPrototype.density η K α γ (jetScale s₀ η i.annulus)
      (d₀*jetScale s₀ η i.annulus^10) i.positive (shift (displacement i.lattice) p) ≠ 0 := by
  have hi : i.annulus < N := by
    by_contra hi
    exact hp (by simp only [color,ite_eq_right hi])
  intro hz
  apply hp
  simp only [color,ite_eq_left hi,JetDatum.term,hz,zero_div]

theorem shifted_flight_position (t : ℝ) (p : JetPrototype.Phase) (n : Lattice) :
    JetSpatialBox.shifted (PlaneChart.join (JetBarrier.flight t p).1.1
      (JetBarrier.flight t p).1.2) n = (JetBarrier.flight t (shift (displacement n) p)).1 := by
  apply Prod.ext
  · simp only [JetSpatialBox.shifted,PlaneChart.transverse_join]
    change (p.1.1+t • VelocityWeight.transverse p.2)-transverseShift n =
      (p.1.1-transverseShift n)+t • VelocityWeight.transverse p.2
    abel
  · change (p.1.2+t*VelocityWeight.axial p.2)-axialShift n =
      (p.1.2-axialShift n)+t*VelocityWeight.axial p.2
    ring

theorem central_enlargement_coordinates {s₀ η t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (htmax : t ≤ 1/32)
    {i : Label} (hi0 : i.lattice = 0) {x : Velocity}
    (hx : x ∈ spatialEnlargement s₀ η t i) : ∀ k, |x k| ≤ 1 := by
  have htzero : transverseShift (0 : Lattice) = 0 := by ext k; simp [transverseShift]
  have hy := hx.1
  have hz := hx.2
  rw [hi0,htzero,sub_zero] at hy
  have hz' : |VelocityWeight.axial x| ≤ 1/8+2*t+1/16 := by
    simpa only [hi0,axialShift,Pi.zero_apply,Int.cast_zero,sub_zero] using hz
  have hyt := enlargement_inside_baseBall hs₀ hη i.annulus i.positive hy
  rw [Metric.mem_ball,dist_zero_right] at hyt
  have hsquare := VelocityWeight.norm_sq_split x
  have hxnorm : ‖x‖ ≤ 1 := by
    have hysq : ‖VelocityWeight.transverse x‖^2 ≤ (1/8:ℝ)^2 := by
      nlinarith [norm_nonneg (VelocityWeight.transverse x)]
    have hzabs : |VelocityWeight.axial x| ≤ 1/4 := by linarith only [hz',htmax]
    have hzsq : (VelocityWeight.axial x)^2 ≤ (1/4:ℝ)^2 := by
      nlinarith [sq_abs (VelocityWeight.axial x),abs_nonneg (VelocityWeight.axial x)]
    nlinarith [norm_nonneg x]
  intro k
  have hk : |x k| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x k
  exact hk.trans hxnorm

theorem color_flight_geometry {s₀ η K α γ d₀ q t : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (ht : 0 ≤ t) (i : Label) (p : JetPrototype.Phase)
    (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
    (hwidth : t*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
    (hp : color s₀ η K α γ d₀ q N i p ≠ 0) :
    PlaneChart.join (JetBarrier.flight t p).1.1 (JetBarrier.flight t p).1.2 ∈
      spatialEnlargement s₀ η t i ∧
    ‖p.2-JetBarrier.centerVelocity α γ (jetScale s₀ η i.annulus) t i.positive
      (JetSpatialBox.shifted (PlaneChart.join (JetBarrier.flight t p).1.1
        (JetBarrier.flight t p).1.2) i.lattice)‖ ≤ d₀*jetScale s₀ η i.annulus^10 ∧
    ‖p.2‖ ≤ 2 := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
  have hd : 0 < d₀*jetScale s₀ η i.annulus^10 := by positivity
  have hcore := color_initial_core hp
  have hy := JetSupport.free_core_transverse ht hd hwidth K α γ i.positive hcore
  have hz := JetSupport.free_core_axial ht hd hdmax hα hαmax η K γ
    (jetScale s₀ η i.annulus) i.positive hcore
  constructor
  · change (JetSpatialBox.shifted (PlaneChart.join (JetBarrier.flight t p).1.1
      (JetBarrier.flight t p).1.2) i.lattice).1 ∈ _ ∧
      |(JetSpatialBox.shifted (PlaneChart.join (JetBarrier.flight t p).1.1
        (JetBarrier.flight t p).1.2) i.lattice).2| ≤ _
    rw [shifted_flight_position]
    exact ⟨hy,hz⟩
  constructor
  · rw [shifted_flight_position]
    exact (JetCoreFlight.error_lt_width hd hα hγ hs ht η K i.positive hcore).le
  · exact (JetSupport.density_support_two hd hdmax hα hαmax η K γ
      (jetScale s₀ η i.annulus) i.positive hcore).le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildCharacteristics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The weak characteristic equation of the constructed mild states -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_along_flight {T t : ℝ} (ht : t ∈ Icc 0 T) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ)
    (p : JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (t,JetBarrier.flight t p) =
      TransportPrimitive.damped L (f₀ p) (fun r => g (r,JetBarrier.flight r p)) t := by
  rw [TransportPrimitive.damped_eq]
  unfold value
  rw [GaussianLocal.time_eq ht,JetFreeTransport.neg_flight]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [JetFreeTransport.flight_add,sub_add_cancel]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveIntegralBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Scalar characteristic representatives for a.e. mild solutions -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem ae_characteristic_path {T t L : ℝ} (ht : t ∈ Icc 0 T)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀ : Measurable f₀)
    {F g : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hgm : Measurable g)
    (hmild : ∀ s ∈ Icc 0 T, (fun p => F (s,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => value T L JetBarrier.flight f₀ g (s,p))) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      ((fun r => F (r,JetBarrier.flight r p)) =ᵐ[volume.restrict (Icc (0:ℝ) t)]
        (fun r => TransportPrimitive.damped L (f₀ p)
          (fun s => g (s,JetBarrier.flight s p)) r)) ∧
      F (t,JetBarrier.flight t p) = TransportPrimitive.damped L (f₀ p)
        (fun s => g (s,JetBarrier.flight s p)) t := by
  let A : ℝ × JetPrototype.Phase → ℝ := fun z => F (z.1,JetBarrier.flight z.1 z.2)
  let B : ℝ × JetPrototype.Phase → ℝ := fun z =>
    value T L JetBarrier.flight f₀ g (z.1,JetBarrier.flight z.1 z.2)
  have hflow : Measurable (fun z : ℝ × JetPrototype.Phase =>
      (z.1,JetBarrier.flight z.1 z.2)) :=
    measurable_fst.prodMk GaussianLocal.measurable_flight
  have hAm : Measurable A := hFm.comp hflow
  have hBm : Measurable B := (measurable_value (ht.1.trans ht.2)
    GaussianLocal.measurable_flight hf₀ hgm).comp hflow
  have hslice (r : ℝ) (hr : r ∈ Icc 0 T) :
      (fun p => A (r,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => B (r,p)) :=
    (FlightMeasure.flight_measurePreserving r).quasiMeasurePreserving.ae (hmild r hr)
  have hall : A =ᵐ[(volume.restrict (Icc 0 t)).prod FlightMeasure.phaseVolume] B := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hAm hBm)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hslice r ⟨hr.1,hr.2.trans ht.2⟩
  have hp := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume)
      (ν := volume.restrict (Icc 0 t))).quasiMeasurePreserving.ae hall)
  filter_upwards [hp,hslice t ht] with p hpe hend
  constructor
  · filter_upwards [hpe,ae_restrict_mem measurableSet_Icc] with r hr hrmem
    exact hr.trans (value_along_flight ⟨hrmem.1,hrmem.2.trans ht.2⟩ L f₀ g p)
  · exact hend.trans (value_along_flight ht L f₀ g p)

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CharacteristicCoordinates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Almost-everywhere velocity-fiber bounds along almost every free path -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem measurableSet_ae_velocity_bound {X : Type*} [MeasurableSpace X]
    {f : X × Velocity → ℝ} {A : X → ℝ} (hf : Measurable f) (hA : Measurable A) :
    MeasurableSet {x | ∀ᵐ w : Velocity, f (x,w) ≤ A x} := by
  let B : Set (X × Velocity) := {z | A z.1 < f z}
  have hB : MeasurableSet B := measurableSet_lt (hA.comp measurable_fst) hf
  have hm : Measurable (fun x : X => (volume : Measure Velocity) (Prod.mk x ⁻¹' B)) :=
    measurable_measure_prodMk_left hB
  have he : {x | ∀ᵐ w : Velocity, f (x,w) ≤ A x} =
      {x | (volume : Measure Velocity) (Prod.mk x ⁻¹' B) = 0} := by
    ext x
    simp only [mem_ofPred_eq,ae_iff,not_le]
    rfl
  rw [he]
  exact measurableSet_eq_fun hm measurable_const

theorem ae_velocity_bound_along_paths {T : ℝ} {F : ℝ × JetPrototype.Phase → ℝ}
    {A : ℝ → ℝ} (hFm : Measurable F) (hAm : Measurable A)
    (hbound : ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume, F (t,p) ≤ A t) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) T),
      ∀ᵐ w : Velocity, F (t,((JetBarrier.flight t p).1,w)) ≤ A t := by
  have hm : Measurable (fun z : (ℝ × JetPrototype.Phase) × Velocity =>
      F (z.1.1,((JetBarrier.flight z.1.1 z.1.2).1,z.2))) := by
    apply hFm.comp
    exact measurable_fst.fst.prodMk
      ((GaussianLocal.measurable_flight.comp measurable_fst).fst.prodMk measurable_snd)
  have hP := measurableSet_ae_velocity_bound hm (hAm.comp measurable_fst)
  have hall : ∀ᵐ z ∂(volume.restrict (Icc (0:ℝ) T)).prod FlightMeasure.phaseVolume,
      ∀ᵐ w : Velocity, F (z.1,((JetBarrier.flight z.1 z.2).1,w)) ≤ A z.1 := by
    apply (Measure.ae_prod_iff_ae_ae hP).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hs : ∀ᵐ x ∂JetPrototype.spaceVolume, ∀ᵐ w : Velocity, F (t,(x,w)) ≤ A t :=
      Measure.ae_ae_of_ae_prod (hbound t ht)
    have hl : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ᵐ w : Velocity, F (t,(p.1,w)) ≤ A t :=
      Measure.quasiMeasurePreserving_fst.ae hs
    exact (FlightMeasure.flight_measurePreserving t).quasiMeasurePreserving.ae hl
  exact Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume)
      (ν := volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae hall)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedCharacteristic
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Cold-core survival for the a.e. representatives in the actual cap construction -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem ColdMildAE.survival {q b L T R t : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F c : ℝ × JetPrototype.Phase → ℝ} {c₀ : JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : Measurable c) (hc₀m : Measurable c₀)
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ z, 0 ≤ c z ∧ c z ≤ R)
    (hceq : ColdMildAE q b L T F c₀ c) (ht : t ∈ Icc 0 T)
    (E k : JetPrototype.Phase → ℝ → ℝ)
    (hE : ∀ p, ContDiff ℝ 1 (E p)) (hE' : ∀ p r, HasDerivAt (E p) (k p r) r)
    (hν : ∀ᵐ p ∂FlightMeasure.phaseVolume, c₀ p ≠ 0 → ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) t),
      CollisionCutoff.frequency b (fun v => physical q F (r,((JetBarrier.flight r p).1,v))) p.2 ≤ k p r) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      Real.exp (E p 0-E p t)*c₀ p ≤ c (t,JetBarrier.flight t p) := by
  have hpath := PositiveIntegral.ae_characteristic_path ht hc₀m hcm
    (measurable_coldForcing hFm hcm q b L) hceq
  filter_upwards [hpath,hν] with p hp hνp
  by_cases hpzero : c₀ p = 0
  · rw [hpzero,mul_zero]
    exact (hc (t,JetBarrier.flight t p)).1
  have hνp := hνp hpzero
  let g : ℝ → ℝ := fun r => coldForcing q b L F c (r,JetBarrier.flight r p)
  let S : ℝ := HotApplication.realBound q*R^2+L*R
  have hgb (r : ℝ) : 0 ≤ g r ∧ g r ≤ S :=
    HotRepresentative.coldSource_bounds hq hb hR hloss
      (GaussianLocal.measurable_state hFm) (GaussianLocal.measurable_state hcm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hc (p.1.1,(p.1.2,p.2))) _
  have hgm : Measurable g := (measurable_coldForcing hFm hcm q b L).comp
    (measurable_id.prodMk (GaussianLocal.measurable_flight.comp
      (measurable_id.prodMk measurable_const)))
  have hgi : IntervalIntegrable g volume 0 t := by
    apply (intervalIntegrable_const (c := S)).mono_fun' hgm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun r => by
      change ‖g r‖ ≤ S
      rw [Real.norm_eq_abs,abs_of_nonneg (hgb r).1]
      exact (hgb r).2)
  have hpe := hp.1
  change ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) t), c (r,JetBarrier.flight r p) =
    TransportPrimitive.damped L (c₀ p) g r at hpe
  rw [ae_restrict_iff' measurableSet_Icc] at hpe hνp
  have hbound : ∀ᵐ r, r ∈ Icc 0 t →
      (L-k p r)*TransportPrimitive.damped L (c₀ p) g r ≤ g r := by
    filter_upwards [hpe,hνp] with r hpr hνr hr
    rw [← hpr hr]
    have hgain := HotRepresentative.gain_nonneg
      (fun p => (hc (p.1.1,(p.1.2,p.2))).1) q b ((r,(JetBarrier.flight r p).1),p.2)
    change 0 ≤ HotRepresentative.gain q b (GaussianLocal.state c)
      ((r,(JetBarrier.flight r p).1),p.2) at hgain
    change (L-k p r)*c (r,JetBarrier.flight r p) ≤
      HotRepresentative.gain q b (GaussianLocal.state c) ((r,(JetBarrier.flight r p).1),p.2)+
        (L-CollisionCutoff.frequency b (fun v => physical q F
          (r,((JetBarrier.flight r p).1,v))) p.2)*c (r,JetBarrier.flight r p)
    exact (mul_le_mul_of_nonneg_right (sub_le_sub_left (hνr hr) L)
      (hc (r,JetBarrier.flight r p)).1).trans (le_add_of_nonneg_left hgain)
  rw [hp.2]
  exact TransportPrimitive.damped_survival ht.1 hgi (hE p) (hE' p) hbound

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetContinuation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The complete core loss estimate from the hot cap and proved escaped tails -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem frequency_at_main_cap {s₀ η K α γ d₀ q t δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hq : q < 2) (hδ : 0 ≤ δ)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (m N : ℕ) (x : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (i : Label) (hi : x ∈ spatialEnlargement s₀ η t i)
    {F : Velocity → ℝ} (hFm : Measurable F) (hFn : ∀ w, 0 ≤ F w)
    (c : Label → Velocity → ℝ) (hcn : ∀ j w, 0 ≤ c j w)
    (hcs : ∀ w, Summable (fun j => c j w))
    (hzero : ∀ j, ¬j.annulus < N → ∀ w, c j w = 0)
    (hhot : ∀ᵐ w, F w-(∑' j, c j w) ≤ t+δ)
    (hcU : ∀ j w, H q w*c j w ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j.annulus) (d₀*jetScale s₀ η j.annulus^10) t j.positive
      (JetSpatialBox.shifted x j.lattice,w)) (b : ℝ) {v : Velocity}
    (hv : ‖v-JetBarrier.centerVelocity α γ (jetScale s₀ η i.annulus) t i.positive
      (JetSpatialBox.shifted x i.lattice)‖ ≤ d₀*jetScale s₀ η i.annulus^10)
    (hv2 : ‖v‖ ≤ 2) :
    CollisionCutoff.frequency b (fun w => H q w*F w) v ≤
      4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9+
        weightFrequencyConstant q 2*(t+δ)+escapedFrequencyConstant s₀ η α K d₀ q m*t^m := by
  let C := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m:ℝ))
  have hC : 0 ≤ C := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _
  have htail (w : Velocity) : (∑' j, escaped s₀ η t N x (fun k => c k w) j) ≤ C*t^m := by
    simpa only [Real.rpow_natCast] using normalized_escaped_bound hs₀ hsmax hη hηmax
      hK hα hαmax hγ hd₀ hd₀max ht htmax hsmall (m:ℝ) q N
      (fun j => c j w) x w hx (fun j => hcn j w) (hcs w) (fun j _ => hcU j w)
  have h := frequency_at_main hs₀ hsmax hη hηmax hK hα hγ hd₀ ht htmax hq
    (add_nonneg ht.le hδ) (mul_nonneg hC (pow_nonneg ht.le m)) hsmall N x i hi
    hFm hFn c hcs hzero hhot htail (hcU i) b hv hv2
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold escapedFrequencyConstant C
  ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Quantitative survival of central cold colors under the actual cap bounds -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem survival_of_capped_family_q80_oai {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (m N : ℕ) (i : Label) (hi0 : i.lattice = 0)
    (hwidth : T*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
    (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : Label → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ j, Measurable (c j))
    (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R) (hc : ∀ j z, 0 ≤ c j z ∧ c j z ≤ R)
    (hmild : ColdMildAE q b L T F (color s₀ η K α γ d₀ q N i) (c i))
    (hsum : ∀ z, Summable (fun j => c j z))
    (hzero : ∀ j, ¬j.annulus < N → c j = 0)
    (hU : ∀ r ∈ Ioc 0 T, ∀ j p, H q p.2*c j (r,p) ≤ JetSupersolution.U η K α γ
      (jetScale s₀ η j.annulus) (d₀*jetScale s₀ η j.annulus^10) r j.positive
        (shift (displacement j.lattice) p))
    (hcap : ∀ r ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      F (r,p)-(∑' j, c j (r,p)) ≤ r+δ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      Real.exp (-coldOpticalDepth
        (4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9)
        (weightFrequencyConstant q 2) δ (escapedFrequencyConstant s₀ η α K d₀ q m) m t)*
        color s₀ η K α γ d₀ q N i p ≤ c i (t,JetBarrier.flight t p) := by
  let B := 4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9
  let A := weightFrequencyConstant q 2
  let D := escapedFrequencyConstant s₀ η α K d₀ q m
  have hhotm : Measurable (fun z => F z-∑' j, c j z) := hFm.sub (Measurable.tsum hcm)
  have hpath := ae_velocity_bound_along_paths (T := t) hhotm
    (show Measurable (fun r : ℝ => r+δ) by fun_prop)
    (fun r hr => hcap r ⟨hr.1,hr.2.trans ht.2⟩)
  have hν : ∀ᵐ p ∂FlightMeasure.phaseVolume,
      color s₀ η K α γ d₀ q N i p ≠ 0 →
      ∀ᵐ r ∂volume.restrict (Icc (0:ℝ) t),
        CollisionCutoff.frequency b (fun v => physical q F
          (r,((JetBarrier.flight r p).1,v))) p.2 ≤ B+A*(r+δ)+D*r^m := by
    filter_upwards [hpath] with p hp hp0
    filter_upwards [hp,ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 0)] with r hr hrmem hrne
    have hrpos : 0 < r := lt_of_le_of_ne hrmem.1 hrne.symm
    have hrT : r ≤ T := hrmem.2.trans ht.2
    have hgeom := color_flight_geometry hs₀ hα hαmax hγ hd₀ hrpos.le i p hdmax
      ((mul_le_mul_of_nonneg_right hrT (by positivity)).trans hwidth) hp0
    let x : Velocity := PlaneChart.join (JetBarrier.flight r p).1.1 (JetBarrier.flight r p).1.2
    have hx := central_enlargement_coordinates hs₀ hsmax hη
      (hrT.trans hTmax) hi0 hgeom.1
    have hrate := frequency_at_main_cap hs₀ hsmax hη hηmax hK hα
      (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hrpos (hrT.trans hTmax) hq hδ
      hsmall m N x hx i hgeom.1
      (hFm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id)))
      (fun w => (hF (r,((JetBarrier.flight r p).1,w))).1)
      (fun j w => c j (r,((JetBarrier.flight r p).1,w)))
      (fun j w => (hc j _).1) (fun w => hsum _)
      (fun j hj w => congrFun (hzero j hj) _)
      hr (fun j w => ?_) b hgeom.2.1 hgeom.2.2
    · exact hrate
    · simpa only [x,JetSpatialBox.shifted,PlaneChart.transverse_join,PlaneChart.axial_join,
        shift,displacement,Prod.sub_def] using hU r ⟨hrpos,hrT⟩ j ((JetBarrier.flight r p).1,w)
  have h := ColdMildAE.survival hq hb hR hloss hFm (hcm i)
    (measurable_color s₀ η K α γ d₀ q N i) hF (hc i) hmild ht
    (fun _ => coldOpticalDepth B A δ D m) (fun _ r => B+A*(r+δ)+D*r^m)
    (fun _ => by unfold coldOpticalDepth; fun_prop)
    (fun _ => coldOpticalDepth_derivative B A δ D m) hν
  simpa only [coldOpticalDepth_zero,zero_sub] using h

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.survival_of_capped_family_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.survival_of_capped_family_q80_oai
