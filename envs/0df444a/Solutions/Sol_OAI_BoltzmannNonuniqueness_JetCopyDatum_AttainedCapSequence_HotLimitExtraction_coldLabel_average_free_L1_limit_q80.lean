-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.coldLabel_average_free_L1_limit_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:08:05.541591+00:00
-- url     : https://prove2.me/submissions/51df5790-f21f-43de-b7e3-3bd24612ff56

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_rebuilt_envelope_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_survival_of_capped_family_q80

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

theorem continuous_velocity {σ α γ s t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    Continuous (velocity σ α γ s t) := by
  have hEq : velocity σ α γ s t = fun z => profile σ α γ s (foot σ α γ s t z) :=
    funext fun _ => velocity_spec hα
  rw [hEq]
  exact (continuous_profile σ α γ s).comp (foot_lipschitzWith hα hγ hs ht).continuous

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

theorem mass_nonneg : 0 ≤ mass := integral_nonneg (fun _ => (Real.exp_pos _).le)
theorem moment_nonneg : 0 ≤ moment := integral_nonneg (fun _ => by
  exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)

theorem kernel_le {b : ℝ} (hb : 1 ≤ b) (v : Velocity) : kernel b v ≤ kernel 1 v := by
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ‖v‖]

theorem integral_kernel_le {b : ℝ} (hb : 1 ≤ b) : (∫ v, kernel b v) ≤ mass :=
  integral_mono (kernel_integrable (lt_of_lt_of_le zero_lt_one hb))
    (kernel_integrable zero_lt_one) (kernel_le hb)

end BoltzmannNonuniqueness.JetGaussianMoments

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

theorem integrable {b d : ℝ} (hb : 0 < b) (hd : 0 < d) (c : ℝ) (u : Velocity) :
    Integrable (density c b d u) :=
  (JetThermalLaw.integrable_scaled (kernel_integrable hb) hd u).const_mul c

theorem mass_le {c b d : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b) (hd : 0 < d) (u : Velocity) :
    (∫ v, density c b d u v) ≤ c * mass := by
  simp only [density]
  rw [integral_const_mul, JetThermalLaw.integral_scaled _ hd u]
  exact mul_le_mul_of_nonneg_left (integral_kernel_le hb) hc

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.JetFreeTransport.flight_zero
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

section

/-! # Local mass bounds for the Gaussian cold barrier, uniform in thermal width -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetBarrier

namespace BoltzmannNonuniqueness.JetBarrierLocalMass

theorem massConstant_nonneg : 0 ≤ massConstant := by
  unfold massConstant
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le JetThermalKernel.bound_pos.le)
    JetGaussianMoments.mass_nonneg

theorem measurable_barrier {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (η K d : ℝ) (a : Bool) :
    Measurable (barrier η K α γ s d t a) := by
  have hv : Measurable (fun p : JetPrototype.Phase => AxialFlow.velocity (sign a) α γ s t p.1.2) :=
    (AxialFlow.continuous_velocity hα hγ hs ht).measurable.comp measurable_fst.snd
  have hc : Measurable (fun p : JetPrototype.Phase => centerVelocity α γ s t a p.1) :=
    SheetMeasures.join.measurable.comp (measurable_const.prodMk hv)
  have hf : Measurable (fun p : JetPrototype.Phase => AxialFlow.foot (sign a) α γ s t p.1.2) :=
    (AxialFlow.foot_lipschitzWith hα hγ hs ht).continuous.measurable.comp measurable_fst.snd
  have hx : Measurable (fun p : JetPrototype.Phase => distanceSquared η α γ s t a p.1) :=
    ((((continuous_infDist_pt (s := JetGeometry.mask η s a)).measurable.comp measurable_fst.fst).pow_const 2).add
      (((continuous_infDist_pt (s := Icc (-(1/8:ℝ)) (1/8))).measurable.comp hf).pow_const 2))
  unfold barrier exponent
  exact measurable_const.mul ((measurable_const.sub
    (measurable_const.mul ((measurable_snd.sub hc).norm.pow_const 2) |>.div_const _)).sub
    (measurable_const.mul hx |>.div_const _)).exp

theorem velocity_integrable {d t : ℝ} (hd : 0 < d) (htmax : t ≤ 1)
    (η K α γ s : ℝ) (a : Bool) (x : Space) :
    Integrable (fun v => barrier η K α γ s d t a (x,v)) := by
  simp_rw [JetBarrierCollision.barrier_eq_density hd]
  exact GaussianFrequency.integrable (by linarith) hd _ _

theorem velocity_integral_le {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space) :
    (∫ v, barrier η K α γ s d t a (x,v)) ≤ massConstant*(K/s) := by
  simp_rw [JetBarrierCollision.barrier_eq_density hd]
  apply (GaussianFrequency.mass_le (JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x)
    (by linarith) hd _).trans
  have h := mul_le_mul_of_nonneg_right
    (JetBarrierCollision.massScale_le hK hs hd ht htmax η α γ a x) JetGaussianMoments.mass_nonneg
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold massConstant
  ring

theorem local_integrable {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (η : ℝ) (a : Bool) (y : Space) (μ : Measure Space) [IsFiniteMeasure μ] :
    Integrable (fun p : JetPrototype.Phase => barrier η K α γ s d t a (p.1-y,p.2)) (μ.prod volume) := by
  have hm : Measurable (fun p : JetPrototype.Phase => barrier η K α γ s d t a (p.1-y,p.2)) :=
    (measurable_barrier hα hγ hs ht.le η K d a).comp
      ((measurable_fst.sub measurable_const).prodMk measurable_snd)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun x => velocity_integrable hd htmax η K α γ s a (x-y)),?_⟩
  apply Integrable.of_bound (hm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    (massConstant*(K/s))
  filter_upwards [] with x
  simp_rw [Real.norm_of_nonneg (barrier_nonneg hK hs.le hd.le η α γ t a _)]
  rw [Real.norm_of_nonneg (integral_nonneg (fun v => barrier_nonneg hK hs.le hd.le η α γ t a _))]
  exact velocity_integral_le hK hs hd ht htmax η α γ a (x-y)

theorem local_integral_le {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (htmax : t ≤ 1)
    (η : ℝ) (a : Bool) (y : Space) (μ : Measure Space) [IsFiniteMeasure μ] :
    (∫ p : JetPrototype.Phase, barrier η K α γ s d t a (p.1-y,p.2) ∂μ.prod volume) ≤
      μ.real univ*(massConstant*(K/s)) := by
  have hi := local_integrable hK hα hγ hs hd ht htmax η a y μ
  rw [integral_prod _ hi]
  have h := integral_mono_ae hi.integral_prod_left (integrable_const (massConstant*(K/s)))
    (ae_of_all _ (fun x => velocity_integral_le hK hs hd ht htmax η α γ a (x-y)))
  simpa only [integral_const,smul_eq_mul] using h

end BoltzmannNonuniqueness.JetBarrierLocalMass

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetPeriodicDatum
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd
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

end BoltzmannNonuniqueness.JetSupersolution

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

theorem epsilon_eq {s : ℝ} (hs : 0 < s) (K d₀ : ℝ) :
    JetSupersolution.epsilon K s (d₀ * s ^ 10) =
      JetComparisonCoefficient.coefficient K * d₀ * s ^ 9 := by
  unfold JetSupersolution.epsilon
  field_simp

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricMesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A compact logarithmic phase for the dilated geometric mesh -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

theorem normalization {a η : ℝ} (ha : 0 < a) (hη : η ≠ 0) :
    a = phase a η*Real.exp (η*(index a η:ℝ)) := by
  unfold phase index
  rw [← Real.exp_add]
  have he : η*Int.fract (Real.log a/η)+η*(⌊Real.log a/η⌋:ℝ) = Real.log a := by
    unfold Int.fract
    field_simp
    ring
  rw [he,Real.exp_log ha]

theorem scale_ratio {s₀ r η : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) (hη : η ≠ 0) (j : ℕ) :
    DatumBounds.scale s₀ η j/r = phase (s₀/r) η*
      Real.exp (η*((index (s₀/r) η:ℝ)-(j:ℝ))) := by
  calc
    _ = (s₀/r)*Real.exp (-(j:ℝ)*η) := by unfold DatumBounds.scale; ring
    _ = (phase (s₀/r) η*Real.exp (η*(index (s₀/r) η:ℝ)))*Real.exp (-(j:ℝ)*η) := by
      exact congrArg (fun a : ℝ => a*Real.exp (-(j:ℝ)*η)) (normalization (div_pos hs₀ hr) hη)
    _ = _ := by
      rw [mul_assoc,← Real.exp_add]
      congr 2
      ring

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Fixed limiting mesh points arise from actual annular indices -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

theorem index_tendsto_atTop {s₀ η : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => index (s₀/r n) η) atTop atTop := by
  have hr' : Tendsto r atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrlim,Eventually.of_forall hr⟩
  have hinv := tendsto_inv_nhdsGT_zero.comp hr'
  have hratio : Tendsto (fun n => s₀/r n) atTop atTop := by
    simpa only [div_eq_mul_inv,Function.comp_def] using hinv.const_mul_atTop hs₀
  exact tendsto_floor_atTop.comp ((Real.tendsto_log_atTop.comp hratio).atTop_div_const hη)

theorem annularIndex_eventually {s₀ η : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0)) (k : ℤ) :
    ∀ᶠ n in atTop, (index (s₀/r n) η:ℝ)-(annularIndex s₀ η r k n:ℝ) = (k:ℝ) := by
  filter_upwards [(index_tendsto_atTop hs₀ hη hr hrlim).eventually_ge_atTop k] with n hn
  have he : (annularIndex s₀ η r k n:ℤ) = index (s₀/r n) η-k :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hn)
  have he' : (annularIndex s₀ η r k n:ℝ) = (index (s₀/r n) η:ℝ)-(k:ℝ) := by
    exact_mod_cast he
  rw [he']
  ring

theorem mesh_point_approximation {s₀ η θ : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (k : ℤ) :
    Tendsto (fun n => DatumBounds.scale s₀ η (annularIndex s₀ η r k n)/r n)
      atTop (𝓝 (θ*Real.exp (η*(k:ℝ)))) := by
  apply (hphase.mul_const (Real.exp (η*(k:ℝ)))).congr'
  filter_upwards [annularIndex_eventually hs₀ hη hr hrlim k] with n hn
  rw [scale_ratio hs₀ (hr n) hη.ne',hn]

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Retention of limiting mesh points above the terminal scale -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

theorem eventually_retained {s₀ η θ l : ℝ} {r : ℕ → ℝ} {N : ℕ → ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ))
    (hbottom : Tendsto (fun n => DatumBounds.scale s₀ η (N n)/r n) atTop (𝓝 l))
    (k : ℤ) (hk : l < θ*Real.exp (η*(k:ℝ))) :
    ∀ᶠ n in atTop, annularIndex s₀ η r k n < N n := by
  have he := hbottom.eventually_lt (mesh_point_approximation hs₀ hη hr hrlim hphase k) hk
  filter_upwards [he] with n hn
  by_contra h
  have hle := JetGeometry.scale_antitone hs₀.le hη.le (le_of_not_gt h)
  exact (not_lt_of_ge hle) ((div_lt_div_iff_of_pos_right (hr n)).mp hn)

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # The annular label uses the geometric scale with index shifted by one -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

theorem annularIndex_eventually_pos {s₀ η : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0)) (k : ℤ) :
    ∀ᶠ n in atTop, 0 < annularIndex s₀ η r k n := by
  filter_upwards [(index_tendsto_atTop hs₀ hη hr hrlim).eventually_ge_atTop (k+1)] with n hn
  unfold annularIndex
  omega

theorem jetIndex_succ_eventually {s₀ η : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0)) (k : ℤ) :
    ∀ᶠ n in atTop, jetIndex s₀ η r k n+1 = annularIndex s₀ η r k n := by
  filter_upwards [annularIndex_eventually_pos hs₀ hη hr hrlim k] with n hn
  exact Nat.sub_add_cancel hn

theorem jet_scale_approximation {s₀ η θ : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (k : ℤ) :
    Tendsto (fun n => JetGeometry.jetScale s₀ η (jetIndex s₀ η r k n)/r n)
      atTop (𝓝 (θ*Real.exp (η*(k:ℝ)))) := by
  apply (mesh_point_approximation hs₀ hη hr hrlim hphase k).congr'
  filter_upwards [jetIndex_succ_eventually hs₀ hη hr hrlim k] with n hn
  exact congrArg (fun j => DatumBounds.scale s₀ η j/r n) hn.symm

theorem jetIndex_eventually_retained {s₀ η θ l : ℝ} {r : ℕ → ℝ} {N : ℕ → ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ))
    (hbottom : Tendsto (fun n => DatumBounds.scale s₀ η (N n+1)/r n) atTop (𝓝 l))
    (k : ℤ) (hk : l < θ*Real.exp (η*(k:ℝ))) :
    ∀ᶠ n in atTop, jetIndex s₀ η r k n < N n := by
  filter_upwards [eventually_retained hs₀ hη hr hrlim hphase hbottom k hk,
    jetIndex_succ_eventually hs₀ hη hr hrlim k] with n hn he
  omega

end BoltzmannNonuniqueness.GeometricMesh

end

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

section

/-! # Countable positive sums in the characteristic equation -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P I : Type*} [MeasurableSpace P] [Countable I]

theorem hasSum_value {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : I → P → ℝ) (hf₀ : ∀ p, Summable (fun i => f₀ i p))
    (g : I → Domain P → ℝ) (hgm : ∀ i, Measurable (g i))
    (hg : ∀ i z, 0 ≤ g i z ∧ g i z ≤ S)
    (hgs : ∀ z, Summable (fun i => g i z)) (hgb : ∀ z, (∑' i, g i z) ≤ S)
    (z : Domain P) : HasSum (fun i => value T L flow (f₀ i) (g i) z)
      (value T L flow (fun p => ∑' i, f₀ i p) (fun q => ∑' i, g i q) z) := by
  have hsm : Measurable (fun q => ∑' i, g i q) := Measurable.tsum hgm
  have hsa (q) : |∑' i, g i q| ≤ S := by
    rw [abs_of_nonneg (tsum_nonneg (fun i => (hg i q).1))]
    exact hgb q
  have hgi (i) := damped_integrable hT hL hflow (hgm i)
    (fun q => by rw [abs_of_nonneg (hg i q).1]; exact (hg i q).2) z
  have hi := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := 0) (b := time T z.1) (μ := volume)
    (F := fun i r => Real.exp (-L * (time T z.1 - r)) * g i (r, flow (r - time T z.1) z.2))
    (f := fun r => Real.exp (-L * (time T z.1 - r)) *
      ∑' i, g i (r, flow (r - time T z.1) z.2))
    (fun i r => Real.exp (-L * (time T z.1 - r)) * g i (r, flow (r - time T z.1) z.2))
    (fun i => (hgi i).def'.aestronglyMeasurable)
    (fun i => ae_of_all _ (fun r _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hg i _).1)]))
    (ae_of_all _ (fun r _ => (hgs _).mul_left _))
    (by
      simpa only [tsum_mul_left] using damped_integrable hT hL hflow hsm hsa z)
    (ae_of_all _ (fun r _ => (hgs _).hasSum.mul_left _))
  exact ((hf₀ _).hasSum.mul_left (Real.exp (-L * time T z.1))).add hi

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveIntegralTime
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Restarting the mild equation at an intermediate time -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem restart {T L S s t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (f₀ : JetPrototype.Phase → ℝ) {g : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hg : ∀ z, |g z| ≤ S) (p : JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g (t,p) =
      Real.exp (-L*(t-s)) * value T L JetBarrier.flight f₀ g (s,JetBarrier.flight (s-t) p) +
      ∫ r in s..t, Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p) := by
  have ht0 : 0 ≤ t := hs.trans hst
  have hti : time T t = t := GaussianLocal.time_eq ⟨ht0,ht⟩
  have hsi : time T s = s := GaussianLocal.time_eq ⟨hs,hst.trans ht⟩
  let a (r : ℝ) := Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)
  have hi : IntervalIntegrable a volume 0 t := by
    have h := damped_integrable hT hL GaussianLocal.measurable_flight hgm hg (t,p)
    simpa only [hti] using h
  have his : IntervalIntegrable a volume 0 s := by
    apply hi.mono_set
    rw [uIcc_of_le hs,uIcc_of_le ht0]
    exact Icc_subset_Icc le_rfl hst
  have hist : IntervalIntegrable a volume s t := by
    apply hi.mono_set
    rw [uIcc_of_le hst,uIcc_of_le ht0]
    exact Icc_subset_Icc hs le_rfl
  have hinit : Real.exp (-L*(t-s))*value T L JetBarrier.flight f₀ g (s,JetBarrier.flight (s-t) p) =
      Real.exp (-L*t)*f₀ (JetBarrier.flight (-t) p) + ∫ r in 0..s,a r := by
    unfold value
    rw [hsi,mul_add,← intervalIntegral.integral_const_mul]
    congr 1
    · rw [JetFreeTransport.flight_add]
      have he : -s+(s-t) = -t := by ring
      rw [he,← mul_assoc,← Real.exp_add]
      congr 2
      ring
    · apply intervalIntegral.integral_congr
      intro r _
      dsimp only [a]
      rw [JetFreeTransport.flight_add]
      have he : r-s+(s-t) = r-t := by ring
      rw [he,← mul_assoc,← Real.exp_add]
      congr 2
      ring
  rw [hinit]
  change value T L JetBarrier.flight f₀ g (t,p) = _ + ∫ r in s..t,a r
  unfold value
  rw [hti,← intervalIntegral.integral_add_adjacent_intervals his hist]
  ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Time regularity along the free paths without continuity of translations -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem along_time_bound {T L S R s t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (_hS : 0 ≤ S) (_hR : 0 ≤ R) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hg : ∀ z, |g z| ≤ S) (hfB : ∀ z, |f z| ≤ R)
    (hf : ∀ z, f z = value T L JetBarrier.flight f₀ g z) (p : JetPrototype.Phase) :
    |f (t,p)-f (s,JetBarrier.flight (s-t) p)| ≤ (L*R+S)*(t-s) := by
  have hr := restart hT hL hs hst ht f₀ hgm hg p
  rw [← hf (t,p),← hf (s,JetBarrier.flight (s-t) p)] at hr
  have he : Real.exp (-L*(t-s)) ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (sub_nonneg.mpr hst))
  have hediff : |Real.exp (-L*(t-s))-1| ≤ L*(t-s) := by
    rw [abs_of_nonpos (sub_nonpos.mpr he)]
    have ha := Real.add_one_le_exp (-L*(t-s))
    linarith
  have hi : |∫ r in s..t, Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)| ≤ S*(t-s) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := t) (C := S)
      (f := fun r => Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)) (by
        intro r hrt
        rw [uIoc_of_le hst] at hrt
        rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
        have hx : Real.exp (-L*(t-r)) ≤ 1 := Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (sub_nonneg.mpr hrt.2))
        exact (mul_le_mul hx (hg _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul S))
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hst)] using hh
  have hsB := hfB (s,JetBarrier.flight (s-t) p)
  have hiB : |(Real.exp (-L*(t-s))-1)*f (s,JetBarrier.flight (s-t) p)| ≤ L*(t-s)*R := by
    rw [abs_mul]
    exact mul_le_mul hediff hsB (abs_nonneg _) (mul_nonneg hL (sub_nonneg.mpr hst))
  calc
    _ = |(Real.exp (-L*(t-s))-1)*f (s,JetBarrier.flight (s-t) p) +
        ∫ r in s..t, Real.exp (-L*(t-r))*g (r,JetBarrier.flight (r-t) p)| := by
      rw [hr]
      congr 1
      ring
    _ ≤ L*(t-s)*R+S*(t-s) := (abs_add_le _ _).trans (add_le_add hiB hi)
    _ = _ := by ring

end BoltzmannNonuniqueness.PositiveIntegral

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

/-! # The essential supremum norm along free transport -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PhaseEssSup

open FlightMeasure

theorem size_le {f : JetPrototype.Phase → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hfm : Measurable f) (hf : ∀ p, |f p| ≤ R) : size f ≤ R := by
  have he : eLpNorm f ∞ phaseVolume ≤ ENNReal.ofReal R := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hf p))
  simpa only [size,ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he

theorem size_difference {f g : JetPrototype.Phase → ℝ} {A B D : ℝ}
    (hD : 0 ≤ D) (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, |f p| ≤ A) (hg : ∀ p, |g p| ≤ B) (hfg : ∀ p, |f p-g p| ≤ D) :
    |size f-size g| ≤ D := by
  have hfp : MemLp f ∞ phaseVolume := memLp_top_of_bound hfm.aestronglyMeasurable A
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hf p))
  have hgp : MemLp g ∞ phaseVolume := memLp_top_of_bound hgm.aestronglyMeasurable B
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using hg p))
  calc
    _ = |‖hfp.toLp f‖-‖hgp.toLp g‖| := by rw [Lp.norm_toLp,Lp.norm_toLp]; rfl
    _ ≤ ‖hfp.toLp f-hgp.toLp g‖ := abs_norm_sub_norm_le _ _
    _ = size (fun p => f p-g p) := by rw [← MemLp.toLp_sub,Lp.norm_toLp]; rfl
    _ ≤ D := size_le hD (hfm.sub hgm) hfg

theorem size_flight {f : JetPrototype.Phase → ℝ} (hfm : Measurable f) (t : ℝ) :
    size (fun p => f (JetBarrier.flight t p)) = size f := by
  unfold size
  exact congrArg ENNReal.toReal
    (eLpNorm_comp_measurePreserving hfm.aestronglyMeasurable (flight_measurePreserving t))

theorem time_difference {T L S R s t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hR : 0 ≤ R) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ z, |g z| ≤ S) (hfB : ∀ z, |f z| ≤ R)
    (hf : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ g z) :
    |size (fun p => f (t,p))-size (fun p => f (s,p))| ≤ (L*R+S)*(t-s) := by
  have hfs : Measurable (fun p => f (s,p)) := hfm.comp (measurable_const.prodMk measurable_id)
  have hh := size_difference (mul_nonneg (add_nonneg (mul_nonneg hL hR) hS) (sub_nonneg.mpr hst))
    (hfm.comp (measurable_const.prodMk measurable_id))
    (hfs.comp (flight_measurePreserving (s-t)).measurable)
    (fun p => hfB (t,p)) (fun p => hfB (s,JetBarrier.flight (s-t) p))
    (PositiveIntegral.along_time_bound hT hL hS hR hs hst ht hgm hg hfB hf)
  change |size (fun p => f (t,p))-size (fun p => f (s,JetBarrier.flight (s-t) p))| ≤ _ at hh
  rw [size_flight hfs] at hh
  exact hh

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Continuity of the cap ratio in the essential weighted norm -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem continuousOn_size {T L S R : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hR : 0 ≤ R)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ z, |g z| ≤ S) (hfB : ∀ z, |f z| ≤ R)
    (hf : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ g z) :
    ContinuousOn (fun t => size (fun p => f (t,p))) (Icc 0 T) := by
  let C : NNReal := ⟨L*R+S,add_nonneg (mul_nonneg hL hR) hS⟩
  have hLip : LipschitzOnWith C (fun t => size (fun p => f (t,p))) (Icc 0 T) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro s hs t ht
    simp only [Real.dist_eq]
    change |size (fun p => f (s,p))-size (fun p => f (t,p))| ≤ (L*R+S)*|s-t|
    rcases le_total s t with hst | hts
    · rw [abs_sub_comm (size _),abs_sub_comm s t,abs_of_nonneg (sub_nonneg.mpr hst)]
      exact time_difference hT hL hS hR hs.1 hst ht.2 hgm hfm hg hfB hf
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
      exact time_difference hT hL hS hR ht.1 hts hs.2 hgm hfm hg hfB hf
  exact hLip.continuousOn

end BoltzmannNonuniqueness.PhaseEssSup

end

end

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

section

/-! # Global norm continuity for the clamped local construction -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem continuous_size {T L S R : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hR : 0 ≤ R)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ u, |g u| ≤ S) (hfB : ∀ u, |f u| ≤ R)
    (hf : ∀ u, f u = PositiveIntegral.value T L JetBarrier.flight f₀ g u) :
    Continuous (fun t => size (fun p => f (t,p))) := by
  have he (t : ℝ) (p : JetPrototype.Phase) :
      f (t,p) = f (PositiveIntegral.time T t,p) := by
    rw [hf (t,p),hf (PositiveIntegral.time T t,p)]
    simp only [PositiveIntegral.value,time_idempotent hT]
  have hn : (fun t => size (fun p => f (t,p))) =
      (fun t => size (fun p => f (PositiveIntegral.time T t,p))) := by
    funext t
    exact congrArg size (funext (he t))
  rw [hn]
  exact (continuousOn_size hT hL hS hR hgm hfm hg hfB hf).comp_continuous
    (by unfold PositiveIntegral.time; fun_prop) (PositiveIntegral.time_bounds hT)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Essential-norm estimates for mild equations holding almost everywhere -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem size_congr_ae {f g : JetPrototype.Phase → ℝ}
    (hfg : f =ᵐ[FlightMeasure.phaseVolume] g) : size f = size g :=
  congrArg ENNReal.toReal (eLpNorm_congr_ae hfg)

theorem continuous_size_of_mildAE {T L A S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hS : 0 ≤ S) {f₀ : JetPrototype.Phase → ℝ}
    {f g : ℝ × JetPrototype.Phase → ℝ}
    (hf₀m : Measurable f₀) (hgm : Measurable g)
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) (hg : ∀ u, 0 ≤ g u ∧ g u ≤ S)
    (hfix : ∀ t, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :
    Continuous (fun t => size (fun p => f (t,p))) := by
  let v := PositiveIntegral.value T L JetBarrier.flight f₀ g
  have hvm : Measurable v := PositiveIntegral.measurable_value hT GaussianLocal.measurable_flight hf₀m hgm
  have hv (u) := PositiveIntegral.value_bounds hT hL hA hS JetBarrier.flight hf₀ hg u
  have hga (u) : |g u| ≤ S := by rw [abs_of_nonneg (hg u).1]; exact (hg u).2
  have hva (u) : |v u| ≤ A+T*S := by rw [abs_of_nonneg (hv u).1]; exact (hv u).2
  have he : (fun t => size (fun p => f (t,p))) = (fun t => size (fun p => v (t,p))) :=
    funext (fun t => size_congr_ae (hfix t))
  rw [he]
  exact continuous_size hT hL hS (by positivity) hgm hvm hga hva (fun _ => rfl)

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

/-! # Subtracting two bounded characteristic integral equations -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem value_sub {T L S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    {g h : ℝ × JetPrototype.Phase → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ u, |g u| ≤ S) (hh : ∀ u, |h u| ≤ S)
    (f₀ k₀ : JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g u-value T L JetBarrier.flight k₀ h u =
      value T L JetBarrier.flight (fun p => f₀ p-k₀ p) (fun z => g z-h z) u := by
  unfold value
  have he (r : ℝ) : Real.exp (-L*(time T u.1-r)) *
      (g (r,JetBarrier.flight (r-time T u.1) u.2)-h (r,JetBarrier.flight (r-time T u.1) u.2)) =
      Real.exp (-L*(time T u.1-r))*g (r,JetBarrier.flight (r-time T u.1) u.2)-
        Real.exp (-L*(time T u.1-r))*h (r,JetBarrier.flight (r-time T u.1) u.2) := mul_sub _ _ _
  simp_rw [he]
  rw [intervalIntegral.integral_sub
    (damped_integrable hT hL GaussianLocal.measurable_flight hgm hg u)
    (damped_integrable hT hL GaussianLocal.measurable_flight hhm hh u)]
  ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
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

section

/-! # Polynomial control of a hot remainder satisfying the mild equation a.e. -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem continuousOn_size_of_mildAE {T L A S : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hS : 0 ≤ S) {f₀ : JetPrototype.Phase → ℝ}
    {f g : ℝ × JetPrototype.Phase → ℝ}
    (hf₀m : Measurable f₀) (hgm : Measurable g)
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) (hg : ∀ u, 0 ≤ g u ∧ g u ≤ S)
    (hfix : ∀ t ∈ Icc 0 T, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :
    ContinuousOn (fun t => size (fun p => f (t,p))) (Icc 0 T) := by
  have hv : Continuous (fun t => size (fun p =>
      PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :=
    continuous_size_of_mildAE hT hL hA hS hf₀m hgm hf₀ hg (fun _ => ae_of_all _ (fun _ => rfl))
  apply hv.continuousOn.congr
  intro t ht
  exact size_congr_ae (hfix t ht)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedJetSolutions
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

/-! # Uniform frequency control by a cold core and the cap weight -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem weightFrequencyConstant_nonneg (q : ℝ) {V : ℝ} (hV : 0 ≤ V) :
    0 ≤ weightFrequencyConstant q V := by
  unfold weightFrequencyConstant
  exact mul_nonneg (by positivity) (add_nonneg
    (mul_nonneg hV (integral_nonneg (H_nonneg q)))
    (integral_nonneg (fun w => mul_nonneg (norm_nonneg w) (H_nonneg q w))))

end BoltzmannNonuniqueness

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

theorem shift_flight (y : Space) (t : ℝ) (p : JetPrototype.Phase) :
    shift y (JetBarrier.flight t p) = JetBarrier.flight t (shift y p) := by
  apply Prod.ext
  · apply Prod.ext <;> dsimp [shift,JetBarrier.flight] <;> abel
  · rfl

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

/-! # Vanishing labels stay absent from the cold iteration -/

noncomputable section

namespace BoltzmannNonuniqueness.WeightedLocal

theorem coldForcing_zero (q b L : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    coldForcing q b L F 0 = 0 := by
  funext z
  simp [coldForcing,HotRepresentative.coldSource,HotRepresentative.gain,
    HotRepresentative.density,GaussianLocal.state,KineticCollisionNullSets.gain,
    CollisionCutoff.gain,CollisionCutoff.integrand]

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

/-! # The polynomial optical depth used in the cold-core survival estimate -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem coldOpticalDepth_nonneg {B A δ D t : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (ht : 0 ≤ t) (m : ℕ) :
    0 ≤ coldOpticalDepth B A δ D m t := by
  unfold coldOpticalDepth
  positivity

end BoltzmannNonuniqueness

end

end

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

/-! # Total-variation control from the cold-core survival sandwich -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem abs_sub_le_of_survival {c f r E : ℝ} (hf : 0 ≤ f) (hr : 0 ≤ r)
    (hE : 0 ≤ E) (hlower : Real.exp (-E)*f ≤ c) (hupper : c ≤ f+r) :
    |c-f| ≤ E*f+r := by
  have he : 1-E ≤ Real.exp (-E) := by linarith only [Real.add_one_le_exp (-E)]
  have hmul := mul_le_mul_of_nonneg_right he hf
  apply abs_le.mpr
  constructor <;> nlinarith only [hlower,hupper,hmul,mul_nonneg hE hf,hr]

end BoltzmannNonuniqueness

end

end

section

/-! # Uniform optical-depth errors on bounded dilation windows -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem coldOpticalDepth_le_dilationError {C A D S U r s t δ : ℝ} (m : ℕ)
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hS : 0 ≤ S)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hsr : s ≤ S*r) (htr : t ≤ U*r) (hδr : δ ≤ r) :
    coldOpticalDepth (C*s^9) A δ D m t ≤ coldDilationError C A D S U m r := by
  have hfirst : C*s^9*t ≤ C*(S*r)^9*(U*r) := by gcongr
  have hsecond : A*(t^2/2+δ*t) ≤ A*((U*r)^2/2+r*(U*r)) := by gcongr
  have hthird : D*t^(m+1)/(m+1) ≤ D*(U*r)^(m+1)/(m+1) := by gcongr
  calc
    _ ≤ C*(S*r)^9*(U*r)+A*((U*r)^2/2+r*(U*r))+D*(U*r)^(m+1)/(m+1) :=
      add_le_add (add_le_add hfirst hsecond) hthird
    _ = _ := by unfold coldDilationError; rw [mul_pow]; ring

theorem coldDilationError_tendsto_zero (C A D S U : ℝ) (m : ℕ) :
    Tendsto (coldDilationError C A D S U m) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (coldDilationError C A D S U m) := by
    unfold coldDilationError
    fun_prop
  simpa [coldDilationError] using hc.continuousAt.tendsto (x := (0:ℝ))

theorem coldOpticalDepth_tendsto_zero {C A D S U : ℝ} {m : ℕ}
    {r s t δ : ℕ → ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hS : 0 ≤ S) (hr : ∀ n, 0 ≤ r n) (hs : ∀ n, 0 ≤ s n)
    (ht : ∀ n, 0 ≤ t n) (hδ : ∀ n, 0 ≤ δ n)
    (hsr : ∀ n, s n ≤ S*r n) (htr : ∀ n, t n ≤ U*r n) (hδr : ∀ n, δ n ≤ r n)
    (hrlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => coldOpticalDepth (C*s n^9) A (δ n) D m (t n)) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => coldOpticalDepth_nonneg (mul_nonneg hC (pow_nonneg (hs n) _))
      hA (hδ n) hD (ht n) m)
    (fun n => coldOpticalDepth_le_dilationError m hC hA hD hS
      (hr n) (hs n) (ht n) (hsr n) (htr n) (hδr n))
  exact (coldDilationError_tendsto_zero C A D S U m).comp hrlim

end BoltzmannNonuniqueness

end

end

section

/-! # The local cold error vanishes after the physical dilation -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem scaled_local_error_le {I E ε V C K r s a : ℝ}
    (hE : 0 ≤ E) (hε : 0 ≤ ε) (hV : 0 ≤ V) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hr : 0 < r) (hs : 0 < s) (ha : 0 < a) (has : a*r ≤ s)
    (hI : I ≤ (E+ε)*(r^3*V)*(C*(K/s))) :
    I/r^2 ≤ (E+ε)*(V*C*K/a) := by
  have hratio : r/s ≤ 1/a := (div_le_div_iff₀ hs ha).mpr (by nlinarith only [has])
  calc
    I/r^2 ≤ ((E+ε)*(r^3*V)*(C*(K/s)))/r^2 :=
      div_le_div_of_nonneg_right hI (sq_nonneg r)
    _ = (E+ε)*V*C*K*(r/s) := by field_simp
    _ ≤ (E+ε)*V*C*K*(1/a) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

theorem scaled_local_error_tendsto_zero {I E ε r s : ℕ → ℝ} {V C K a : ℝ}
    (hE : ∀ n, 0 ≤ E n) (hε : ∀ n, 0 ≤ ε n)
    (hV : 0 ≤ V) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hr : ∀ n, 0 < r n) (hs : ∀ n, 0 < s n) (ha : 0 < a)
    (has : ∀ n, a*r n ≤ s n) (hIn : ∀ n, 0 ≤ I n)
    (hI : ∀ n, I n ≤ (E n+ε n)*((r n)^3*V)*(C*(K/s n)))
    (hElim : Tendsto E atTop (𝓝 0)) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => I n/(r n)^2) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => div_nonneg (hIn n) (sq_nonneg _))
    (fun n => scaled_local_error_le (hE n) (hε n) hV hC hK (hr n) (hs n) ha (has n) (hI n))
  simpa only [zero_add,zero_mul] using (hElim.add hεlim).mul_const (V*C*K/a)

theorem jet_epsilon_tendsto_zero {r s : ℕ → ℝ} {S : ℝ}
    (hs : ∀ n, 0 < s n) (hsr : ∀ n, s n ≤ S*r n)
    (hrlim : Tendsto r atTop (𝓝 0)) (K d₀ : ℝ) :
    Tendsto (fun n => JetSupersolution.epsilon K (s n) (d₀*(s n)^10)) atTop (𝓝 0) := by
  have hslim : Tendsto s atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (hs n).le) hsr
    simpa only [mul_zero] using hrlim.const_mul S
  simp_rw [JetEscapedEnvelope.epsilon_eq (hs _)]
  simpa only [zero_pow (by norm_num : (9:ℕ) ≠ 0),mul_zero] using
    (hslim.pow 9).const_mul (JetComparisonCoefficient.coefficient K*d₀)

end BoltzmannNonuniqueness

end

end

section

/-! # The three-dimensional Jacobian in the cold dilation -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace BoltzmannNonuniqueness.ColdDilationMeasure

theorem space_finrank : Module.finrank ℝ JetPrototype.Space = 3 := by
  simp [JetPrototype.Space,VelocityWeight.Transverse,Module.finrank_prod]

theorem setIntegral_space_smul (f : JetPrototype.Space → ℝ) (Ω : Set JetPrototype.Space)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in Ω, f (r • x) ∂JetPrototype.spaceVolume) =
      (r^3)⁻¹*(∫ x in r • Ω, f x ∂JetPrototype.spaceVolume) := by
  simpa only [space_finrank,smul_eq_mul] using
    Measure.setIntegral_comp_smul_of_pos JetPrototype.spaceVolume f Ω hr

theorem dilated_error_integral (f : JetPrototype.Phase → ℝ) (Ω : Set JetPrototype.Space)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in Ω, ∫ v : Velocity, |r*f (r • x,v)| ∂volume ∂JetPrototype.spaceVolume) =
      (∫ x in r • Ω, ∫ v : Velocity, |f (x,v)| ∂volume ∂JetPrototype.spaceVolume)/r^2 := by
  simp_rw [abs_mul,abs_of_pos hr,integral_const_mul]
  rw [setIntegral_space_smul (fun x => ∫ v : Velocity, |f (x,v)|) Ω hr]
  field_simp

theorem spaceVolume_real_smul (Ω : Set JetPrototype.Space) {r : ℝ} (hr : 0 < r) :
    JetPrototype.spaceVolume.real (r • Ω) = r^3*JetPrototype.spaceVolume.real Ω := by
  have h := setIntegral_space_smul (fun _ => (1:ℝ)) Ω hr
  simp only [setIntegral_const,smul_eq_mul,mul_one] at h
  have hr3 : r^3 ≠ 0 := pow_ne_zero _ hr.ne'
  exact (inv_mul_eq_iff_eq_mul₀ hr3).mp h.symm

end BoltzmannNonuniqueness.ColdDilationMeasure

end

end

section

/-! # Small dilated jets satisfy the geometric survival conditions automatically -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness

theorem eventually_cold_survival_geometry {s : ℕ → ℝ} {η d₀ T : ℝ}
    (hη : 0 < η) (hslim : Tendsto s atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      T*(d₀*(s n)^10) ≤ enlargementWidth η (s n) ∧ d₀*(s n)^10 ≤ 1/64 := by
  have h8 : Tendsto (fun n => T*d₀*(s n)^8) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (8:ℕ) ≠ 0),mul_zero] using (hslim.pow 8).const_mul (T*d₀)
  have h10 : Tendsto (fun n => d₀*(s n)^10) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (10:ℕ) ≠ 0),mul_zero] using (hslim.pow 10).const_mul d₀
  have hw : ∀ᶠ n in atTop, T*d₀*(s n)^8 < gapCoefficient η/4 :=
    h8.eventually (gt_mem_nhds (div_pos (gapCoefficient_pos hη) (by norm_num)))
  have hd : ∀ᶠ n in atTop, d₀*(s n)^10 < 1/64 :=
    h10.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hw,hd] with n hn hdn
  refine ⟨?_,hdn.le⟩
  have h := mul_le_mul_of_nonneg_right hn.le (sq_nonneg (s n))
  calc
    T*(d₀*(s n)^10) = T*d₀*(s n)^8*(s n)^2 := by ring
    _ ≤ enlargementWidth η (s n) := h

end BoltzmannNonuniqueness

end

end

section

/-! # Product-space integrability and measure change for the spatial dilation -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace BoltzmannNonuniqueness.ColdDilationMeasure

theorem map_space_restrict {r : ℝ} (hr : 0 < r) (Ω : Set JetPrototype.Space) :
    Measure.map (fun x : JetPrototype.Space => r • x) (JetPrototype.spaceVolume.restrict Ω) =
      ENNReal.ofReal ((r^3)⁻¹) • JetPrototype.spaceVolume.restrict (r • Ω) := by
  let e := spaceEquiv r hr.ne'
  have hp : e ⁻¹' (r • Ω) = Ω := by
    ext x
    exact smul_mem_smul_set_iff₀ hr.ne' Ω x
  have h := e.restrict_map JetPrototype.spaceVolume (r • Ω)
  rw [hp] at h
  change (Measure.map (fun x : JetPrototype.Space => r • x) JetPrototype.spaceVolume).restrict (r • Ω) =
    Measure.map (fun x : JetPrototype.Space => r • x) (JetPrototype.spaceVolume.restrict Ω) at h
  rw [Measure.map_addHaar_smul JetPrototype.spaceVolume hr.ne',space_finrank,
    abs_of_pos (inv_pos.mpr (pow_pos hr 3)),Measure.restrict_smul] at h
  exact h.symm

theorem map_phase_restrict {r : ℝ} (hr : 0 < r) (Ω : Set JetPrototype.Space) :
    Measure.map (fun p : JetPrototype.Phase => (r • p.1,p.2))
      ((JetPrototype.spaceVolume.restrict Ω).prod (volume : Measure Velocity)) =
      ENNReal.ofReal ((r^3)⁻¹) •
        ((JetPrototype.spaceVolume.restrict (r • Ω)).prod (volume : Measure Velocity)) := by
  change Measure.map (Prod.map (fun x : JetPrototype.Space => r • x) id) _ = _
  rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    map_space_restrict hr Ω,Measure.map_id,Measure.prod_smul_left]

theorem integrable_dilate {r : ℝ} (hr : 0 < r) (Ω : Set JetPrototype.Space)
    {f : JetPrototype.Phase → ℝ}
    (hf : Integrable f ((JetPrototype.spaceVolume.restrict (r • Ω)).prod volume)) :
    Integrable (fun p : JetPrototype.Phase => f (r • p.1,p.2))
      ((JetPrototype.spaceVolume.restrict Ω).prod volume) := by
  have hc0 : ENNReal.ofReal ((r^3)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hr 3))).ne'
  have hm : Integrable f (Measure.map (phaseEquiv r hr.ne')
      ((JetPrototype.spaceVolume.restrict Ω).prod volume)) := by
    change Integrable f (Measure.map (fun p : JetPrototype.Phase => (r • p.1,p.2)) _)
    rw [map_phase_restrict hr Ω]
    exact (integrable_smul_measure hc0 ENNReal.ofReal_ne_top).mpr hf
  exact (integrable_map_equiv (phaseEquiv r hr.ne') f).mp hm

theorem integrable_dilated_error {r : ℝ} (hr : 0 < r) (Ω : Set JetPrototype.Space)
    {f : JetPrototype.Phase → ℝ}
    (hf : Integrable (fun p => |f p|) ((JetPrototype.spaceVolume.restrict (r • Ω)).prod volume)) :
    Integrable (fun p : JetPrototype.Phase => |r*f (r • p.1,p.2)|)
      ((JetPrototype.spaceVolume.restrict Ω).prod volume) := by
  simpa only [abs_mul,abs_of_pos hr] using (integrable_dilate hr Ω hf).const_mul r

end BoltzmannNonuniqueness.ColdDilationMeasure

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The hot remainder of a countable almost-everywhere mild cold family -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

theorem family_hot_mildAE {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    {F₀ : JetPrototype.Phase → ℝ} {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hSum : ∀ s : Finset I, ∀ u, ∑ i ∈ s, c i u ≤ F u)
    (hc₀n : ∀ i p, 0 ≤ c₀ i p)
    (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : MildAE q b L T F₀ F) (hceq : ∀ i, ColdMildAE q b L T F (c₀ i) (c i)) :
    ∀ t ∈ Icc 0 T, (fun p => F (t,p)-∑' i, c i (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight
        (fun x => F₀ x-∑' i, c₀ i x) (remainderForcing q b L F c) (t,p)) := by
  classical
  let G (i : I) := coldForcing q b L F (c i)
  let S := HotApplication.realBound q*R^2+L*R
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    have hs := hSum {i} u
    simpa only [Finset.sum_singleton] using hs.trans (hF u).2
  have hgm (i) : Measurable (G i) := measurable_coldForcing hFm (hcm i) q b L
  have hgb (i) (u) : 0 ≤ G i u ∧ G i u ≤ S :=
    HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (GaussianLocal.measurable_state (hcm i)) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => hcb i (p.1.1,(p.1.2,p.2))) _
  have hfb (u) : 0 ≤ forcing q b L F u ∧ forcing q b L F u ≤ S :=
    HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) _
  have hgsum (s : Finset I) (u) : (∑ i ∈ s, G i u) ≤ forcing q b L F u :=
    HotRepresentative.finite_sum_coldSource_le hq hb hloss s
      (fun i _ => GaussianLocal.measurable_state (hcm i)) (GaussianLocal.measurable_state hFm)
      (fun i _ p => hcb i (p.1.1,(p.1.2,p.2))) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => hSum s (p.1.1,(p.1.2,p.2))) _
  have hgs (u) : Summable (fun i => G i u) :=
    summable_of_sum_le (fun i => (hgb i u).1) (fun s => hgsum s u)
  have hgBound (u) : (∑' i, G i u) ≤ forcing q b L F u :=
    Real.tsum_le_of_sum_le (fun i => (hgb i u).1) (fun s => hgsum s u)
  have hga (u) : |∑' i, G i u| ≤ S := by
    rw [abs_of_nonneg (tsum_nonneg (fun i => (hgb i u).1))]
    exact (hgBound u).trans (hfb u).2
  intro t ht
  have hcae : ∀ᵐ p ∂FlightMeasure.phaseVolume, ∀ i, c i (t,p) =
      PositiveIntegral.value T L JetBarrier.flight (c₀ i) (G i) (t,p) :=
    ae_all_iff.mpr (fun i => hceq i t ht)
  filter_upwards [hFeq t ht,hcae] with p hfp hcp
  have hs := PositiveIntegral.hasSum_value hT hL GaussianLocal.measurable_flight c₀
    (fun p => summable_of_sum_le (fun i => hc₀n i p) (fun s => hSum₀ s p)) G hgm hgb hgs
    (fun u => (hgBound u).trans (hfb u).2) (t,p)
  have he : (fun i => PositiveIntegral.value T L JetBarrier.flight (c₀ i) (G i) (t,p)) =
      (fun i => c i (t,p)) := funext (fun i => (hcp i).symm)
  rw [he] at hs
  rw [hfp,hs.tsum_eq]
  exact PositiveIntegral.value_sub hT hL (measurable_forcing hFm q b L) (Measurable.tsum hgm)
    (fun u => by rw [abs_of_nonneg (hfb u).1]; exact (hfb u).2) hga F₀ (fun p => ∑' i, c₀ i p) (t,p)

end BoltzmannNonuniqueness.WeightedLocal

end

end

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClippedColdShift
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Vanishing components in the clipped and normalized cold construction -/

noncomputable section

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedColdPicard_zero (q b L T : ℝ) {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, 0 ≤ F u) (n : ℕ) : clippedColdPicard q b L T F 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext u
    simp only [clippedColdPicard,ih,coldForcing_zero]
    simp [PositiveIntegral.value,min_eq_right (hF u)]

theorem clippedColdLimit_zero (q b L T : ℝ) {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, 0 ≤ F u) : clippedColdLimit q b L T F 0 = 0 := by
  funext u
  simp [clippedColdLimit,clippedColdPicard_zero q b L T hF]

theorem normalizedFamily_zero {I : Type*} (F : ℝ × JetPrototype.Phase → ℝ)
    {c : I → ℝ × JetPrototype.Phase → ℝ} {i : I} (hi : c i = 0) :
    normalizedFamily F c i = 0 := by
  funext u
  simp [normalizedFamily,hi]

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FamilyHotBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Pointwise bounds for a dominated family's hot remainder and source -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem family_hot_bounds {I : Type*} [Countable I] {q b L R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hSum : ∀ s : Finset I, ∀ u, ∑ i ∈ s, c i u ≤ F u) :
    Measurable (fun u => F u-∑' i, c i u) ∧
      (∀ u, 0 ≤ F u-∑' i, c i u ∧ F u-∑' i, c i u ≤ R) ∧
      Measurable (remainderForcing q b L F c) ∧
      ∀ u, 0 ≤ remainderForcing q b L F c u ∧
        remainderForcing q b L F c u ≤ HotApplication.realBound q*R^2+L*R := by
  classical
  let G (i : I) := coldForcing q b L F (c i)
  let S := HotApplication.realBound q*R^2+L*R
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hSum {i} u).trans (hF u).2
  have hgm (i) : Measurable (G i) := measurable_coldForcing hFm (hcm i) q b L
  have hgb (i) (u) : 0 ≤ G i u ∧ G i u ≤ S :=
    HotRepresentative.coldSource_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (GaussianLocal.measurable_state (hcm i)) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => hcb i (p.1.1,(p.1.2,p.2))) _
  have hfb (u) : 0 ≤ forcing q b L F u ∧ forcing q b L F u ≤ S :=
    HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hFm)
      (fun p => hF (p.1.1,(p.1.2,p.2))) _
  have hgsum (s : Finset I) (u) : (∑ i ∈ s, G i u) ≤ forcing q b L F u :=
    HotRepresentative.finite_sum_coldSource_le hq hb hloss s
      (fun i _ => GaussianLocal.measurable_state (hcm i)) (GaussianLocal.measurable_state hFm)
      (fun i _ p => hcb i (p.1.1,(p.1.2,p.2))) (fun p => hF (p.1.1,(p.1.2,p.2)))
      (fun p => hSum s (p.1.1,(p.1.2,p.2))) _
  have hgBound (u) : (∑' i, G i u) ≤ forcing q b L F u :=
    Real.tsum_le_of_sum_le (fun i => (hgb i u).1) (fun s => hgsum s u)
  refine ⟨hFm.sub (Measurable.tsum hcm),?_,
    (measurable_forcing hFm q b L).sub (Measurable.tsum hgm),?_⟩
  · intro u
    exact ⟨sub_nonneg.mpr (Real.tsum_le_of_sum_le (fun i => hcn i u) (fun s => hSum s u)),
      (sub_le_self _ (tsum_nonneg (fun i => hcn i u))).trans (hF u).2⟩
  · intro u
    exact ⟨sub_nonneg.mpr (hgBound u),
      (sub_le_self _ (tsum_nonneg (fun i => (hgb i u).1))).trans (hfb u).2⟩

end BoltzmannNonuniqueness.WeightedLocal

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

theorem measurable_seed (s₀ η K α γ d₀ q : ℝ) (N : ℕ) : Measurable (seed s₀ η K α γ d₀ q N) :=
  Measurable.tsum (measurable_color s₀ η K α γ d₀ q N)

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

theorem normalized_measurable (q δ : ℝ) : Measurable (normalized q δ) :=
  (measurable_raw q δ).const_mul _

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetFamilyBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local total-variation error of a surviving cold core -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetLocalFreeError

theorem integral_error_le {K α γ s d t E ε : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (hE : 0 ≤ E) (hε : 0 ≤ ε)
    (η : ℝ) (a : Bool) (y : Space) (μ : Measure Space) [IsFiniteMeasure μ]
    {c : JetPrototype.Phase → ℝ} (hcm : Measurable c)
    (hlower : ∀ᵐ p ∂μ.prod volume,
      Real.exp (-E)*JetFreeTransport.free η K α γ s d t a (shift y p) ≤ c p)
    (hupper : ∀ᵐ p ∂μ.prod volume,
      c p ≤ JetFreeTransport.free η K α γ s d t a (shift y p)+
        ε*barrier η K α γ s d t a (shift y p)) :
    Integrable (fun p => |c p-JetFreeTransport.free η K α γ s d t a (shift y p)|)
      (μ.prod volume) ∧
    (∫ p, |c p-JetFreeTransport.free η K α γ s d t a (shift y p)| ∂μ.prod volume) ≤
      (E+ε)*μ.real univ*(JetBarrierLocalMass.massConstant*(K/s)) := by
  let f : JetPrototype.Phase → ℝ := fun p => JetFreeTransport.free η K α γ s d t a (shift y p)
  let B : JetPrototype.Phase → ℝ := fun p => barrier η K α γ s d t a (shift y p)
  have hBi : Integrable B (μ.prod volume) :=
    JetBarrierLocalMass.local_integrable hK hα hγ hs hd ht htmax η a y μ
  have hfm : Measurable f := (JetFreeTransport.measurable_free η K α γ s d t a).comp
    (measurable_shift y)
  have hb : ∀ᵐ p ∂μ.prod volume, |c p-f p| ≤ (E+ε)*B p := by
    filter_upwards [hlower,hupper] with p hl hu
    have hfn : 0 ≤ f p := JetFreeTransport.free_nonneg hK hs.le hd.le η α γ t a _
    have hBn : 0 ≤ B p := barrier_nonneg hK hs.le hd.le η α γ t a _
    have hfb : f p ≤ B p := JetFreeTransport.free_le_barrier hK hd hα hγ hs ht
      (htmax.trans (by norm_num)) η a _
    have he := abs_sub_le_of_survival hfn (mul_nonneg hε hBn) hE hl hu
    exact he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hfb hE])
  have hci : Integrable (fun p => |c p-f p|) (μ.prod volume) := by
    apply (hBi.const_mul (E+ε)).mono' (hcm.sub hfm).aestronglyMeasurable.norm
    simpa only [Real.norm_eq_abs,Pi.sub_apply,abs_abs] using hb
  refine ⟨hci,?_⟩
  have he := integral_mono_ae hci (hBi.const_mul (E+ε)) hb
  rw [integral_const_mul] at he
  have hm := mul_le_mul_of_nonneg_left
    (JetBarrierLocalMass.local_integral_le hK hα hγ hs hd ht htmax η a y μ)
    (add_nonneg hE hε)
  exact he.trans (by simpa only [B,shift,mul_assoc] using hm)

end BoltzmannNonuniqueness.JetLocalFreeError

end

end

section

/-! # The geometric cold family for an a.e. mild total solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_zero (s₀ η K α γ d₀ q b L T : ℝ) (N : ℕ)
    {F : ℝ × JetPrototype.Phase → ℝ} (hF : ∀ u, 0 ≤ F u)
    (i : JetLattice.Label) (hi : ¬i.annulus < N) :
    rebuilt s₀ η K α γ d₀ q b L T N F i = 0 := by
  have hz : color s₀ η K α γ d₀ q N i = 0 := by
    funext p
    simp only [color,ite_eq_right hi,Pi.zero_apply]
  apply normalizedFamily_zero F
  change clippedColdLimit q b L T F (color s₀ η K α γ d₀ q N i) = 0
  rw [hz,clippedColdLimit_zero q b L T hF]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapDilationScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The attained cap ratio and its uniform perturbation bound -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.Cap

theorem peak_eq_of_max {T δ t : ℝ} {z : ℝ → ℝ} (ht : t ∈ Icc 0 T)
    (hmax : ∀ s ∈ Icc 0 T, z s/(s+δ) ≤ z t/(t+δ)) :
    peak T δ z = z t/(t+δ) := by
  have hmem : z t/(t+δ) ∈ (fun t => z t/(t+δ)) '' Icc 0 T := mem_image_of_mem _ ht
  have hbd : BddAbove ((fun t => z t/(t+δ)) '' Icc 0 T) :=
    ⟨z t/(t+δ),by rintro y ⟨s,hs,rfl⟩; exact hmax s hs⟩
  exact le_antisymm (csSup_le ⟨_,hmem⟩ (by rintro y ⟨s,hs,rfl⟩; exact hmax s hs)) (le_csSup hbd hmem)

theorem peak_attained {T δ : ℝ} {z : ℝ → ℝ} (hT : 0 ≤ T) (hδ : 0 < δ)
    (hz : ContinuousOn z (Icc 0 T)) :
    ∃ t ∈ Icc 0 T, peak T δ z = z t/(t+δ) ∧ ∀ s ∈ Icc 0 T, z s/(s+δ) ≤ peak T δ z := by
  have hc : ContinuousOn (fun t => z t/(t+δ)) (Icc 0 T) :=
    hz.div (by fun_prop) (fun t ht => ne_of_gt (by linarith [ht.1]))
  obtain ⟨t,ht,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) hc
  have he := peak_eq_of_max ht hm
  exact ⟨t,ht,he,fun s hs => (hm hs).trans_eq he.symm⟩

end BoltzmannNonuniqueness.Cap

end

end

section

/-! # Scalar scales at an attained cap time -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Cap

theorem dilation_radius_pos {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) : 0 < t+δ :=
  add_pos_of_nonneg_of_pos ht hδ

theorem cold_fraction_mem {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) :
    δ/(t+δ) ∈ Icc (0:ℝ) 1 :=
  ⟨div_nonneg hδ.le (dilation_radius_pos ht hδ).le,
    (div_le_one (dilation_radius_pos ht hδ)).mpr (by linarith)⟩

theorem terminal_scale_tendsto_zero {T δ : ℕ → ℝ} (hT : ∀ n, 0 < T n)
    (hTlim : Tendsto T atTop (𝓝 0))
    (hratio : Tendsto (fun n => δ n/T n) atTop (𝓝 0)) :
    Tendsto δ atTop (𝓝 0) := by
  have h := hratio.mul hTlim
  simpa only [div_mul_cancel₀ _ (hT _).ne',mul_zero] using h

theorem dilation_radius_tendsto_zero {T δ t : ℕ → ℝ} (hT : ∀ n, 0 < T n)
    (ht : ∀ n, t n ∈ Icc 0 (T n)) (hδ : ∀ n, 0 < δ n)
    (hTlim : Tendsto T atTop (𝓝 0))
    (hratio : Tendsto (fun n => δ n/T n) atTop (𝓝 0)) :
    Tendsto (fun n => t n+δ n) atTop (𝓝 0) := by
  have hδlim := terminal_scale_tendsto_zero hT hTlim hratio
  apply squeeze_zero (fun n => (dilation_radius_pos (ht n).1 (hδ n)).le)
    (fun n => add_le_add (ht n).2 (le_refl (δ n)))
  simpa only [add_zero] using hTlim.add hδlim

end BoltzmannNonuniqueness.Cap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RebuiltHotRegularity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Time regularity of the reconstructed hot remainder -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem rebuilt_hot_continuous {I : Type*} [Countable I] {q b L T R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F : ℝ × JetPrototype.Phase → ℝ} {F₀ : JetPrototype.Phase → ℝ}
    {c₀ : I → JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hF₀m : Measurable F₀) (hc₀m : ∀ i, Measurable (c₀ i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hF₀ : ∀ p, F₀ p ≤ R)
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hSum₀ : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight F₀ (forcing q b L F) (t,p))) :
    ContinuousOn (fun t => PhaseEssSup.size (fun p =>
      F (t,p)-∑' i, rebuiltColdFamily q b L T F c₀ i (t,p))) (Icc 0 T) := by
  obtain ⟨hcm,hcb,hSum,_,hceq⟩ := rebuiltColdFamily_properties hq hb hL hT hR hloss
    hFm hc₀m hF hc₀ hSum₀ hFeq
  have hcn (i) (u) : 0 ≤ rebuiltColdFamily q b L T F c₀ i u := (hcb i u).1
  have hhb := family_hot_bounds hq hb hR hloss hFm hcm hF hcn hSum
  have hhm := family_hot_mildAE hq hb hL hT hR hloss hFm hcm hF hcn hSum
    (fun i p => (hc₀ i p).1) hSum₀ (fun t _ => hFeq t) hceq
  have hinit (p) : 0 ≤ F₀ p-∑' i, c₀ i p ∧ F₀ p-∑' i, c₀ i p ≤ R := by
    have hn : 0 ≤ ∑' i, c₀ i p := tsum_nonneg (fun i => (hc₀ i p).1)
    have hs : (∑' i, c₀ i p) ≤ F₀ p := Real.tsum_le_of_sum_le
      (fun i => (hc₀ i p).1) (fun s => hSum₀ s p)
    exact ⟨sub_nonneg.mpr hs,(sub_le_self _ hn).trans (hF₀ p)⟩
  exact PhaseEssSup.continuousOn_size_of_mildAE
    (f₀ := fun p => F₀ p-∑' i, c₀ i p)
    (g := remainderForcing q b L F (rebuiltColdFamily q b L T F c₀))
    (f := fun u => F u-∑' i, rebuiltColdFamily q b L T F c₀ i u) hT hL hR
    (show 0 ≤ HotApplication.realBound q*R^2+L*R by have := (HotApplication.realBound_pos q).le; positivity)
    (hF₀m.sub (Measurable.tsum hc₀m)) hhb.2.2.1 hinit hhb.2.2.2 hhm

end BoltzmannNonuniqueness.WeightedLocal

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RebuiltHotCapBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The attained cap bounds the rebuilt hot density at every time -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem hot_bound_of_cap {I : Type*} [Countable I] {q b L T R δ : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    {F₀ : JetPrototype.Phase → ℝ} (hF₀m : Measurable F₀) (hF₀ : ∀ p, F₀ p ≤ R)
    {c₀ : I → JetPrototype.Phase → ℝ} (hc₀m : ∀ i, Measurable (c₀ i))
    (hc₀ : ∀ i p, 0 ≤ c₀ i p ∧ c₀ i p ≤ R)
    (hdom : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c₀ i p ≤ F₀ p)
    (F : PeriodicMildState q b L T R F₀) (hcap : hotPeak δ c₀ F ≤ 1) :
    ∀ t ∈ Icc 0 T, ∀ᵐ p ∂FlightMeasure.phaseVolume,
      F.value (t,p)-(∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)) ≤ t+δ := by
  have hprop := rebuiltColdFamily_properties hq hb hL hT hR hloss F.measurable_value hc₀m
    F.value_bounds hc₀ hdom (F.all_mild hT)
  have hcn (i) (u) : 0 ≤ rebuiltColdFamily q b L T F.value c₀ i u := (hprop.2.1 i u).1
  have hhot := family_hot_bounds hq hb hR hloss F.measurable_value hprop.1
    F.value_bounds hcn hprop.2.2.1
  have hreg := rebuilt_hot_continuous hq hb hL hT hR hloss F.measurable_value hF₀m hc₀m
    F.value_bounds hF₀ hc₀ hdom (F.all_mild hT)
  obtain ⟨_,_,_,hpeak⟩ := Cap.peak_attained hT hδ hreg
  intro t ht
  have hsize : PhaseEssSup.size (fun p => F.value (t,p)-
      ∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)) ≤ t+δ :=
    (div_le_one (by linarith [ht.1] : 0 < t+δ)).mp ((hpeak t ht).trans hcap)
  have hae := PhaseEssSup.ae_abs_le_size
    (hhot.1.comp (measurable_const.prodMk measurable_id))
    (fun p => show |F.value (t,p)-∑' i, rebuiltColdFamily q b L T F.value c₀ i (t,p)| ≤ R from by
      rw [abs_of_nonneg (hhot.2.1 (t,p)).1]
      exact (hhot.2.1 (t,p)).2)
  filter_upwards [hae] with p hp
  exact (le_abs_self _).trans (hp.trans hsize)

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

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

theorem escapedFrequencyConstant_nonneg {s₀ K d₀ : ℝ}
    (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 < d₀) (η α q : ℝ) (m : ℕ) :
    0 ≤ escapedFrequencyConstant s₀ η α K d₀ q m :=
  mul_nonneg (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _)
    (weightFrequencyConstant_nonneg q (by norm_num))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Cold survival for the actual capped periodic mild solutions -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_survival {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (m N : ℕ) (i : Label) (hi0 : i.lattice = 0)
    (hwidth : T*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
    (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
    {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (F : PeriodicMildState q b L T R (initial s₀ η K α γ d₀ q N h₀))
    (hcap : F.hotPeak δ (color s₀ η K α γ d₀ q N) ≤ 1)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      Real.exp (-coldOpticalDepth
        (4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9)
        (weightFrequencyConstant q 2) δ (escapedFrequencyConstant s₀ η α K d₀ q m) m t)*
        color s₀ η K α γ d₀ q N i p ≤
          rebuilt s₀ η K α γ d₀ q b L T N F.value i (t,JetBarrier.flight t p) := by
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (j) (p) : 0 ≤ color s₀ η K α γ d₀ q N j p ∧ color s₀ η K α γ d₀ q N j p ≤ R :=
    ⟨(hi.1 j p).1,(hi.1 j p).2.trans (hF₀ p)⟩
  have hp := rebuiltColdFamily_properties hq hb hL hT hR hloss F.measurable_value
    (measurable_color s₀ η K α γ d₀ q N) F.value_bounds hc₀ hi.2 (F.all_mild hT)
  have hc (j) (z) : 0 ≤ rebuilt s₀ η K α γ d₀ q b L T N F.value j z ∧
      rebuilt s₀ η K α γ d₀ q b L T N F.value j z ≤ R := by
    refine ⟨(hp.2.1 j z).1,?_⟩
    have hd := hp.2.2.1 {j} z
    simpa only [Finset.sum_singleton,rebuilt] using hd.trans (F.value_bounds z).2
  apply survival_of_capped_family_q80 hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hTmax hq hb hR hδ.le hsmall hloss m N i hi0 hwidth hdmax
    F.measurable_value hp.1 F.value_bounds hc (hp.2.2.2.2 i)
    (fun z => (hp.2.2.2.1 z).1)
    (rebuilt_zero s₀ η K α γ d₀ q b L T N (fun z => (F.value_bounds z).1))
    (fun r hr j p => rebuilt_envelope_q80 hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall
      hq hb hL hT hR (hTmax.trans (by norm_num)) hloss N hh₀ F.measurable_value
      F.value_bounds hF₀ j hr p)
    (PeriodicMildState.hot_bound_of_cap hq hb hL hT hR hδ hloss
      ((measurable_seed s₀ η K α γ d₀ q N).add hh₀m) hF₀
      (measurable_color s₀ η K α γ d₀ q N) hc₀ hi.2 F hcap) ht

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual cold colors lie between their surviving free flight and the Gaussian excess -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem physical_freeColor {s₀ η K α γ d₀ q : ℝ} {N : ℕ} {i : Label}
    (hi : i.annulus < N) (t : ℝ) (p : JetPrototype.Phase) :
    H q p.2*freeColor s₀ η K α γ d₀ q N i t p =
      JetFreeTransport.free η K α γ (jetScale s₀ η i.annulus)
        (d₀*jetScale s₀ η i.annulus^10) t i.positive (shift (displacement i.lattice) p) := by
  have he : shift (displacement i.lattice) (JetBarrier.flight (-t) p) =
      JetBarrier.flight (-t) (shift (displacement i.lattice) p) :=
    shift_flight _ _ _
  simp only [freeColor,color,ite_eq_left hi,JetDatum.term,JetBarrier.flight,shift] at *
  rw [mul_div_cancel₀ _ (H_pos q p.2).ne']
  exact congrArg (JetPrototype.density η K α γ (jetScale s₀ η i.annulus)
    (d₀*jetScale s₀ η i.annulus^10) i.positive) he

theorem rebuilt_le_free_add_barrier {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hTmax : T ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (i : Label) {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    H q p.2*rebuilt s₀ η K α γ d₀ q b L T N F i (t,p) ≤
      H q p.2*freeColor s₀ η K α γ d₀ q N i t p+
        JetSupersolution.epsilon K (jetScale s₀ η i.annulus) (d₀*jetScale s₀ η i.annulus^10)*
          JetBarrier.barrier η K α γ (jetScale s₀ η i.annulus)
            (d₀*jetScale s₀ η i.annulus^10) t i.positive (shift (displacement i.lattice) p) := by
  by_cases hi : i.annulus < N
  · have h := rebuilt_envelope_q80 hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall
      hq hb hL hT hR hTmax hloss N hh₀ hFm hF hF₀ i ht p
    rw [physical_freeColor hi]
    exact h
  · rw [rebuilt_zero s₀ η K α γ d₀ q b L T N (fun z => (hF z).1) i hi]
    simp only [Pi.zero_apply,mul_zero,freeColor,color,ite_eq_right hi,zero_add]
    have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
    have hd : 0 < d₀*jetScale s₀ η i.annulus^10 := by positivity
    exact mul_nonneg (JetSupersolution.epsilon_nonneg hK hs hd)
      (JetBarrier.barrier_nonneg hK hs.le hd.le η α γ t i.positive _)

theorem eulerian_survival {s₀ η K α γ d₀ q b L T t E : ℝ} {N : ℕ} {i : Label}
    {F : ℝ × JetPrototype.Phase → ℝ}
    (h : ∀ᵐ p ∂FlightMeasure.phaseVolume, Real.exp (-E)*color s₀ η K α γ d₀ q N i p ≤
      rebuilt s₀ η K α γ d₀ q b L T N F i (t,JetBarrier.flight t p)) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      Real.exp (-E)*(H q p.2*freeColor s₀ η K α γ d₀ q N i t p) ≤
        H q p.2*rebuilt s₀ η K α γ d₀ q b L T N F i (t,p) := by
  have he := (FlightMeasure.flight_measurePreserving (-t)).quasiMeasurePreserving.ae h
  filter_upwards [he] with p hp
  simp only [JetFreeTransport.flight_neg] at hp
  have hm := mul_le_mul_of_nonneg_left hp (H_nonneg q p.2)
  simpa only [freeColor,mul_left_comm] using hm

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Local free-transport error for the actual capped periodic solutions -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_local_free_error {s₀ η K α γ d₀ q b L T R δ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hδ : 0 < δ)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (m N : ℕ) (i : Label) (hi0 : i.lattice = 0)
    (hwidth : T*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
    (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
    {h₀ : JetPrototype.Phase → ℝ} (hh₀m : Measurable h₀) (hh₀ : ∀ p, 0 ≤ h₀ p)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (F : PeriodicMildState q b L T R (initial s₀ η K α γ d₀ q N h₀))
    (hcap : F.hotPeak δ (color s₀ η K α γ d₀ q N) ≤ 1)
    (hi : i.annulus < N) (Ω : Set JetPrototype.Space)
    [IsFiniteMeasure (JetPrototype.spaceVolume.restrict Ω)]
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    let s := jetScale s₀ η i.annulus
    let E := coldOpticalDepth (4*JetBarrierCollision.frequencyConstant*K*d₀*s^9)
      (weightFrequencyConstant q 2) δ (escapedFrequencyConstant s₀ η α K d₀ q m) m t
    let ε := JetSupersolution.epsilon K s (d₀*s^10)
    let μ := (JetPrototype.spaceVolume.restrict Ω).prod (volume : Measure Velocity)
    let error := fun p : JetPrototype.Phase =>
      |H q p.2*rebuilt s₀ η K α γ d₀ q b L T N F.value i (t,p)-
        JetFreeTransport.free η K α γ s (d₀*s^10) t i.positive (shift (displacement i.lattice) p)|
    Integrable error μ ∧ (∫ p, error p ∂μ) ≤
      (E+ε)*(JetPrototype.spaceVolume.restrict Ω).real univ*(JetBarrierLocalMass.massConstant*(K/s)) := by
  dsimp only
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.annulus+1)
  have hd : 0 < d₀*jetScale s₀ η i.annulus^10 := by positivity
  have hT₁ : T ≤ 1 := hTmax.trans (by norm_num)
  have hinit := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hc₀ (j) (p) : 0 ≤ color s₀ η K α γ d₀ q N j p ∧ color s₀ η K α γ d₀ q N j p ≤ R :=
    ⟨(hinit.1 j p).1,(hinit.1 j p).2.trans (hF₀ p)⟩
  have hp := rebuiltColdFamily_properties hq hb hL hT hR hloss F.measurable_value
    (measurable_color s₀ η K α γ d₀ q N) F.value_bounds hc₀ hinit.2 (F.all_mild hT)
  have hcm : Measurable (fun p : JetPrototype.Phase =>
      H q p.2*rebuilt s₀ η K α γ d₀ q b L T N F.value i (t,p)) :=
    ((ChartKernel.measurable_H q).comp measurable_snd).mul
      ((hp.1 i).comp (measurable_const.prodMk measurable_id))
  have hl := eulerian_survival (rebuilt_survival hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hTmax hq hb hL hT hR hδ hsmall hloss m N i hi0 hwidth hdmax
    hh₀m hh₀ hF₀ F hcap ⟨ht.1.le,ht.2⟩)
  have hac : (JetPrototype.spaceVolume.restrict Ω).prod (volume : Measure Velocity) ≪
      FlightMeasure.phaseVolume :=
    Measure.absolutelyContinuous_restrict.prod Measure.AbsolutelyContinuous.rfl
  have hl' := hl.filter_mono hac.ae_le
  simp_rw [physical_freeColor hi] at hl'
  have hE : 0 ≤ coldOpticalDepth
      (4*JetBarrierCollision.frequencyConstant*K*d₀*jetScale s₀ η i.annulus^9)
      (weightFrequencyConstant q 2) δ (escapedFrequencyConstant s₀ η α K d₀ q m) m t := by
    apply coldOpticalDepth_nonneg _ (weightFrequencyConstant_nonneg q (by norm_num)) hδ.le
      (escapedFrequencyConstant_nonneg hs₀ hK hd₀ η α q m) ht.1.le
    have := JetBarrierCollision.frequencyConstant_nonneg
    positivity
  apply JetLocalFreeError.integral_error_le hK hα hγ hs hd ht.1 (ht.2.trans hT₁) hE
    (JetSupersolution.epsilon_nonneg hK hs hd) η i.positive (displacement i.lattice)
    (JetPrototype.spaceVolume.restrict Ω) hcm hl'
  exact ae_of_all _ (fun p => by
    have hu := rebuilt_le_free_add_barrier hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall
      hq hb hL hT hR hT₁ hloss N hh₀ F.measurable_value F.value_bounds hF₀ i ht p
    simpa only [physical_freeColor hi,jetScale] using hu)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapDilationCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual cap shots on horizons tending to zero -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem shrinkingHorizon_pos {τ : ℝ} (hτ : 0 < τ) (n : ℕ) : 0 < shrinkingHorizon τ n :=
  div_pos hτ (by positivity)

theorem shrinkingHorizon_le {τ : ℝ} (hτ : 0 < τ) (n : ℕ) : shrinkingHorizon τ n ≤ τ := by
  apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)+1)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem shrinkingHorizon_tendsto_zero (τ : ℝ) :
    Tendsto (shrinkingHorizon τ) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => τ/((n:ℝ)+1)) atTop (𝓝 0)
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul τ
  simpa only [div_eq_mul_inv,one_mul,mul_zero] using h

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Attained times and dilation radii for the actual shrinking cap shots -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

namespace AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem radius_pos (S : AttainedCapSequence F) (hs₀ : 0 < s₀) (n : ℕ) : 0 < S.radius n :=
  Cap.dilation_radius_pos (S.time_mem n).1 (DatumBounds.scale_pos hs₀ _)

theorem radius_tendsto_zero (S : AttainedCapSequence F) (hs₀ : 0 < s₀) :
    Tendsto S.radius atTop (𝓝 0) :=
  Cap.dilation_radius_tendsto_zero (shrinkingHorizon_pos F.horizonScale_pos) S.time_mem
    (fun n => DatumBounds.scale_pos hs₀ (F.indices n+1))
    (shrinkingHorizon_tendsto_zero F.horizonScale) F.cold_ratio_tendsto

theorem coldFraction_mem (S : AttainedCapSequence F) (hs₀ : 0 < s₀) (n : ℕ) :
    S.coldFraction n ∈ Icc (0:ℝ) 1 :=
  Cap.cold_fraction_mem (S.time_mem n).1 (DatumBounds.scale_pos hs₀ _)

end AttainedCapSequence
end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Every compact subinterval of the limiting horizon is eventually available -/

noncomputable section

open Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_scaled_slab (S : AttainedCapSequence F) (hs₀ : 0 < s₀)
    {κ : ℕ → ℕ} {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {A : ℝ} (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) A,
      S.radius (κ n)*t ∈ Icc 0 (shrinkingHorizon F.horizonScale (κ n)) := by
  filter_upwards [hU.eventually (lt_mem_nhds hA)] with n hn
  have hR := S.radius_pos hs₀ (κ n)
  have hT := shrinkingHorizon_pos F.horizonScale_pos (κ n)
  have hquot : A < shrinkingHorizon F.horizonScale (κ n)/S.radius (κ n) :=
    (ENNReal.ofReal_lt_ofReal_iff (div_pos hT hR)).mp hn
  have htime : S.radius (κ n)*A < shrinkingHorizon F.horizonScale (κ n) := by
    have h := (lt_div_iff₀ hR).mp hquot
    simpa only [mul_comm] using h
  intro t ht
  exact ⟨mul_nonneg hR.le ht.1,
    (mul_le_mul_of_nonneg_left ht.2 hR.le).trans htime.le⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

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

/-! # Actual cold labels approaching each point of the limiting geometric mesh -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_scale_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) :
    Tendsto (fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus/S.radius (E.indices n))
      atTop (𝓝 (E.phase*Real.exp (η*(k:ℝ)))) :=
  GeometricMesh.jet_scale_approximation hs₀ hη (fun n => S.radius_pos hs₀ (E.indices n))
    ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop) E.phase_limit k

theorem HotLimitExtraction.coldLabel_retained (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool)
    (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))) :
    ∀ᶠ n in atTop, (E.coldLabel k a n).annulus < F.indices (E.indices n) :=
  GeometricMesh.jetIndex_eventually_retained hs₀ hη (fun n => S.radius_pos hs₀ (E.indices n))
    ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop)
    E.phase_limit E.fraction_limit k hk

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The quantitative free-flight error of the constructed cap approximations -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocal
open BoltzmannNonuniqueness.WeightedLocalControl BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.local_free_error {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (hq : q < 2) (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (m : ℕ) (i : Label) (hi0 : i.lattice = 0) (hi : i.annulus < N)
    (hwidth : T*(d₀*jetScale s₀ η i.annulus^10) ≤ enlargementWidth η (jetScale s₀ η i.annulus))
    (hdmax : d₀*jetScale s₀ η i.annulus^10 ≤ 1/64)
    (Ω : Set JetPrototype.Space) [IsFiniteMeasure (JetPrototype.spaceVolume.restrict Ω)]
    {t : ℝ} (ht : t ∈ Ioc 0 T) :
    let s := jetScale s₀ η i.annulus
    let E := coldOpticalDepth (4*JetBarrierCollision.frequencyConstant*K*d₀*s^9)
      (weightFrequencyConstant q 2) (DatumBounds.scale s₀ η (N+1))
      (escapedFrequencyConstant s₀ η α K d₀ q m) m t
    let ε := JetSupersolution.epsilon K s (d₀*s^10)
    let μ := (JetPrototype.spaceVolume.restrict Ω).prod (volume : Measure Velocity)
    let error := fun p : JetPrototype.Phase => |H q p.2*F.cold i (t,p)-
      JetFreeTransport.free η K α γ s (d₀*s^10) t i.positive (shift (displacement i.lattice) p)|
    Integrable error μ ∧ (∫ p, error p ∂μ) ≤
      (E+ε)*(JetPrototype.spaceVolume.restrict Ω).real univ*(JetBarrierLocalMass.massConstant*(K/s)) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  exact rebuilt_local_free_error hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hTmax
    hq (by positivity) (bounds (by positivity) F.amplitude_pos).1 hT (by linarith [F.amplitude_pos])
    hδ hsmall le_rfl m N i hi0 hwidth hdmax
    ((HotSeedProfile.normalized_measurable q _).const_mul F.coefficient) hh₀ F.initial_bound
    F.solution F.cap.le hi Ω ht

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Cold dilation estimates for cap shots with varying horizons -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Pointwise
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cap_variable_cold_dilation_free_error {s₀ η K α γ d₀ q a S U : ℝ} {T : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hT : ∀ n, 0 ≤ T n) (hTmax : ∀ n, T n ≤ 1/32)
    (hq : q < 2) (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ → ℕ) (F : ∀ n, CapApproximation s₀ η K α γ d₀ q (T n) (N n))
    (j : ℕ → Label) (hj0 : ∀ n, (j n).lattice = 0) (hj : ∀ n, (j n).annulus < N n)
    (r t : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ∈ Ioc 0 (T n)) (ha : 0 < a) (hS : 0 ≤ S)
    (hlo : ∀ n, a*r n ≤ jetScale s₀ η (j n).annulus)
    (hhi : ∀ n, jetScale s₀ η (j n).annulus ≤ S*r n)
    (htime : ∀ n, t n ≤ U*r n)
    (hδ : ∀ n, DatumBounds.scale s₀ η (N n+1) ≤ r n)
    (hwidth : ∀ n, T n*(d₀*jetScale s₀ η (j n).annulus^10) ≤
      enlargementWidth η (jetScale s₀ η (j n).annulus))
    (hdmax : ∀ n, d₀*jetScale s₀ η (j n).annulus^10 ≤ 1/64)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Tendsto (fun n => ∫ x in Ω, ∫ v : Velocity,
      |r n*(H q v*(F n).cold (j n) (t n,(r n • x,v))-
        JetFreeTransport.free η K α γ (jetScale s₀ η (j n).annulus)
          (d₀*jetScale s₀ η (j n).annulus^10) (t n) (j n).positive
          (shift (displacement (j n).lattice) (r n • x,v)))|
      ∂volume ∂JetPrototype.spaceVolume) atTop (𝓝 0) := by
  let s := fun n => jetScale s₀ η (j n).annulus
  let δ := fun n => DatumBounds.scale s₀ η (N n+1)
  let C := 4*JetBarrierCollision.frequencyConstant*K*d₀
  let A := weightFrequencyConstant q 2
  let D := escapedFrequencyConstant s₀ η α K d₀ q 0
  let E := fun n => coldOpticalDepth (C*s n^9) A (δ n) D 0 (t n)
  let ε := fun n => JetSupersolution.epsilon K (s n) (d₀*(s n)^10)
  let err := fun n (p : JetPrototype.Phase) =>
    H q p.2*(F n).cold (j n) (t n,p)-
      JetFreeTransport.free η K α γ (s n) (d₀*(s n)^10) (t n) (j n).positive
        (shift (displacement (j n).lattice) p)
  let I := fun n => ∫ p : JetPrototype.Phase, |err n p|
    ∂(JetPrototype.spaceVolume.restrict (r n • Ω)).prod volume
  have hs (n) : 0 < s n := DatumBounds.scale_pos (η := η) hs₀ _
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) JetBarrierCollision.frequencyConstant_nonneg) hK) hd₀.le
  have hA : 0 ≤ A := weightFrequencyConstant_nonneg q (by norm_num)
  have hD : 0 ≤ D := escapedFrequencyConstant_nonneg hs₀ hK hd₀ η α q 0
  have hEn (n) : 0 ≤ E n := coldOpticalDepth_nonneg
    (mul_nonneg hC (pow_nonneg (hs n).le _)) hA (DatumBounds.scale_pos hs₀ _).le hD (ht n).1.le 0
  have hεn (n) : 0 ≤ ε n := JetSupersolution.epsilon_nonneg hK (hs n)
    (mul_pos hd₀ (pow_pos (hs n) _))
  have hcomp (n) : IsCompact (r n • Ω) := hΩ.image (continuous_const_smul (r n))
  have hfin (n) : IsFiniteMeasure (JetPrototype.spaceVolume.restrict (r n • Ω)) :=
    isFiniteMeasure_restrict.mpr (hcomp n).measure_lt_top.ne
  have hbound (n) : Integrable (fun p => |err n p|)
      ((JetPrototype.spaceVolume.restrict (r n • Ω)).prod volume) ∧
      I n ≤ (E n+ε n)*((r n)^3*JetPrototype.spaceVolume.real Ω)*
        (JetBarrierLocalMass.massConstant*(K/s n)) := by
    let _ := hfin n
    have hb := (F n).local_free_error hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      (hT n) (hTmax n) hq hsmall 0 (j n) (hj0 n) (hj n) (hwidth n) (hdmax n) (r n • Ω) (ht n)
    dsimp only at hb
    refine ⟨hb.1,?_⟩
    simpa only [I,err,E,ε,C,A,D,s,δ,measureReal_restrict_apply_univ,
      ColdDilationMeasure.spaceVolume_real_smul Ω (hr n)] using hb.2
  have hElim : Tendsto E atTop (𝓝 0) :=
    coldOpticalDepth_tendsto_zero hC hA hD hS (fun n => (hr n).le)
      (fun n => (hs n).le) (fun n => (ht n).1.le) (fun n => (DatumBounds.scale_pos hs₀ _).le)
      hhi htime hδ hrlim
  have hεlim : Tendsto ε atTop (𝓝 0) := jet_epsilon_tendsto_zero hs hhi hrlim K d₀
  have hlim : Tendsto (fun n => I n/(r n)^2) atTop (𝓝 0) :=
    scaled_local_error_tendsto_zero hEn hεn measureReal_nonneg JetBarrierLocalMass.massConstant_nonneg
      hK hr hs ha hlo (fun n => integral_nonneg (fun _ => abs_nonneg _))
      (fun n => (hbound n).2) hElim hεlim
  convert hlim using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [ColdDilationMeasure.dilated_error_integral (err n) Ω (hr n)]
  rw [← integral_prod _ (hbound n).1]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

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

section

/-! # Cold free-flight convergence on varying cap horizons -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Pointwise
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cap_variable_cold_dilation_limit {s₀ η K α γ d₀ q a S U : ℝ} {T : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hT : ∀ n, 0 ≤ T n) (hTmax : ∀ n, T n ≤ 1/32)
    (hq : q < 2) (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ → ℕ) (F : ∀ n, CapApproximation s₀ η K α γ d₀ q (T n) (N n))
    (j : ℕ → Label) (hj0 : ∀ n, (j n).lattice = 0) (hj : ∀ n, (j n).annulus < N n)
    (r t : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ∈ Ioc 0 (T n)) (ha : 0 < a) (hS : 0 ≤ S)
    (hlo : ∀ n, a*r n ≤ jetScale s₀ η (j n).annulus)
    (hhi : ∀ n, jetScale s₀ η (j n).annulus ≤ S*r n)
    (htime : ∀ n, t n ≤ U*r n)
    (hδ : ∀ n, DatumBounds.scale s₀ η (N n+1) ≤ r n)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Tendsto (fun n => ∫ x in Ω, ∫ v : Velocity,
      |r n*(H q v*(F n).cold (j n) (t n,(r n • x,v))-
        JetFreeTransport.free η K α γ (jetScale s₀ η (j n).annulus)
          (d₀*jetScale s₀ η (j n).annulus^10) (t n) (j n).positive
          (shift (displacement (j n).lattice) (r n • x,v)))|
      ∂volume ∂JetPrototype.spaceVolume) atTop (𝓝 0) := by
  have hslim : Tendsto (fun n => jetScale s₀ η (j n).annulus) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (DatumBounds.scale_pos (η := η) hs₀ _).le) hhi
    simpa only [mul_zero] using hrlim.const_mul S
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp (eventually_cold_survival_geometry (T := (1/32:ℝ)) (d₀ := d₀) hη hslim)
  apply (tendsto_add_atTop_iff_nat n₀).mp
  exact cap_variable_cold_dilation_free_error hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max (fun n => hT (n+n₀)) (fun n => hTmax (n+n₀)) hq hsmall
    (fun n => N (n+n₀)) (fun n => F (n+n₀)) (fun n => j (n+n₀))
    (fun n => hj0 (n+n₀)) (fun n => hj (n+n₀)) (fun n => r (n+n₀)) (fun n => t (n+n₀))
    (fun n => hr (n+n₀)) (hrlim.comp (tendsto_add_atTop_nat n₀))
    (fun n => ht (n+n₀)) ha hS (fun n => hlo (n+n₀)) (fun n => hhi (n+n₀))
    (fun n => htime (n+n₀)) (fun n => hδ (n+n₀))
    (fun n => (mul_le_mul_of_nonneg_right (hTmax (n+n₀)) (by positivity)).trans
      (hn₀ (n+n₀) (by omega)).1) (fun n => (hn₀ (n+n₀) (by omega)).2) Ω hΩ

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Product-space cold dilation with varying cap horizons -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology Pointwise
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem cap_variable_cold_L1_dilation_limit {s₀ η K α γ d₀ q a S U : ℝ} {T : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hT : ∀ n, 0 ≤ T n) (hTmax : ∀ n, T n ≤ 1/32)
    (hq : q < 2) (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ → ℕ) (F : ∀ n, CapApproximation s₀ η K α γ d₀ q (T n) (N n))
    (j : ℕ → Label) (hj0 : ∀ n, (j n).lattice = 0) (hj : ∀ n, (j n).annulus < N n)
    (r t : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (ht : ∀ n, t n ∈ Ioc 0 (T n)) (ha : 0 < a) (hS : 0 ≤ S)
    (hlo : ∀ n, a*r n ≤ jetScale s₀ η (j n).annulus)
    (hhi : ∀ n, jetScale s₀ η (j n).annulus ≤ S*r n)
    (htime : ∀ n, t n ≤ U*r n)
    (hδ : ∀ n, DatumBounds.scale s₀ η (N n+1) ≤ r n)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Tendsto (fun n => ∫ p : JetPrototype.Phase,
      |r n*(H q p.2*(F n).cold (j n) (t n,(r n • p.1,p.2))-
        JetFreeTransport.free η K α γ (jetScale s₀ η (j n).annulus)
          (d₀*jetScale s₀ η (j n).annulus^10) (t n) (j n).positive
          (shift (displacement (j n).lattice) (r n • p.1,p.2)))|
      ∂(JetPrototype.spaceVolume.restrict Ω).prod volume) atTop (𝓝 0) := by
  have hbase := cap_variable_cold_dilation_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hT hTmax hq hsmall N F j hj0 hj r t hr hrlim ht ha hS hlo hhi htime hδ Ω hΩ
  apply hbase.congr'
  have hslim : Tendsto (fun n => jetScale s₀ η (j n).annulus) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (DatumBounds.scale_pos (η := η) hs₀ _).le) hhi
    simpa only [mul_zero] using hrlim.const_mul S
  filter_upwards [eventually_cold_survival_geometry (T := (1/32:ℝ)) (d₀ := d₀) hη hslim] with n hn
  have hcomp : IsCompact (r n • Ω) := hΩ.image (continuous_const_smul (r n))
  let _ : IsFiniteMeasure (JetPrototype.spaceVolume.restrict (r n • Ω)) :=
    isFiniteMeasure_restrict.mpr hcomp.measure_lt_top.ne
  have hb := (F n).local_free_error hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    (hT n) (hTmax n) hq hsmall 0 (j n) (hj0 n) (hj n)
    ((mul_le_mul_of_nonneg_right (hTmax n) (by positivity)).trans hn.1) hn.2 (r n • Ω) (ht n)
  dsimp only at hb
  exact (integral_prod _ (ColdDilationMeasure.integrable_dilated_error (hr n) Ω hb.1)).symm

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Cold/free convergence for the actual retained mesh labels -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_free_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (k : ℤ) (a : Bool)
    (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    let j := E.coldLabel k a
    let r := fun n => S.radius (E.indices n)
    Tendsto (fun n => ∫ p : JetPrototype.Phase,
      |r n*(H q p.2*(F.approximation (E.indices n)).cold (j n) (r n*t,(r n • p.1,p.2))-
        JetFreeTransport.free η K α γ (JetGeometry.jetScale s₀ η (j n).annulus)
          (d₀*(JetGeometry.jetScale s₀ η (j n).annulus)^10) (r n*t) (j n).positive
          (shift (displacement (j n).lattice) (r n • p.1,p.2)))|
      ∂(JetPrototype.spaceVolume.restrict Ω).prod volume) atTop (𝓝 0) := by
  intro j r
  let μ := E.phase*Real.exp (η*(k:ℝ))
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hrlim : Tendsto r atTop (𝓝 0) :=
    (S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop
  have hr (n) : 0 < r n := S.radius_pos hs₀ (E.indices n)
  have hs : Tendsto (fun n => JetGeometry.jetScale s₀ η (j n).annulus/r n) atTop (𝓝 μ) :=
    E.coldLabel_scale_limit hs₀ hη k a
  have hlo := hs.eventually (lt_mem_nhds (show μ/2 < μ by linarith))
  have hhi := hs.eventually (gt_mem_nhds (show μ < 2*μ by linarith))
  have hgood : ∀ᶠ n in atTop,
      (j n).annulus < F.indices (E.indices n) ∧
      r n*t ∈ Ioc 0 (shrinkingHorizon F.horizonScale (E.indices n)) ∧
      (μ/2)*r n ≤ JetGeometry.jetScale s₀ η (j n).annulus ∧
      JetGeometry.jetScale s₀ η (j n).annulus ≤ (2*μ)*r n := by
    filter_upwards [E.coldLabel_retained hs₀ hη k a hk,
      S.eventually_scaled_slab hs₀ E.horizon_limit htU,hlo,hhi] with n hj htime hl hu
    exact ⟨hj,⟨mul_pos (hr n) ht,(htime t ⟨ht.le,le_rfl⟩).2⟩,
      ((lt_div_iff₀ (hr n)).mp hl).le,((div_lt_iff₀ (hr n)).mp hu).le⟩
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hgood
  apply (tendsto_add_atTop_iff_nat n₀).mp
  exact cap_variable_cold_L1_dilation_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    (fun n => (shrinkingHorizon_pos F.horizonScale_pos (E.indices (n+n₀))).le)
    (fun n => (shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le)
    hq hsmall (fun n => F.indices (E.indices (n+n₀)))
    (fun n => F.approximation (E.indices (n+n₀))) (fun n => j (n+n₀)) (fun _ => rfl)
    (fun n => (hn₀ (n+n₀) (by omega)).1) (fun n => r (n+n₀)) (fun n => r (n+n₀)*t)
    (fun n => hr (n+n₀)) (hrlim.comp (tendsto_add_atTop_nat n₀))
    (fun n => (hn₀ (n+n₀) (by omega)).2.1) (by positivity : 0 < μ/2)
    (by positivity : 0 ≤ 2*μ) (fun n => (hn₀ (n+n₀) (by omega)).2.2.1)
    (fun n => (hn₀ (n+n₀) (by omega)).2.2.2)
    (U := t) (fun n => (mul_comm (r (n+n₀)) t).le)
    (fun n => (div_le_one (hr (n+n₀))).mp (S.coldFraction_mem hs₀ (E.indices (n+n₀))).2)
    Ω hΩ

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapFiniteBackgroundLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local integrability of the actual cold colors and their free profiles -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.cold_physical_integrable {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T)
    (i : JetLattice.Label) (t : ℝ) (μ : Measure JetPrototype.Space) [IsFiniteMeasure μ] :
    Integrable (fun p : JetPrototype.Phase => H q p.2*F.cold i (t,p)) (μ.prod volume) := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  have hm : Measurable (fun p : JetPrototype.Phase => H q p.2*F.cold i (t,p)) :=
    ((ChartKernel.measurable_H q).comp measurable_snd).mul
      ((hc.1 i).comp (measurable_const.prodMk measurable_id))
  apply (((integrable_H hq).comp_snd μ).const_mul (2*F.amplitude)).mono' hm.aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (mul_nonneg (H_nonneg q p.2) (hc.2.1 i (t,p)))]
  have hb : F.cold i (t,p) ≤ 2*F.amplitude := by
    simpa only [Finset.sum_singleton] using (hc.2.2.1 {i} (t,p)).trans (F.solution.value_bounds (t,p)).2
  exact (mul_le_mul_of_nonneg_left hb (H_nonneg q p.2)).trans_eq (mul_comm _ _)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Bounded testing of the actual cold/free error -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal Pointwise
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelError_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hq : q < 2)
    (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 < t)
    (htmax : S.radius (E.indices n)*t ≤ 1)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Integrable (E.coldLabelError k a n t) ((JetPrototype.spaceVolume.restrict Ω).prod volume) := by
  let r := S.radius (E.indices n)
  let i := E.coldLabel k a n
  let s := JetGeometry.jetScale s₀ η i.annulus
  let d := d₀*s^10
  let μ := JetPrototype.spaceVolume.restrict (r • Ω)
  have hr : 0 < r := S.radius_pos hs₀ (E.indices n)
  have hs : 0 < s := DatumBounds.scale_pos hs₀ _
  have hd : 0 < d := mul_pos hd₀ (pow_pos hs 10)
  let _ : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (hΩ.image (continuous_const_smul r)).measure_lt_top.ne
  have hc := (F.approximation (E.indices n)).cold_physical_integrable hs₀ hsmax hη hηmax hK hd₀.le hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le i (r*t) μ
  have hb := JetBarrierLocalMass.local_integrable hK hα hγ hs hd (mul_pos hr ht) htmax η a
    (displacement i.lattice) μ
  have hf : Integrable (fun p : JetPrototype.Phase => JetFreeTransport.free η K α γ s d (r*t) a
      (shift (displacement i.lattice) p)) (μ.prod volume) := by
    apply hb.mono' ((JetFreeTransport.measurable_free η K α γ s d (r*t) a).comp
      (measurable_shift _)).aestronglyMeasurable
    filter_upwards [] with p
    dsimp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (JetFreeTransport.free_nonneg hK hs.le hd.le η α γ (r*t) a _)]
    exact JetFreeTransport.free_le_barrier hK hd hα hγ hs (mul_pos hr ht)
      (htmax.trans (by norm_num)) η a _
  exact (ColdDilationMeasure.integrable_dilate hr Ω (hc.sub hf)).const_mul r

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Local L1 convergence of the cold/free velocity-average error -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_average_error_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (k : ℤ) (a : Bool) (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) :
    Tendsto (fun n => ∫ x, |∫ v, ψ v*E.coldLabelError k a n t (x,v)|
      ∂JetPrototype.spaceVolume.restrict Ω) atTop (𝓝 0) := by
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  have hl := E.coldLabel_free_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq
    k a hk ht htU Ω hΩ
  change Tendsto (fun n => ∫ p, |E.coldLabelError k a n t p|
    ∂(JetPrototype.spaceVolume.restrict Ω).prod volume) atTop (𝓝 0) at hl
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => abs_nonneg _)))
    _ (by simpa only [mul_zero] using hl.const_mul B)
  filter_upwards [S.eventually_scaled_slab hs₀ E.horizon_limit htU] with n hn
  have htime : S.radius (E.indices n)*t ≤ 1 :=
    (hn t ⟨ht.le,le_rfl⟩).2.trans
      (((shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le).trans (by norm_num))
  have hi := E.coldLabelError_integrable hs₀ hsmax hη hηmax hK hα hγ hd₀ hq k a n ht htime Ω hΩ
  rw [← integral_const_mul,integral_prod _ (hi.abs.const_mul B)]
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
    (hi.abs.const_mul B).integral_prod_left
  filter_upwards [hi.prod_right_ae] with x hx
  rw [← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le (hx.abs.const_mul B)
  filter_upwards [] with v
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_right (hψB v) (abs_nonneg _)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The velocity averages of the actual retained cold colors -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal Pointwise
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelDensity_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω) :
    Integrable (E.coldLabelDensity k a n t) ((JetPrototype.spaceVolume.restrict Ω).prod volume) := by
  let r := S.radius (E.indices n)
  let μ := JetPrototype.spaceVolume.restrict (r • Ω)
  have hr : 0 < r := S.radius_pos hs₀ (E.indices n)
  let _ : IsFiniteMeasure μ :=
    isFiniteMeasure_restrict.mpr (hΩ.image (continuous_const_smul r)).measure_lt_top.ne
  have hi := (F.approximation (E.indices n)).cold_physical_integrable hs₀ hsmax hη hηmax
    hK hd₀ hq (shrinkingHorizon_pos F.horizonScale_pos _).le (E.coldLabel k a n) (r*t) μ
  exact (ColdDilationMeasure.integrable_dilate hr Ω hi).const_mul r

theorem HotLimitExtraction.coldLabelError_eq (E : HotLimitExtraction S)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) (p : JetPrototype.Phase) :
    E.coldLabelError k a n t p = E.coldLabelDensity k a n t p-
      S.radius (E.indices n)*JetFreeTransport.free η K α γ
        (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)
        (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
        (S.radius (E.indices n)*t) a (S.radius (E.indices n) • p.1,p.2) := by
  have hz : displacement (E.coldLabel k a n).lattice = 0 := by
    change (JetLattice.transverseShift 0,JetLattice.axialShift 0) = 0
    ext i <;> simp [JetLattice.transverseShift,JetLattice.axialShift]
  unfold coldLabelError coldLabelDensity
  rw [hz]
  simp only [WeightedTranslation.shift,sub_zero]
  change _ = _
  ring

theorem HotLimitExtraction.coldLabelAverage_sub_free (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀) (hq : q < 2)
    (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 < t)
    (htmax : S.radius (E.indices n)*t ≤ 1) (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    ∀ᵐ x ∂JetPrototype.spaceVolume.restrict Ω,
      E.coldLabelAverage k a n t ψ x-E.coldLabelFreeAverage k a n t ψ x =
        ∫ v, ψ v*E.coldLabelError k a n t (x,v) := by
  have hm := hψ.comp (measurable_snd : Measurable (Prod.snd : JetPrototype.Phase → Velocity))
  have hi := (E.coldLabelDensity_integrable hs₀ hsmax hη hηmax hK hd₀.le hq k a n t Ω hΩ).bdd_mul
    hm.aestronglyMeasurable (ae_of_all _ (fun p => hψB p.2))
  have he := (E.coldLabelError_integrable hs₀ hsmax hη hηmax hK hα hγ hd₀ hq k a n ht htmax Ω hΩ).bdd_mul
    hm.aestronglyMeasurable (ae_of_all _ (fun p => hψB p.2))
  filter_upwards [hi.prod_right_ae,he.prod_right_ae] with x hix hex
  dsimp only [Function.comp_apply] at hix hex
  have hd : Integrable (fun v => S.radius (E.indices n)*JetFreeTransport.free η K α γ
      (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)
      (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
      (S.radius (E.indices n)*t) a (S.radius (E.indices n) • x,v)*ψ v) := by
    apply (hix.sub hex).congr
    filter_upwards [] with v
    dsimp only [Pi.sub_apply]
    rw [E.coldLabelError_eq]
    ring
  have hident : (fun v => ψ v*E.coldLabelError k a n t (x,v)) =
      (fun v => ψ v*E.coldLabelDensity k a n t (x,v)-
        S.radius (E.indices n)*JetFreeTransport.free η K α γ
          (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)
          (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
          (S.radius (E.indices n)*t) a (S.radius (E.indices n) • x,v)*ψ v) := by
    funext v
    rw [E.coldLabelError_eq]
    ring
  rw [hident,integral_sub hix hd]
  rfl

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # L1 comparison of the actual and free cold velocity averages -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_average_free_L1_limit_q80_oai (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1/4) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (k : ℤ) (a : Bool) (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Tendsto (fun n => ∫ x, |E.coldLabelAverage k a n t ψ x-E.coldLabelFreeAverage k a n t ψ x|
      ∂JetPrototype.spaceVolume.restrict Ω) atTop (𝓝 0) := by
  have hl := E.coldLabel_average_error_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq k a hk ht htU Ω hΩ hψB
  apply hl.congr'
  filter_upwards [S.eventually_scaled_slab hs₀ E.horizon_limit htU] with n hn
  have htime : S.radius (E.indices n)*t ≤ 1 :=
    (hn t ⟨ht.le,le_rfl⟩).2.trans
      (((shrinkingHorizon_le F.horizonScale_pos _).trans F.horizonScale_le).trans (by norm_num))
  apply integral_congr_ae
  filter_upwards [E.coldLabelAverage_sub_free hs₀ hsmax hη hηmax hK hα hγ hd₀ hq
    k a n ht htime Ω hΩ hψ hψB] with x hx
  rw [hx]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.coldLabel_average_free_L1_limit_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.coldLabel_average_free_L1_limit_q80_oai
