-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_zero_solution_large_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:57:06.501773+00:00
-- url     : https://prove2.me/submissions/04b53946-6725-4980-b6b0-6fba4fdab665

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_rebuilt_envelope_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_uniform_hot_source_q80

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

theorem frequency_congr {f g : Velocity → ℝ} (hfg : f =ᵐ[volume] g) (b : ℝ) (v : Velocity) :
    CollisionCutoff.frequency b f v = CollisionCutoff.frequency b g v := by
  unfold CollisionCutoff.frequency
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg] with w hw
  rw [hw]

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

theorem frequency_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (b : ℝ) :
    frequency b f =ᵐ[μ.prod volume] frequency b g := by
  have hx := ae_ae_of_ae_prod hfg
  have he : ∀ᵐ x ∂μ, ∀ v, CollisionCutoff.frequency b (fun w => f (x, w)) v =
      CollisionCutoff.frequency b (fun w => g (x, w)) v :=
    hx.mono (fun x hx v => CollisionNullSets.frequency_congr hx b v)
  exact (quasiMeasurePreserving_fst.ae he).mono (fun p hp => hp p.2)

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

/-! # Mass, energy, and entropy of the full cold datum -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetGeometry
open BoltzmannNonuniqueness.JetThermalEntropy
open BoltzmannNonuniqueness.JetDatum

namespace BoltzmannNonuniqueness.JetDatumMoments

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

end BoltzmannNonuniqueness.JetDatumMoments

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

/-! # Fixed-scale uniform bounds for the cold envelope -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetEnvelopeBound

theorem U_le_H {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1 / 16) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η q : ℝ) (a : Bool) (x : Space) (v : Velocity) :
    JetSupersolution.U η K α γ s d t a (x, v) ≤
      (2 * JetGaussianEscape.constant α * (K / s) * (d ^ 3)⁻¹ * tiltConstant) * H q v := by
  have hD : 0 ≤ JetBarrier.distanceSquared η α γ s t a x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he : Real.exp (-(1 / 8 : ℝ) * JetBarrier.distanceSquared η α γ s t a x / (d ^ 2 * t)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hD) (by positivity)
  have hg : Real.exp (-4 * ‖v‖ ^ 2) ≤ tiltConstant * H q v :=
    (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg ‖v‖])).trans (JetGaussianEscape.gaussian_le_hot q v)
  have hc : 0 ≤ JetGaussianEscape.constant α * (K / s) * (d ^ 3)⁻¹ := by
    unfold JetGaussianEscape.constant
    have := JetThermalKernel.bound_pos
    positivity
  have hb := JetGaussianEscape.barrier_velocity_decay hK hα hs hd hdmax htmax η γ a x v
  calc
    _ ≤ 2 * JetBarrier.barrier η K α γ s d t a (x, v) :=
      JetSupersolution.le_twice_barrier hK hs hd hα hγ ht htmax hε η a (x, v)
    _ ≤ 2 * (JetGaussianEscape.constant α * (K / s) * (d ^ 3)⁻¹ * (1 * (tiltConstant * H q v))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact hb.trans (by
        rw [mul_assoc _ (Real.exp _) (Real.exp _)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul he hg (Real.exp_nonneg _) (by norm_num)) hc)
    _ = _ := by ring

end BoltzmannNonuniqueness.JetEnvelopeBound

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetEnvelopeTimeIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integral cold supersolution, including the initial right trace -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetIntegralSupersolution

theorem integral_from_right_trace {u g : ℝ → ℝ} {l t : ℝ} (ht : 0 < t)
    (hu : ∀ a, 0 < a → a ≤ t → AbsolutelyContinuousOnInterval u a t)
    (hl : Tendsto u (𝓝[>] 0) (𝓝 l)) (hg : IntervalIntegrable g volume 0 t)
    (hd : ∀ᵐ r, r ∈ Ioc 0 t → g r ≤ deriv u r) :
    l + (∫ r in 0..t, g r) ≤ u t := by
  have hgsub (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ t) :
      IntervalIntegrable g volume a b := by
    apply hg.mono_set
    rw [uIcc_of_le hab, uIcc_of_le ht.le]
    intro r hr
    exact ⟨ha.trans hr.1, hr.2.trans hb⟩
  have hineq (a : ℝ) (ha : a ∈ Ioc 0 t) : u a + (∫ r in a..t, g r) ≤ u t := by
    have hac := hu a ha.1 ha.2
    have hbound : (∫ r in a..t, g r) ≤ ∫ r in a..t, deriv u r := by
      apply intervalIntegral.integral_mono_ae_restrict ha.2
        (hgsub a t ha.1.le ha.2 le_rfl) hac.intervalIntegrable_deriv
      filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Icc] with r hr hmem
      exact hr ⟨ha.1.trans_le hmem.1, hmem.2⟩
    rw [hac.integral_deriv_eq_sub] at hbound
    linarith
  have hp := (hg.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)).continuousOn
  rw [uIcc_of_le ht.le] at hp
  have hplim : Tendsto (fun a => ∫ r in 0..a, g r) (𝓝[>] 0) (𝓝 0) := by
    have h := (hp 0 ⟨le_rfl, ht.le⟩).tendsto
    rw [nhdsWithin_Icc_eq_nhdsGE ht] at h
    simpa only [intervalIntegral.integral_same] using
      h.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
  have hlim : Tendsto (fun a => u a + ((∫ r in 0..t, g r) - ∫ r in 0..a, g r))
      (𝓝[>] 0) (𝓝 (l + ∫ r in 0..t, g r)) := by
    simpa only [sub_zero] using hl.add (tendsto_const_nhds.sub hplim)
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT ht] with a ha
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hgsub 0 a le_rfl ha.1.le ha.2.le) (hgsub a t ha.1.le ha.2.le le_rfl)
  have hb := hineq a ⟨ha.1, ha.2.le⟩
  linarith

end BoltzmannNonuniqueness.JetIntegralSupersolution

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

theorem numerator_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ : ℝ) :
    0 ≤ K * max 1 (α * γ)⁻¹ * JetGaussianProduct.coefficient + JetRemainderSheet.uniformConstant K := by
  have hm : 0 ≤ max 1 (α * γ)⁻¹ := zero_le_one.trans (le_max_left _ _)
  have hJ := JetThermalKernel.bound_pos
  have hL := JetComparisonCoefficient.coefficient_ge_one hK
  unfold JetGaussianProduct.coefficient JetRemainderSheet.uniformConstant
  positivity

theorem coefficient_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ q : ℝ) : 0 ≤ coefficient K α γ q :=
  mul_nonneg (numerator_nonneg hK α γ) (sheetConstant_pos α q).le

end BoltzmannNonuniqueness.JetMainGain

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

/-! # Positive integral contraction along measurable characteristics

This lemma constructs a fixed point of a bounded positive source map.
The collision source and its quantitative estimates are supplied separately.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P : Type*} [MeasurableSpace P]

theorem value_difference {T L S D : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hD : 0 ≤ D)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : P → ℝ) {g h : Domain P → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S) (hgh : ∀ z, |g z - h z| ≤ D)
    (z : Domain P) : |value T L flow f₀ g z - value T L flow f₀ h z| ≤ T * D := by
  have ht := time_bounds hT z.1
  have hgi := damped_integrable hT hL hflow hgm hg z
  have hhi := damped_integrable hT hL hflow hhm hh z
  unfold value
  rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hgi hhi]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := time T z.1)
    (C := D) (f := fun r =>
      Real.exp (-L * (time T z.1 - r)) * g (r, flow (r - time T z.1) z.2) -
      Real.exp (-L * (time T z.1 - r)) * h (r, flow (r - time T z.1) z.2))
    (fun r hr => by
      rw [uIoc_of_le ht.1] at hr
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-L * (time T z.1 - r)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [hr.2])
      exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans (by simpa using hgh _))
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hb
  exact hb.trans (by nlinarith)

/-- Positive Picard iteration converges in the complete sup-norm space. -/
theorem exists_fixed_point {T L A R S K : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hS : 0 ≤ S) (hK : 0 ≤ K)
    (hball : A + T * S ≤ R) (hsmall : T * K < 1)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ : P → ℝ} (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (source : BoundedMeasurable.PositiveBall (Domain P) R → Domain P → ℝ)
    (hsm : ∀ f, Measurable (source f))
    (hsb : ∀ f z, 0 ≤ source f z ∧ source f z ≤ S)
    (hsl : ∀ f g z, |source f z - source g z| ≤ K * dist f g) :
    ∃ f : BoundedMeasurable.PositiveBall (Domain P) R,
      ∀ z, f.val z = value T L flow f₀ (source f) z := by
  let step : BoundedMeasurable.PositiveBall (Domain P) R →
      BoundedMeasurable.PositiveBall (Domain P) R := fun f =>
    ⟨BoundedMeasurable.ofBounded (Domain P) (value T L flow f₀ (source f))
      (measurable_value hT hflow hf₀m (hsm f)) (A + T * S)
      (fun z => by
        rw [abs_of_nonneg (value_bounds hT hL hA hS flow hf₀ (hsb f) z).1]
        exact (value_bounds hT hL hA hS flow hf₀ (hsb f) z).2),
      fun z => ⟨(value_bounds hT hL hA hS flow hf₀ (hsb f) z).1,
        (value_bounds hT hL hA hS flow hf₀ (hsb f) z).2.trans hball⟩⟩
  have hc : ContractingWith ⟨T * K, mul_nonneg hT hK⟩ step := by
    constructor
    · exact hsmall
    · apply LipschitzWith.of_dist_le_mul
      intro f g
      change dist (step f).val (step g).val ≤ (T * K) * dist f g
      apply BoundedMeasurable.dist_le (Domain P) (by positivity)
      intro z
      have h := value_difference hT hL (mul_nonneg hK dist_nonneg) hflow f₀
        (hsm f) (hsm g)
        (fun z => by rw [abs_of_nonneg (hsb f z).1]; exact (hsb f z).2)
        (fun z => by rw [abs_of_nonneg (hsb g z).1]; exact (hsb g z).2)
        (hsl f g) z
      simpa only [step, BoundedMeasurable.ofBounded_apply, mul_assoc] using h
  let zero : BoundedMeasurable.PositiveBall (Domain P) R :=
    ⟨BoundedMeasurable.ofBounded (Domain P) (fun _ => 0) measurable_const 0
      (fun _ => by simp), fun _ => ⟨le_rfl, hR⟩⟩
  let : Nonempty (BoundedMeasurable.PositiveBall (Domain P) R) := ⟨zero⟩
  refine ⟨hc.fixedPoint, ?_⟩
  intro z
  have he := congrArg (fun f : BoundedMeasurable.PositiveBall (Domain P) R => f.val z)
    hc.fixedPoint_isFixedPt
  exact he.symm

end BoltzmannNonuniqueness.PositiveIntegral

end

end

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

/-! # Dependence of the characteristic map on its initial value -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PositiveIntegral

variable {P : Type*} [MeasurableSpace P]

theorem value_difference_initial {T L S D I : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (hD : 0 ≤ D) (_hI : 0 ≤ I)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ k₀ : P → ℝ} (hfk : ∀ p, |f₀ p-k₀ p| ≤ I)
    {g h : Domain P → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S) (hgh : ∀ z, |g z-h z| ≤ D)
    (z : Domain P) : |value T L flow f₀ g z-value T L flow k₀ h z| ≤ I+T*D := by
  have hsource := value_difference hT hL hD hflow f₀ hgm hhm hg hh hgh z
  have hinitial : |value T L flow f₀ h z-value T L flow k₀ h z| ≤ I := by
    have heq : value T L flow f₀ h z-value T L flow k₀ h z =
        Real.exp (-L*time T z.1) * (f₀ (flow (-time T z.1) z.2)-k₀ (flow (-time T z.1) z.2)) := by
      unfold value
      ring
    rw [heq, abs_mul, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-L*time T z.1) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (time_bounds hT z.1).1)
    exact (mul_le_mul he (hfk _) (abs_nonneg _) (by norm_num)).trans_eq (one_mul I)
  exact (abs_sub_le _ _ _).trans ((add_le_add hsource hinitial).trans_eq (add_comm _ _))

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedBranchingBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # Constant damping preserves an absolutely continuous supersolution -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.DampedSupersolution

theorem integral_bound {u g : ℝ → ℝ} {l t L : ℝ} (ht : 0 < t)
    (hu : ∀ a, 0 < a → a ≤ t → AbsolutelyContinuousOnInterval u a t)
    (hl : Tendsto u (𝓝[>] 0) (𝓝 l))
    (hui : IntervalIntegrable u volume 0 t) (hgi : IntervalIntegrable g volume 0 t)
    (hd : ∀ᵐ r, r ∈ Ioc 0 t → HasDerivAt u (deriv u r) r ∧ g r ≤ deriv u r) :
    Real.exp (-L * t) * l +
      (∫ r in 0..t, Real.exp (-L * (t-r)) * (g r + L * u r)) ≤ u t := by
  have hec : ContDiff ℝ 1 (fun r : ℝ => Real.exp (L * r)) := by fun_prop
  have hei : IntervalIntegrable (fun r => Real.exp (L*r) * (g r + L*u r)) volume 0 t :=
    (hgi.add (hui.const_mul L)).continuousOn_mul hec.continuous.continuousOn
  have htr : Tendsto (fun r => Real.exp (L*r) * u r) (𝓝[>] 0) (𝓝 l) := by
    have he := hec.continuous.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa using he.mul hl
  have hb := JetIntegralSupersolution.integral_from_right_trace ht
    (u := fun r => Real.exp (L*r) * u r)
    (fun a ha hat => hec.contDiffOn.absolutelyContinuousOnInterval.mul (hu a ha hat))
    htr hei (by
      filter_upwards [hd] with r hr hrt
      have he : HasDerivAt (fun r : ℝ => Real.exp (L*r)) (Real.exp (L*r)*L) r :=
        by simpa using ((hasDerivAt_id r).const_mul L).exp
      have hdprod : HasDerivAt (fun r => Real.exp (L*r) * u r)
          (Real.exp (L*r)*L*u r + Real.exp (L*r)*deriv u r) r :=
        he.mul (hr hrt).1
      rw [hdprod.deriv]
      nlinarith [mul_le_mul_of_nonneg_left (hr hrt).2 (Real.exp_nonneg (L*r))])
  have hm := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg (-L*t))
  have he : Real.exp (-L*t) * Real.exp (L*t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hi : Real.exp (-L*t) *
      (∫ r in 0..t, Real.exp (L*r) * (g r + L*u r)) =
      ∫ r in 0..t, Real.exp (-L*(t-r)) * (g r + L*u r) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [mul_add, hi, ← mul_assoc, he, one_mul] at hm
  exact hm

end BoltzmannNonuniqueness.DampedSupersolution

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ColdGaussianFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The scalar integral Gronwall step in cold-color comparison -/

noncomputable section

open MeasureTheory Set Filter

namespace BoltzmannNonuniqueness.ColdGronwall

/-- A nonnegative integrable error bounded by a constant times its past integral vanishes. -/
theorem eq_zero_of_integral_bound {z : ℝ → ℝ} {C T : ℝ} (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hi : IntervalIntegrable z volume 0 T) (hz : ∀ t ∈ Icc 0 T, 0 ≤ z t)
    (hb : ∀ t ∈ Icc 0 T, z t ≤ C * primitive z t) : ∀ t ∈ Icc 0 T, z t = 0 := by
  let W : ℝ → ℝ := fun t => Real.exp (-C * t) * primitive z t
  have hZ : AbsolutelyContinuousOnInterval (primitive z) 0 T :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-C * t)) := by fun_prop
  have hW : AbsolutelyContinuousOnInterval W 0 T := he.contDiffOn.absolutelyContinuousOnInterval.mul hZ
  have hder : ∀ᵐ t, t ∈ Icc 0 T → deriv W t ≤ 0 := by
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    have hzt := ht (by simpa only [uIcc_of_le hT] using hmem) 0 (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have het := ((hasDerivAt_id t).const_mul (-C)).exp
    have hw := het.mul hzt
    change HasDerivAt W _ t at hw
    rw [hw.deriv]
    have hbt := hb t hmem
    have hp := mul_le_mul_of_nonneg_left hbt (Real.exp_pos (-C * t)).le
    dsimp only [primitive, id] at hp ⊢
    nlinarith only [hp]
  intro t ht
  have hWt : AbsolutelyContinuousOnInterval W 0 t := by
    apply hW.mono
    rw [uIcc_of_le ht.1, uIcc_of_le hT]
    intro r hr
    exact ⟨hr.1, hr.2.trans ht.2⟩
  have hint : 0 ≤ ∫ r in 0..t, -deriv W r := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict ht.1
    filter_upwards [ae_restrict_of_ae hder, ae_restrict_mem measurableSet_Icc] with r hr hrt
    exact neg_nonneg.mpr (hr ⟨hrt.1, hrt.2.trans ht.2⟩)
  rw [intervalIntegral.integral_neg, hWt.integral_deriv_eq_sub] at hint
  have hW0 : W 0 = 0 := by simp [W, primitive]
  rw [hW0] at hint
  have hZt : primitive z t ≤ 0 := by
    dsimp only [W] at hint
    nlinarith [Real.exp_pos (-C * t)]
  exact le_antisymm ((hb t ht).trans (mul_nonpos_of_nonneg_of_nonpos hC hZt)) (hz t ht)

end BoltzmannNonuniqueness.ColdGronwall

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

/-! # Comparison for the damped scalar integral inequality -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveScalarComparison

theorem le_supersolution {T L K a : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hK : 0 ≤ K)
    {z u : ℝ → ℝ} {G : ℝ → ℝ → ℝ}
    (hzc : ContinuousOn z (Icc 0 T)) (huc : ContinuousOn u (Icc 0 T))
    (hzi : IntervalIntegrable (fun r => G r (z r)) volume 0 T)
    (hui : IntervalIntegrable (fun r => G r (u r)) volume 0 T)
    (hz : ∀ t ∈ Icc 0 T, z t ≤ Real.exp (-L*t)*a+
      ∫ r in 0..t, Real.exp (-L*(t-r))*G r (z r))
    (hu : ∀ t ∈ Icc 0 T, Real.exp (-L*t)*a+
      ∫ r in 0..t, Real.exp (-L*(t-r))*G r (u r) ≤ u t)
    (hlip : ∀ r ∈ Icc 0 T, G r (z r)-G r (u r) ≤ K*max 0 (z r-u r)) :
    ∀ t ∈ Icc 0 T, z t ≤ u t := by
  let d (r : ℝ) := max 0 (z r-u r)
  have hdc : ContinuousOn d (Icc 0 T) :=
    (show Continuous (fun x : ℝ => max 0 x) from continuous_const.max continuous_id).comp_continuousOn
      (hzc.sub huc)
  have hdi : IntervalIntegrable d volume 0 T := hdc.intervalIntegrable_of_Icc hT
  have hn (r : ℝ) : 0 ≤ d r := le_max_left _ _
  have hbound (t : ℝ) (ht : t ∈ Icc 0 T) : d t ≤ K*ColdGronwall.primitive d t := by
    have hsub : uIcc 0 t ⊆ uIcc 0 T := by
      rw [uIcc_of_le ht.1,uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2
    have hzt := (hzi.mono_set hsub).continuousOn_mul
      (show ContinuousOn (fun r => Real.exp (-L*(t-r))) (uIcc 0 t) by fun_prop)
    have hut := (hui.mono_set hsub).continuousOn_mul
      (show ContinuousOn (fun r => Real.exp (-L*(t-r))) (uIcc 0 t) by fun_prop)
    have hdt := hdi.mono_set hsub
    have hdiff : z t-u t ≤ ∫ r in 0..t,
        Real.exp (-L*(t-r))*(G r (z r)-G r (u r)) := by
      have h₁ := hz t ht
      have h₂ := hu t ht
      rw [show (fun r => Real.exp (-L*(t-r))*(G r (z r)-G r (u r))) =
        (fun r => Real.exp (-L*(t-r))*G r (z r)-Real.exp (-L*(t-r))*G r (u r)) by
          funext r; ring, intervalIntegral.integral_sub hzt hut]
      linarith
    have hint : (∫ r in 0..t, Real.exp (-L*(t-r))*(G r (z r)-G r (u r))) ≤
        K*ColdGronwall.primitive d t := by
      rw [ColdGronwall.primitive,← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on ht.1
        ((hzi.sub hui).mono_set hsub |>.continuousOn_mul (by fun_prop)) (hdt.const_mul K)
      intro r hr
      have he : Real.exp (-L*(t-r)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [hr.2])
      calc
        _ ≤ Real.exp (-L*(t-r))*(K*d r) :=
          mul_le_mul_of_nonneg_left (hlip r ⟨hr.1,hr.2.trans ht.2⟩) (Real.exp_pos _).le
        _ ≤ K*d r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right he (mul_nonneg hK (hn r))
    exact max_le (mul_nonneg hK (intervalIntegral.integral_nonneg_of_forall ht.1 hn)) (hdiff.trans hint)
  have hd0 := ColdGronwall.eq_zero_of_integral_bound hK hT hdi (fun r _ => hn r) hbound
  intro t ht
  have hd := hd0 t ht
  have h := le_max_right 0 (z t-u t)
  change z t-u t ≤ d t at h
  rw [hd] at h
  linarith

end BoltzmannNonuniqueness.PositiveScalarComparison

end

end

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

theorem size_nonneg (f : JetPrototype.Phase → ℝ) : 0 ≤ size f := ENNReal.toReal_nonneg

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

theorem size_le_ae {f : JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hR : 0 ≤ R) (hf : ∀ᵐ p ∂FlightMeasure.phaseVolume, |f p| ≤ R) : size f ≤ R := by
  have h : eLpNorm f ∞ FlightMeasure.phaseVolume ≤ ENNReal.ofReal R := by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (hf.mono (fun p hp => by
      simpa only [Real.norm_eq_abs] using hp))
  simpa only [size,ENNReal.toReal_ofReal hR] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

theorem measurable_canonical {f : ℝ × JetPrototype.Phase → ℝ} (hfm : Measurable f)
    (hnorm : Measurable (fun t => size (fun p => f (t,p)))) : Measurable (canonical f) :=
  hfm.min (hnorm.comp measurable_fst)

theorem canonical_bounds {f : ℝ × JetPrototype.Phase → ℝ}
    (hf : ∀ u, 0 ≤ f u) (u : ℝ × JetPrototype.Phase) :
    0 ≤ canonical f u ∧ canonical f u ≤ size (fun p => f (u.1,p)) ∧ canonical f u ≤ f u :=
  ⟨le_min (hf u) (size_nonneg _),min_le_right _ _,min_le_left _ _⟩

theorem canonical_ae_at_time {f : ℝ × JetPrototype.Phase → ℝ}
    (hfm : Measurable f) {R : ℝ} (hf : ∀ u, |f u| ≤ R) (t : ℝ) :
    (fun p => canonical f (t,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => f (t,p)) := by
  filter_upwards [ae_abs_le_size (hfm.comp (measurable_const.prodMk measurable_id))
    (fun p => hf (t,p))] with p hp
  exact min_eq_left ((le_abs_self _).trans hp)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Scalar upper integral bounds for the essential norm of a mild solution -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem value_le_ae {T L S a t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (ht : t ∈ Icc 0 T)
    {f₀ : JetPrototype.Phase → ℝ} {g : ℝ × JetPrototype.Phase → ℝ} {w : ℝ → ℝ}
    (hgm : Measurable g) (hg : ∀ u, |g u| ≤ S) (hw : IntervalIntegrable w volume 0 T)
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, f₀ p ≤ a)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume,
      u.1 ∈ Ioc 0 T → g u ≤ w u.1) :
    ∀ᵐ p ∂FlightMeasure.phaseVolume,
      PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p) ≤
        Real.exp (-L*t)*a+∫ r in 0..t, Real.exp (-L*(t-r))*w r := by
  have hi := (FlightMeasure.flight_measurePreserving (-t)).quasiMeasurePreserving.ae hinit
  have hs := (FlightMeasure.spacetime_measurePreserving t).quasiMeasurePreserving.ae hsource
  have hsp := (Measure.measurePreserving_swap (μ := FlightMeasure.phaseVolume) (ν := volume)).quasiMeasurePreserving.ae hs
  have hr := ae_ae_of_ae_prod hsp
  have hwt : IntervalIntegrable w volume 0 t := hw.mono_set (by
    rw [uIcc_of_le ht.1,uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl ht.2)
  have hwi : IntervalIntegrable (fun r => Real.exp (-L*(t-r))*w r) volume 0 t :=
    hwt.continuousOn_mul (by fun_prop)
  filter_upwards [hi,hr] with p hip hrp
  unfold PositiveIntegral.value
  rw [GaussianLocal.time_eq ht]
  apply add_le_add (mul_le_mul_of_nonneg_left hip (Real.exp_pos _).le)
  have hgi := PositiveIntegral.damped_integrable hT hL GaussianLocal.measurable_flight hgm hg (t,p)
  rw [GaussianLocal.time_eq ht] at hgi
  apply intervalIntegral.integral_mono_ae_restrict ht.1 hgi hwi
  filter_upwards [ae_restrict_of_ae hrp,ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) 0)] with r hr hrmem hr0
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact hr ⟨lt_of_le_of_ne hrmem.1 hr0.symm,hrmem.2.trans ht.2⟩

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

theorem canonical_ae {f : ℝ × JetPrototype.Phase → ℝ} (hfm : Measurable f)
    {R : ℝ} (hf : ∀ u, |f u| ≤ R)
    (hnorm : Measurable (fun t => size (fun p => f (t,p)))) :
    canonical f =ᵐ[(volume : Measure ℝ).prod FlightMeasure.phaseVolume] f := by
  apply (ae_prod_iff_ae_ae (measurableSet_eq_fun (measurable_canonical hfm hnorm) hfm)).mpr
  exact ae_of_all _ (canonical_ae_at_time hfm hf)

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

theorem mild_size_le_of_ae {T L S a t : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L)
    (ha : 0 ≤ a) (ht : t ∈ Icc 0 T)
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ} {w : ℝ → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ u, |g u| ≤ S)
    (hw : IntervalIntegrable w volume 0 T) (hwn : ∀ r ∈ Icc 0 T, 0 ≤ w r)
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, f₀ p ≤ a)
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume,
      u.1 ∈ Ioc 0 T → g u ≤ w u.1)
    (hfn : ∀ u, 0 ≤ f u)
    (hfix : (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p))) :
    size (fun p => f (t,p)) ≤ Real.exp (-L*t)*a+∫ r in 0..t, Real.exp (-L*(t-r))*w r := by
  apply size_le_ae (f := fun p => f (t,p)) (hfm.comp (measurable_const.prodMk measurable_id))
  · apply add_nonneg (mul_nonneg (Real.exp_pos _).le ha)
    exact intervalIntegral.integral_nonneg ht.1 (fun r hr =>
      mul_nonneg (Real.exp_pos _).le (hwn r ⟨hr.1,hr.2.trans ht.2⟩))
  · filter_upwards [value_le_ae hT hL ht hgm hg hw hinit hsource,hfix] with p hp he
    rw [abs_of_nonneg (hfn (t,p)),he]
    exact hp

end BoltzmannNonuniqueness.PhaseEssSup

end

end

section

/-! # Bounding a total essential norm by its cold and hot parts -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem size_le_cold_add_hot {f c : JetPrototype.Phase → ℝ} {R B Z : ℝ}
    (hfm : Measurable f) (hcm : Measurable c) (hB : 0 ≤ B)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R) (hc : ∀ p, 0 ≤ c p ∧ c p ≤ f p)
    (hcB : ∀ p, c p ≤ B) (hz : size (fun p => f p-c p) ≤ Z) :
    size f ≤ B+Z := by
  have habs (p) : |f p-c p| ≤ R := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hc p).2)]
    linarith [(hf p).2,(hc p).1]
  have hZ : 0 ≤ Z := (size_nonneg _).trans hz
  apply size_le_ae hfm (add_nonneg hB hZ)
  filter_upwards [ae_abs_le_size (hfm.sub hcm) habs] with p hp
  change |f p-c p| ≤ size (fun p => f p-c p) at hp
  rw [abs_of_nonneg (hf p).1]
  rw [abs_of_nonneg (sub_nonneg.mpr (hc p).2)] at hp
  linarith [hcB p]

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

theorem value_eq_of_time_eq {T : ℝ} (hT : 0 ≤ T) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) {g h : ℝ × JetPrototype.Phase → ℝ}
    (hgh : ∀ r ∈ Icc 0 T, ∀ p, g (r,p) = h (r,p)) (u : ℝ × JetPrototype.Phase) :
    value T L JetBarrier.flight f₀ g u = value T L JetBarrier.flight f₀ h u := by
  unfold value
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (time_bounds hT u.1).1] at hr
  dsimp only
  rw [hgh r ⟨hr.1,hr.2.trans (time_bounds hT u.1).2⟩]

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

section

/-! # Restricting and translating the damped mild integral -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PositiveIntegral

theorem shifted_value {U s t : ℝ} (ht : t-s ∈ Icc 0 U) (L : ℝ)
    (f₀ : JetPrototype.Phase → ℝ) (g : ℝ × JetPrototype.Phase → ℝ)
    (p : JetPrototype.Phase) :
    value U L JetBarrier.flight f₀ g (t-s,p) =
      Real.exp (-L*(t-s))*f₀ (JetBarrier.flight (s-t) p) +
      ∫ r in s..t, Real.exp (-L*(t-r))*g (r-s,JetBarrier.flight (r-t) p) := by
  unfold value
  rw [GaussianLocal.time_eq ht]
  have he : -(t-s) = s-t := by ring
  rw [he]
  congr 1
  have hi := intervalIntegral.integral_comp_add_right
    (fun r => Real.exp (-L*(t-r))*g (r-s,JetBarrier.flight (r-t) p)) s
    (a := 0) (b := t-s)
  rw [zero_add,sub_add_cancel] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  have h₁ : t-(r+s) = t-s-r := by ring
  have h₂ : r+s-s = r := by ring
  have h₃ : r+s-t = r-(t-s) := by ring
  rw [h₁,h₂,h₃]

end BoltzmannNonuniqueness.PositiveIntegral

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ZeroProfileParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A polynomial zero-seed supersolution uniform in the smallest jet scale -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.ZeroProfile

theorem source_le_derivative {M C B D δ t : ℝ} {m : ℕ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : B ≤ D) (hD : 0 ≤ D) (hδ : 0 < δ)
    (ht : 0 < t) (ht₁ : t ≤ 1) (hsmall : C*D*t ≤ 1)
    (hm : M+2 ≤ (m+1 : ℕ)) :
    source M C B δ m t (profile D m t) ≤ D*(m+1 : ℕ)*t^m := by
  have hlinear : M/(t+δ)*(D*t^(m+1)) ≤ M*D*t^m := by
    have hr : t/(t+δ) ≤ 1 := (div_le_one (by positivity : 0 < t+δ)).mpr (by linarith)
    calc
      _ = (M*D*t^m)*(t/(t+δ)) := by rw [pow_succ]; ring
      _ ≤ (M*D*t^m)*1 := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := mul_one _
  have hpow : t^(m+2) ≤ t := by
    rw [show m+2 = (m+1)+1 by omega,pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ ht.le ht₁) ht.le).trans_eq (one_mul t)
  have hq : C*D*t^(m+2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hD)).trans hsmall
  have hquad : C*(D*t^(m+1))^2 ≤ D*t^m := by
    calc
      _ = (D*t^m)*(C*D*t^(m+2)) := by simp only [pow_succ] <;> ring
      _ ≤ (D*t^m)*1 := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := mul_one _
  have hforcing : B*t^m ≤ D*t^m := mul_le_mul_of_nonneg_right hB (pow_nonneg ht.le _)
  have hcoef := mul_le_mul_of_nonneg_right hm (show 0 ≤ D*t^m by positivity)
  unfold source profile
  nlinarith only [hlinear,hquad,hforcing,hcoef]

theorem profile_hasDerivAt (D : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (profile D m) (D*(m+1 : ℕ)*t^m) t := by
  refine (((hasDerivAt_id t).pow (m+1)).const_mul D).congr_deriv (Eq.symm ?_)
  · simp only [Nat.add_sub_cancel, mul_one, id_eq]
    ring

end BoltzmannNonuniqueness.ZeroProfile

end

end

section

/-! # Damped integral supersolution for the zero hot seed -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.ZeroProfile

theorem integral_supersolution {M C B D δ T L t : ℝ} {m : ℕ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : B ≤ D) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hT₁ : T ≤ 1) (hsmall : C*D*T ≤ 1)
    (hm : M+2 ≤ (m+1 : ℕ)) (ht : t ∈ Icc 0 T) :
    (∫ r in 0..t, Real.exp (-L*(t-r)) *
      (source M C B δ m r (profile D m r)+L*profile D m r)) ≤ profile D m t := by
  by_cases ht0 : t=0
  · simp [ht0,profile]
  have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have huc : ContDiff ℝ 1 (profile D m) := by unfold profile; fun_prop
  have hden : ContinuousOn (fun r => M/(r+δ)) (Icc 0 t) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const)
      (fun r hr => ne_of_gt (by linarith [hr.1]))
  have hgc : ContinuousOn (fun r => source M C B δ m r (profile D m r)) (Icc 0 t) :=
    ((hden.mul huc.continuous.continuousOn).add
      ((huc.continuous.continuousOn.pow 2).const_mul C)).add
        ((continuousOn_id.pow m).const_mul B)
  have h := DampedSupersolution.integral_bound (L := L) htp
    (fun _ _ _ => huc.contDiffOn.absolutelyContinuousOnInterval)
    (show Tendsto (profile D m) (𝓝[>] 0) (𝓝 0) from by
      simpa [profile] using huc.continuous.continuousAt.tendsto.mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
    (huc.continuous.intervalIntegrable 0 t) (hgc.intervalIntegrable_of_Icc htp.le) (by
      filter_upwards [] with r hr
      have hd := profile_hasDerivAt D m r
      refine ⟨?_,?_⟩
      · simpa only [hd.deriv] using hd
      · rw [hd.deriv]
        exact source_le_derivative hM hC hB hD hδ hr.1 (hr.2.trans (ht.2.trans hT₁))
          ((mul_le_mul_of_nonneg_left (hr.2.trans ht.2) (mul_nonneg hC hD)).trans hsmall) hm)
  simpa only [mul_zero,zero_add] using h

end BoltzmannNonuniqueness.ZeroProfile

end

end

section

/-! # One-sided Lipschitz estimate for the scalar hot majorant -/

noncomputable section

namespace BoltzmannNonuniqueness.ZeroProfile

theorem source_difference {M C B δ L R t z u : ℝ} {m : ℕ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : 0 < δ)
    (ht : 0 ≤ t) (hz : 0 ≤ z) (hu : 0 ≤ u) (hzR : z ≤ R) (huR : u ≤ R) :
    (source M C B δ m t z+L*z)-(source M C B δ m t u+L*u) ≤
      (M/δ+2*C*R+L)*max 0 (z-u) := by
  have hd : 0 ≤ M/(t+δ) := div_nonneg hM (by linarith)
  have hdle : M/(t+δ) ≤ M/δ :=
    div_le_div_of_nonneg_left hM hδ (by linarith)
  have hc : 0 ≤ M/(t+δ)+C*(z+u)+L := by positivity
  have hcle : M/(t+δ)+C*(z+u)+L ≤ M/δ+2*C*R+L := by
    nlinarith [mul_nonneg hC (show 0 ≤ R-z by linarith),
      mul_nonneg hC (show 0 ≤ R-u by linarith)]
  have he : (source M C B δ m t z+L*z)-(source M C B δ m t u+L*u) =
      (M/(t+δ)+C*(z+u)+L)*(z-u) := by unfold source; ring
  rw [he]
  by_cases hzu : 0 ≤ z-u
  · rw [max_eq_right hzu]
    exact mul_le_mul_of_nonneg_right hcle hzu
  · rw [max_eq_left (le_of_not_ge hzu),mul_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hc (le_of_not_ge hzu)

end BoltzmannNonuniqueness.ZeroProfile

end

end

section

/-! # Uniform polynomial bound for a zero-seed scalar integral inequality -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.ZeroProfile

theorem le_profile {M C B D δ T L R : ℝ} {m : ℕ} {z : ℝ → ℝ}
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : B ≤ D) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hT : 0 ≤ T) (hT₁ : T ≤ 1) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hsmall : C*D*T ≤ 1) (hm : M+2 ≤ (m+1 : ℕ))
    (hzc : ContinuousOn z (Icc 0 T)) (hzb : ∀ t ∈ Icc 0 T, 0 ≤ z t ∧ z t ≤ R)
    (hz : ∀ t ∈ Icc 0 T, z t ≤ ∫ r in 0..t,
      Real.exp (-L*(t-r))*(source M C B δ m r (z r)+L*z r)) :
    ∀ t ∈ Icc 0 T, z t ≤ profile D m t := by
  have huc : ContinuousOn (profile D m) (Icc 0 T) := by unfold profile; fun_prop
  have hden : ContinuousOn (fun r => M/(r+δ)) (Icc 0 T) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const)
      (fun r hr => ne_of_gt (by linarith [hr.1]))
  have hgc (y : ℝ → ℝ) (hy : ContinuousOn y (Icc 0 T)) :
      ContinuousOn (fun r => source M C B δ m r (y r)+L*y r) (Icc 0 T) := by
    exact (((hden.mul hy).add ((hy.pow 2).const_mul C)).add
      ((continuousOn_id.pow m).const_mul B)).add (hy.const_mul L)
  apply PositiveScalarComparison.le_supersolution (a := 0)
    (G := fun r y => source M C B δ m r y+L*y) hT hL
    (show 0 ≤ M/δ+2*C*(R+D)+L by positivity) hzc huc
    ((hgc z hzc).intervalIntegrable_of_Icc hT)
    ((hgc (profile D m) huc).intervalIntegrable_of_Icc hT)
  · intro t ht
    simpa only [mul_zero,zero_add] using hz t ht
  · intro t ht
    simpa only [mul_zero,zero_add] using integral_supersolution hM hC hB hD hδ hT₁ hsmall hm ht
  · intro t ht
    have hp : 0 ≤ profile D m t := mul_nonneg hD (pow_nonneg ht.1 _)
    have hpD : profile D m t ≤ D := by
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ ht.1 (ht.2.trans hT₁)) hD).trans_eq (mul_one D)
    exact source_difference hM hC hL hδ ht.1 (hzb t ht).1 hp
      ((hzb t ht).2.trans (le_add_of_nonneg_right hD))
      (hpD.trans (le_add_of_nonneg_left hR))

theorem profile_le_square {D T t : ℝ} {m : ℕ} (hD : 0 ≤ D)
    (hT₁ : T ≤ 1) (hDT : D*T ≤ 1) (hm : 2 ≤ m) (ht : t ∈ Icc 0 T) :
    profile D m t ≤ t^2 := by
  have ht₁ : t ≤ 1 := ht.2.trans hT₁
  have hp : t^(m-2) ≤ 1 := pow_le_one₀ ht.1 ht₁
  have hDt : D*t ≤ 1 := (mul_le_mul_of_nonneg_left ht.2 hD).trans hDT
  have hfac : (D*t)*t^(m-2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hD ht.1)).trans (by simpa using hDt)
  calc
    profile D m t = ((D*t)*t^(m-2))*t^2 := by
      unfold profile
      rw [show m+1 = (m-2)+2+1 by omega,pow_succ,pow_add]
      ring
    _ ≤ 1*t^2 := mul_le_mul_of_nonneg_right hfac (sq_nonneg t)
    _ = t^2 := one_mul _

end BoltzmannNonuniqueness.ZeroProfile

end

end

section

/-! # A positive uniform time for the polynomial zero-seed comparison -/

noncomputable section

namespace BoltzmannNonuniqueness.ZeroProfile

private theorem small_product {a t : ℝ} (ha : 0 ≤ a) (ht : t ≤ (a+1)⁻¹) : a*t ≤ 1 := by
  calc
    a*t ≤ a*(a+1)⁻¹ := mul_le_mul_of_nonneg_left ht ha
    _ = a/(a+1) := (div_eq_mul_inv _ _).symm
    _ ≤ 1 := (div_le_one (by linarith : 0 < a+1)).mpr (by linarith)

theorem parameters_exist {M C : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (E : ℕ → ℝ) (hE : ∀ m, 0 ≤ E m) :
    ∃ (m : ℕ) (D T : ℝ), 2 ≤ m ∧ 0 < D ∧ 0 < T ∧ T ≤ 1/32 ∧
      M+2 ≤ (m+1 : ℕ) ∧ (M+C)*E m ≤ D ∧ C*D*T ≤ 1 ∧
      E m*T^(m+1) ≤ 1 ∧ D*T ≤ 1 := by
  obtain ⟨m,hm⟩ := exists_nat_gt (M+2)
  have hEm := hE m
  let D := (M+C)*E m+1
  have hD : 0 < D := by dsimp [D] <;> positivity
  let T := min (1/32 : ℝ) (min (C*D+1)⁻¹ (min (E m+1)⁻¹ (D+1)⁻¹))
  have hT : 0 < T := by dsimp [T] <;> positivity
  have hT₃₂ : T ≤ 1/32 := min_le_left _ _
  have hTc : T ≤ (C*D+1)⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have hTe : T ≤ (E m+1)⁻¹ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hTd : T ≤ (D+1)⁻¹ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hm₂ : 2 ≤ m := by
    have h : (2:ℝ) < m := by linarith
    have hn : 2 < m := by exact_mod_cast h
    omega
  refine ⟨m,D,T,hm₂,hD,hT,hT₃₂,?_,?_,small_product (mul_nonneg hC hD.le) hTc,?_,small_product hD.le hTd⟩
  · push_cast
    linarith
  · dsimp [D]
    linarith
  · have hp : T^(m+1) ≤ T := by
      rw [pow_succ]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (pow_le_one₀ hT.le (show T ≤ 1 by linarith)) hT.le
    exact (mul_le_mul_of_nonneg_left hp (hE m)).trans (small_product (hE m) hTe)

end BoltzmannNonuniqueness.ZeroProfile

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

theorem actual_gain_upper_difference {q A B D : ℝ} {v : Velocity} (hv : v ∈ good q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, f w - g w ≤ D * H q w) (b : ℝ) :
    CollisionCutoff.gain b f v - CollisionCutoff.gain b g v ≤
      (D * (A+B) * HotApplication.realBound q) * H q v := by
  have hbase := integrable_H_gain hv
  have hfi := GainOrder.integrable_of_le hfm hf hfB v (GainOrder.integrable_const_mul A v hbase)
  have hgi := GainOrder.integrable_of_le hgm hg hgB v (GainOrder.integrable_const_mul B v hbase)
  have hfc := CollisionCutoff.integrable_gain b hfm hf v hfi
  have hgc := CollisionCutoff.integrable_gain b hgm hg v hgi
  calc
    _ = ∫ p, CollisionCutoff.integrand b f v p - CollisionCutoff.integrand b g v p
        ∂((volume : Measure Velocity).prod sphereArea) := (integral_sub hfc hgc).symm
    _ ≤ ∫ p, (D*(A+B)) * GainOrder.integrand (H q) v p
        ∂((volume : Measure Velocity).prod sphereArea) :=
      integral_mono (hfc.sub hgc) (hbase.const_mul _)
        (GainUpperDifference.cutoff_integrand_bound hA hB hD hf hg hfB hgB hfg b v)
    _ = (D*(A+B)) * BoltzmannNonuniqueness.gain (fun p => H q p.2) 0 v := integral_const_mul _ _
    _ ≤ (D*(A+B)) * (HotApplication.realBound q * H q v) :=
      mul_le_mul_of_nonneg_left (H_gain_bound hv) (mul_nonneg hD (add_nonneg hA hB))
    _ = _ := by ring

theorem actual_gain_difference {q A B D : ℝ} {v : Velocity} (hv : v ∈ good q)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ w, 0 ≤ f w) (hg : ∀ w, 0 ≤ g w)
    (hfB : ∀ w, f w ≤ A * H q w) (hgB : ∀ w, g w ≤ B * H q w)
    (hfg : ∀ w, |f w - g w| ≤ D * H q w) (b : ℝ) :
    |CollisionCutoff.gain b f v - CollisionCutoff.gain b g v| ≤
      (D*(A+B)*HotApplication.realBound q) * H q v := by
  have h₁ := actual_gain_upper_difference hv hA hB hD hfm hgm hf hg hfB hgB
    (fun w => (le_abs_self _).trans (hfg w)) b
  have h₂ := actual_gain_upper_difference hv hB hA hD hgm hfm hg hf hgB hfB
    (fun w => (le_abs_self _).trans (by simpa only [abs_sub_comm] using hfg w)) b
  rw [add_comm B A] at h₂
  exact abs_le.mpr ⟨by linarith, h₁⟩

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

theorem gain_difference {q A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ B)
    (hfg : ∀ p, |f p-g p| ≤ D) (b : ℝ) (p : X × Velocity) :
    |gain q b f p - gain q b g p| ≤ D*(A+B)*HotApplication.realBound q := by
  unfold gain
  split_ifs with hv
  · rw [← sub_div, abs_div, abs_of_pos (H_pos q p.2)]
    apply (div_le_iff₀ (H_pos q p.2)).mpr
    apply actual_gain_difference hv hA hB hD
      ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
      ((measurable_density hgm q).comp (measurable_const.prodMk measurable_id))
      (fun w => mul_nonneg (H_nonneg _ _) (hf _).1)
      (fun w => mul_nonneg (H_nonneg _ _) (hg _).1)
      (fun w => (mul_le_mul_of_nonneg_left (hf _).2 (H_nonneg _ _)).trans_eq (mul_comm _ _))
      (fun w => (mul_le_mul_of_nonneg_left (hg _).2 (H_nonneg _ _)).trans_eq (mul_comm _ _))
    intro w
    change |H q w * f (p.1,w) - H q w * g (p.1,w)| ≤ _
    rw [← mul_sub, abs_mul, abs_of_nonneg (H_nonneg _ _)]
    exact (mul_le_mul_of_nonneg_left (hfg _) (H_nonneg _ _)).trans_eq (mul_comm _ _)
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg hD (add_nonneg hA hB)) (HotApplication.realBound_pos q).le

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
theorem density_difference {q D : ℝ} {f g : X × Velocity → ℝ}
    (hfg : ∀ p, |f p-g p| ≤ D) (p : X × Velocity) :
    |density q f p - density q g p| ≤ D * H q p.2 := by
  unfold density
  rw [← mul_sub, abs_mul, abs_of_nonneg (H_nonneg _ _)]
  exact (mul_le_mul_of_nonneg_left (hfg p) (H_nonneg _ _)).trans_eq (mul_comm _ _)

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

theorem frequency_difference {q A B D b : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ A) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ B)
    (hfg : ∀ p, |f p-g p| ≤ D) (p : X × Velocity) :
    |frequency q b f p - frequency q b g p| ≤ D * CutoffLipschitz.frequencyConstant q b :=
  CutoffLipschitz.frequency_difference hq hb
    ((measurable_density hfm q).comp (measurable_const.prodMk measurable_id))
    ((measurable_density hgm q).comp (measurable_const.prodMk measurable_id))
    (fun w => (density_bounds hf (p.1,w)).1) (fun w => (density_bounds hg (p.1,w)).1)
    (fun w => (density_bounds hf (p.1,w)).2) (fun w => (density_bounds hg (p.1,w)).2)
    (fun w => density_difference hfg (p.1,w)) p.2

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

theorem source_difference {q b L R D : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hD : 0 ≤ D)
    {f g : X × Velocity → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ R) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ R)
    (hfg : ∀ p, |f p-g p| ≤ D) (p : X × Velocity) :
    |source q b L f p - source q b L g p| ≤
      (2*R*(HotApplication.realBound q + CutoffLipschitz.frequencyConstant q b)+L)*D := by
  have hgain := gain_difference (q := q) hR hR hD hfm hgm hf hg hfg b p
  have hνdiff := frequency_difference hq hb hfm hgm hf hg hfg p
  have hνfb : |frequency q b f p| ≤ R * CutoffLipschitz.frequencyConstant q b := by
    rw [abs_of_nonneg (frequency_nonneg (fun p => (hf p).1) q b p)]
    exact frequency_bound hq hb hfm hf p
  have hgabs : |g p| ≤ R := by rw [abs_of_nonneg (hg p).1]; exact (hg p).2
  have hloss : |frequency q b f p * f p - frequency q b g p * g p| ≤
      2 * CutoffLipschitz.frequencyConstant q b * R * D := by
    calc
      _ = |frequency q b f p * (f p-g p) + (frequency q b f p-frequency q b g p)*g p| := by
        congr 1; ring
      _ ≤ |frequency q b f p| * |f p-g p| + |frequency q b f p-frequency q b g p| * |g p| := by
        simpa only [abs_mul] using abs_add_le (frequency q b f p * (f p-g p))
          ((frequency q b f p-frequency q b g p)*g p)
      _ ≤ (R*CutoffLipschitz.frequencyConstant q b)*D + (D*CutoffLipschitz.frequencyConstant q b)*R :=
        add_le_add (mul_le_mul hνfb (hfg p) (abs_nonneg _)
          (mul_nonneg hR (CutoffLipschitz.frequencyConstant_nonneg hb q)))
          (mul_le_mul hνdiff hgabs (abs_nonneg _)
            (mul_nonneg hD (CutoffLipschitz.frequencyConstant_nonneg hb q)))
      _ = _ := by ring
  calc
    _ = |(gain q b f p-gain q b g p)+L*(f p-g p)-
        (frequency q b f p*f p-frequency q b g p*g p)| := by unfold source; congr 1; ring
    _ ≤ |gain q b f p-gain q b g p|+L*|f p-g p|+
        |frequency q b f p*f p-frequency q b g p*g p| := by
      have ha : |(gain q b f p-gain q b g p)+L*(f p-g p)| ≤
          |gain q b f p-gain q b g p|+L*|f p-g p| := by
        simpa only [abs_mul, abs_of_nonneg hL] using
          abs_add_le (gain q b f p-gain q b g p) (L*(f p-g p))
      exact (abs_sub _ _).trans (add_le_add ha le_rfl)
    _ ≤ D*(R+R)*HotApplication.realBound q+L*D+
        2*CutoffLipschitz.frequencyConstant q b*R*D :=
      add_le_add (add_le_add hgain (mul_le_mul_of_nonneg_left (hfg p) hL)) hloss
    _ = _ := by ring

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Polynomial control of a hot remainder satisfying the mild equation a.e. -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.PhaseEssSup

theorem zero_seed_bound_ae {T L S R M C B D δ : ℝ} {m : ℕ}
    (hT : 0 ≤ T) (hT₁ : T ≤ 1) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hB : 0 ≤ B) (hBD : B ≤ D) (hD : 0 ≤ D)
    (hδ : 0 < δ) (hsmall : C*D*T ≤ 1) (hm : M+2 ≤ (m+1 : ℕ))
    {f₀ : JetPrototype.Phase → ℝ} {g f : ℝ × JetPrototype.Phase → ℝ}
    (hgm : Measurable g) (hfm : Measurable f) (hg : ∀ u, |g u| ≤ S)
    (hf : ∀ u, 0 ≤ f u ∧ f u ≤ R)
    (hzc : ContinuousOn (fun t => size (fun p => f (t,p))) (Icc 0 T))
    (hinit : ∀ᵐ p ∂FlightMeasure.phaseVolume, f₀ p ≤ 0)
    (hfix : ∀ t ∈ Icc 0 T, (fun p => f (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ g (t,p)))
    (hsource : ∀ᵐ u ∂(volume : Measure ℝ).prod FlightMeasure.phaseVolume,
      u.1 ∈ Ioc 0 T → g u ≤
        ZeroProfile.source M C B δ m u.1 (size (fun p => f (u.1,p)))+
          L*size (fun p => f (u.1,p))) :
    ∀ t ∈ Icc 0 T, size (fun p => f (t,p)) ≤ ZeroProfile.profile D m t := by
  let z (t : ℝ) := size (fun p => f (t,p))
  have hden : ContinuousOn (fun t => M/(t+δ)) (Icc 0 T) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const)
      (fun t ht => ne_of_gt (by linarith [ht.1]))
  have hwc : ContinuousOn (fun t => ZeroProfile.source M C B δ m t (z t)+L*z t) (Icc 0 T) :=
    (((hden.mul hzc).add ((hzc.pow 2).const_mul C)).add
      ((continuousOn_id.pow m).const_mul B)).add (hzc.const_mul L)
  apply ZeroProfile.le_profile hM hC hBD hD hδ hT hT₁ hL hR hsmall hm hzc
  · intro t _
    exact ⟨size_nonneg _,size_le hR (hfm.comp (measurable_const.prodMk measurable_id))
      (fun p => by rw [abs_of_nonneg (hf (t,p)).1]; exact (hf (t,p)).2)⟩
  · intro t ht
    have hw : IntervalIntegrable (fun r => ZeroProfile.source M C B δ m r (z r)+L*z r)
        volume 0 T := hwc.intervalIntegrable_of_Icc hT
    have hwn (r : ℝ) (hr : r ∈ Icc 0 T) :
        0 ≤ ZeroProfile.source M C B δ m r (z r)+L*z r := by
      have hz : 0 ≤ z r := size_nonneg _
      have hr0 : 0 ≤ r := hr.1
      have hd : 0 < r+δ := by linarith [hr.1]
      unfold ZeroProfile.source
      positivity
    simpa only [mul_zero,zero_add] using
      mild_size_le_of_ae hT hL (by rfl : (0:ℝ) ≤ 0) ht hgm hfm hg hw hwn hinit hsource
        (fun u => (hf u).1) (hfix t ht)

end BoltzmannNonuniqueness.PhaseEssSup

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetColdLimitComparison
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Gaussian control of the actual finite annular datum -/

noncomputable section

open MeasureTheory
open scoped BigOperators
open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetFiniteGaussian

theorem coefficient_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η : ℝ) (j : ℕ) : 0 ≤ coefficient s₀ η K d₀ j := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (j+1)
  have hJ := JetThermalKernel.bound_pos
  unfold coefficient jetScale
  positivity

theorem amplitude_pos {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η : ℝ) (N : ℕ) : 0 < amplitude s₀ η K d₀ N := by
  have h := Finset.sum_nonneg (s := indices N)
    (fun i _ => coefficient_nonneg hs₀ hK hd₀ η i.1)
  unfold amplitude
  linarith

theorem term_bound {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1 / 8)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀ * (1 / 8 : ℝ) ^ 10 ≤ 1 / 64) (hα : 0 ≤ α) (hαmax : α ≤ 1 / 4)
    (γ : ℝ) (i : JetDatum.Index) (p : JetPrototype.Phase) :
    JetDatum.term s₀ η K α γ d₀ i p ≤ coefficient s₀ η K d₀ i.1 * JetGaussianMoments.kernel 2 p.2 := by
  have hs := DatumBounds.scale_pos (η := η) hs₀ (i.1+1)
  have hd : 0 < d₀ * jetScale s₀ η i.1 ^ 10 := mul_pos hd₀ (pow_pos hs _)
  have hcoef := coefficient_nonneg hs₀ hK hd₀.le η i.1
  by_cases hz : JetDatum.term s₀ η K α γ d₀ i p = 0
  · rw [hz]
    exact mul_nonneg hcoef (Real.exp_pos _).le
  have hv := JetSupport.density_support_two hd
    (JetDatumMoments.thermal_width_le hs₀ hsmax hη hd₀.le hwidth i.1) hα hαmax η K γ _ i.2 hz
  have hW : 1 ≤ Real.exp 8 * JetGaussianMoments.kernel 2 p.2 := by
    unfold JetGaussianMoments.kernel
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [norm_nonneg p.2]
  let A := (K / jetScale s₀ η i.1) * ((d₀ * jetScale s₀ η i.1 ^ 10) ^ 3)⁻¹ * JetThermalKernel.bound
  have hA : 0 ≤ A := by
    have hJ := JetThermalKernel.bound_pos
    dsimp [A]
    positivity
  calc
    _ ≤ A := JetBarrier.initial_density_bound hK hs hd.le η α γ i.2 p
    _ ≤ A * (Real.exp 8 * JetGaussianMoments.kernel 2 p.2) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hW hA
    _ = _ := by unfold coefficient; dsimp [A] <;> ring

end BoltzmannNonuniqueness.JetFiniteGaussian

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

theorem exists_normalized {q b L T A R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hloss : R * CutoffLipschitz.frequencyConstant q b ≤ L)
    (hball : A + T*(HotApplication.realBound q * R^2 + L*R) ≤ R)
    (hsmall : T*(2*R*(HotApplication.realBound q + CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) :
    ∃ f : ℝ × JetPrototype.Phase → ℝ, Measurable f ∧
      (∀ z, 0 ≤ f z ∧ f z ≤ R) ∧
      ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L f) z := by
  let S := HotApplication.realBound q * R^2 + L*R
  let K := 2*R*(HotApplication.realBound q + CutoffLipschitz.frequencyConstant q b)+L
  have hS : 0 ≤ S := by
    have := (HotApplication.realBound_pos q).le
    dsimp [S] <;> positivity
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K] <;> positivity
  obtain ⟨f,hf⟩ := PositiveIntegral.exists_fixed_point hT hL hA hR hS hK hball hsmall
    GaussianLocal.measurable_flight hf₀m hf₀
    (fun f => forcing q b L (fun z => f.val z))
    (fun f => measurable_forcing (BoundedMeasurable.measurable _ f.val) q b L)
    (fun f z => HotRepresentative.source_bounds hq hb hR hloss
      (GaussianLocal.measurable_state (BoundedMeasurable.measurable _ f.val))
      (fun p => f.property (p.1.1,(p.1.2,p.2))) ((z.1,z.2.1),z.2.2))
    (fun f g z => HotRepresentative.source_difference hq hb hL hR dist_nonneg
      (GaussianLocal.measurable_state (BoundedMeasurable.measurable _ f.val))
      (GaussianLocal.measurable_state (BoundedMeasurable.measurable _ g.val))
      (fun p => f.property (p.1.1,(p.1.2,p.2)))
      (fun p => g.property (p.1.1,(p.1.2,p.2)))
      (fun p => BoundedMeasurable.dist_apply_le _ f.val g.val (p.1.1,(p.1.2,p.2)))
      ((z.1,z.2.1),z.2.2))
  exact ⟨fun z => f.val z, BoundedMeasurable.measurable _ f.val, f.property, hf⟩

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The actual finite periodic datum in the singular weighted space -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.WeightedFiniteSeed

theorem amplitude_pos {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀)
    (η : ℝ) (N : ℕ) : 0 < amplitude s₀ η K d₀ N :=
  mul_pos (JetFiniteGaussian.amplitude_pos hs₀ hK hd₀ η N) tiltConstant_pos

end BoltzmannNonuniqueness.WeightedFiniteSeed

end

end

section

/-! # Quantitative dependence in the singular weighted local space -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem normalized_difference {q b L T R I : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R) (hI : 0 ≤ I)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {f₀ g₀ : JetPrototype.Phase → ℝ} (hseed : ∀ p, |f₀ p-g₀ p| ≤ I)
    {f g : ℝ × JetPrototype.Phase → ℝ} (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ R) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ R)
    (hfeq : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L f) z)
    (hgeq : ∀ z, g z = PositiveIntegral.value T L JetBarrier.flight g₀ (forcing q b L g) z)
    (z : ℝ × JetPrototype.Phase) :
    |f z-g z| ≤ I / (1-T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L)) := by
  let P := ℝ × JetPrototype.Phase
  let f' := BoundedMeasurable.ofBounded P f hfm R
    (fun z => by rw [abs_of_nonneg (hf z).1]; exact (hf z).2)
  let g' := BoundedMeasurable.ofBounded P g hgm R
    (fun z => by rw [abs_of_nonneg (hg z).1]; exact (hg z).2)
  let K := 2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L
  let S := HotApplication.realBound q*R^2+L*R
  have hK : 0 ≤ K := by
    have := (HotApplication.realBound_pos q).le
    have := CutoffLipschitz.frequencyConstant_nonneg hb q
    dsimp [K] <;> positivity
  have hsource (u : ℝ × JetPrototype.Phase → ℝ) (hum : Measurable u)
      (hu : ∀ z, 0 ≤ u z ∧ u z ≤ R) (z) : |forcing q b L u z| ≤ S := by
    have h := HotRepresentative.source_bounds hq hb hR hloss (GaussianLocal.measurable_state hum)
      (fun p => hu (p.1.1,(p.1.2,p.2))) ((z.1,z.2.1),z.2.2)
    change 0 ≤ forcing q b L u z ∧ _ at h
    rw [abs_of_nonneg h.1]
    exact h.2
  have hdiff (z) : |forcing q b L f z-forcing q b L g z| ≤ K*dist f' g' :=
    HotRepresentative.source_difference hq hb hL hR dist_nonneg
      (GaussianLocal.measurable_state hfm) (GaussianLocal.measurable_state hgm)
      (fun p => hf (p.1.1,(p.1.2,p.2))) (fun p => hg (p.1.1,(p.1.2,p.2)))
      (fun p => BoundedMeasurable.dist_apply_le P f' g' (p.1.1,(p.1.2,p.2)))
      ((z.1,z.2.1),z.2.2)
  have hd : dist f' g' ≤ I+(T*K)*dist f' g' := by
    apply BoundedMeasurable.dist_le P (by positivity)
    intro z
    change |f z-g z| ≤ _
    rw [hfeq z,hgeq z]
    simpa only [mul_assoc] using PositiveIntegral.value_difference_initial hT hL
      (mul_nonneg hK dist_nonneg) hI GaussianLocal.measurable_flight hseed
      (measurable_forcing hfm q b L) (measurable_forcing hgm q b L)
      (hsource f hfm hf) (hsource g hgm hg) hdiff z
  have hden : 0 < 1-T*K := by dsimp [K] <;> linarith
  have hdist : dist f' g' ≤ I/(1-T*K) := (le_div_iff₀ hden).mpr (by nlinarith [hd])
  exact (BoundedMeasurable.dist_apply_le P f' g' z).trans hdist

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

theorem frequency_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q b : ℝ) : frequency q b f =ᵐ[μ.prod volume] frequency q b g :=
  KineticCollisionNullSets.frequency_congr μ (density_congr μ hfg q) b

theorem source_congr (μ : Measure X) [SFinite μ] {f g : X × Velocity → ℝ}
    (hfg : f =ᵐ[μ.prod volume] g) (q b L : ℝ) : source q b L f =ᵐ[μ.prod volume] source q b L g := by
  filter_upwards [gain_congr μ hfg q b,frequency_congr μ hfg q b,hfg] with p hg hν hp
  unfold source
  rw [hg,hν,hp]

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # The collision source only depends on its current time slice -/

noncomputable section

namespace BoltzmannNonuniqueness.WeightedLocal

theorem forcing_eq_of_slice {F G : ℝ × JetPrototype.Phase → ℝ} {s t : ℝ}
    (h : ∀ p, F (s,p) = G (t,p)) (q b L : ℝ) (p : JetPrototype.Phase) :
    forcing q b L F (s,p) = forcing q b L G (t,p) := by
  have he : timeSlice F s = timeSlice G t := funext (fun u => h u.2)
  exact congrArg (fun H => forcing q b L H (0,p)) he

theorem forcing_paste_left {s t : ℝ} (ht : t ≤ s) (F G : ℝ × JetPrototype.Phase → ℝ)
    (q b L : ℝ) (p : JetPrototype.Phase) :
    forcing q b L (paste s F G) (t,p) = forcing q b L F (t,p) :=
  forcing_eq_of_slice (fun _ => by simp only [paste,ite_eq_left ht]) q b L p

theorem forcing_paste_right {s t : ℝ} (ht : s < t) (F G : ℝ × JetPrototype.Phase → ℝ)
    (q b L : ℝ) (p : JetPrototype.Phase) :
    forcing q b L (paste s F G) (t,p) = forcing q b L G (t-s,p) :=
  forcing_eq_of_slice (fun _ => by simp only [paste,ite_eq_right (not_le.mpr ht)]) q b L p

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

theorem measurable_pull {f : ℝ × JetPrototype.Phase → ℝ} (hf : Measurable f) (y : Space) :
    Measurable (pull y f) := hf.comp (measurable_fst.prodMk ((measurable_shift y).comp measurable_snd))

theorem shift_flight (y : Space) (t : ℝ) (p : JetPrototype.Phase) :
    shift y (JetBarrier.flight t p) = JetBarrier.flight t (shift y p) := by
  apply Prod.ext
  · apply Prod.ext <;> dsimp [shift,JetBarrier.flight] <;> abel
  · rfl

theorem forcing_pull (q b L : ℝ) (y : Space) (f : ℝ × JetPrototype.Phase → ℝ) :
    WeightedLocal.forcing q b L (pull y f) = pull y (WeightedLocal.forcing q b L f) := rfl

theorem coldForcing_pull (q b L : ℝ) (y : Space) (F c : ℝ × JetPrototype.Phase → ℝ) :
    WeightedLocal.coldForcing q b L (pull y F) (pull y c) =
      pull y (WeightedLocal.coldForcing q b L F c) := rfl

theorem value_pull (T L : ℝ) (y : Space) (f₀ : JetPrototype.Phase → ℝ)
    (g : ℝ × JetPrototype.Phase → ℝ) :
    PositiveIntegral.value T L JetBarrier.flight (fun p => f₀ (shift y p)) (pull y g) =
      pull y (PositiveIntegral.value T L JetBarrier.flight f₀ g) := by
  funext z
  simp only [PositiveIntegral.value,pull,shift_flight]

theorem fixed_point_pull {q b L T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight f₀ (WeightedLocal.forcing q b L F) z)
    (y : Space) (z : ℝ × JetPrototype.Phase) :
    pull y F z = PositiveIntegral.value T L JetBarrier.flight
      (fun p => f₀ (shift y p)) (WeightedLocal.forcing q b L (pull y F)) z := by
  rw [forcing_pull,value_pull]
  exact hF _

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

theorem measurable_replacement {F C : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hCm : Measurable C)
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p)-C (t,p)))) :
    Measurable (replacement F C) :=
  hCm.add (PhaseEssSup.measurable_canonical (hFm.sub hCm) hnorm)

theorem replacement_bounds {F C : ℝ × JetPrototype.Phase → ℝ}
    (hC : ∀ u, 0 ≤ C u ∧ C u ≤ F u) (u : ℝ × JetPrototype.Phase) :
    C u ≤ replacement F C u ∧ replacement F C u ≤ F u ∧
      replacement F C u-C u ≤ PhaseEssSup.size (fun p => F (u.1,p)-C (u.1,p)) := by
  have h := PhaseEssSup.canonical_bounds (f := fun z => F z-C z)
    (fun z => sub_nonneg.mpr (hC z).2) u
  unfold replacement
  constructor
  · linarith [h.1]
  constructor
  · linarith [h.2.2]
  · linarith [h.2.1]

theorem replacement_ae {F C : ℝ × JetPrototype.Phase → ℝ} {R : ℝ}
    (hFm : Measurable F) (hCm : Measurable C)
    (hF : ∀ u, F u ≤ R) (hC : ∀ u, 0 ≤ C u ∧ C u ≤ F u)
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p)-C (t,p)))) :
    replacement F C =ᵐ[(volume : Measure ℝ).prod FlightMeasure.phaseVolume] F := by
  have hB (u) : |F u-C u| ≤ R := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hC u).2)]
    linarith [(hC u).1,hF u]
  filter_upwards [PhaseEssSup.canonical_ae (hFm.sub hCm) hB hnorm] with u hu
  change PhaseEssSup.canonical (fun z => F z-C z) u = F u-C u at hu
  unfold replacement
  rw [hu]
  ring

theorem state_congr {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[(volume : Measure ℝ).prod FlightMeasure.phaseVolume] G) :
    GaussianLocal.state F =ᵐ[((volume : Measure ℝ).prod JetPrototype.spaceVolume).prod volume]
      GaussianLocal.state G :=
  (measurePreserving_prodAssoc (volume : Measure ℝ) JetPrototype.spaceVolume
    (volume : Measure Velocity)).quasiMeasurePreserving.ae_eq_comp hFG

end BoltzmannNonuniqueness.HotCanonical

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem coldSource_congr_total (μ : Measure X) [SFinite μ]
    {F G : X × Velocity → ℝ} (hFG : F =ᵐ[μ.prod volume] G)
    (q b L : ℝ) (c : X × Velocity → ℝ) : coldSource q b L F c =ᵐ[μ.prod volume] coldSource q b L G c := by
  filter_upwards [frequency_congr μ hFG q b] with p hp
  unfold coldSource
  rw [hp]

end BoltzmannNonuniqueness.HotRepresentative

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

/-! # Almost-everywhere invariance of the colored forcing along spacetime -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

private theorem unstate_congr {f g : (ℝ × JetPrototype.Space) × Velocity → ℝ}
    (hfg : f =ᵐ[((volume : Measure ℝ).prod JetPrototype.spaceVolume).prod volume] g) :
    (fun u : ℝ × JetPrototype.Phase => f ((u.1,u.2.1),u.2.2)) =ᵐ[spacetimeVolume]
      (fun u : ℝ × JetPrototype.Phase => g ((u.1,u.2.1),u.2.2)) :=
  (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume : Measure ℝ) JetPrototype.spaceVolume
      (volume : Measure Velocity))).quasiMeasurePreserving.ae_eq_comp hfg

theorem forcing_congr {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[spacetimeVolume] G) (q b L : ℝ) :
    forcing q b L F =ᵐ[spacetimeVolume] forcing q b L G :=
  unstate_congr (HotRepresentative.source_congr ((volume : Measure ℝ).prod JetPrototype.spaceVolume)
    (HotCanonical.state_congr hFG) q b L)

theorem coldForcing_congr_total {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[spacetimeVolume] G) (q b L : ℝ) (c : ℝ × JetPrototype.Phase → ℝ) :
    coldForcing q b L F c =ᵐ[spacetimeVolume] coldForcing q b L G c :=
  unstate_congr (HotRepresentative.coldSource_congr_total
    ((volume : Measure ℝ).prod JetPrototype.spaceVolume) (HotCanonical.state_congr hFG) q b L
    (GaussianLocal.state c))

theorem remainderForcing_congr {I : Type*} [Countable I] {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[spacetimeVolume] G) (q b L : ℝ) (c : I → ℝ × JetPrototype.Phase → ℝ) :
    remainderForcing q b L F c =ᵐ[spacetimeVolume] remainderForcing q b L G c := by
  have hc : ∀ᵐ u ∂spacetimeVolume, ∀ i, coldForcing q b L F (c i) u = coldForcing q b L G (c i) u :=
    ae_all_iff.mpr (fun i => coldForcing_congr_total hFG q b L (c i))
  filter_upwards [forcing_congr hFG q b L,hc] with u hfu hcu
  unfold remainderForcing
  rw [hfu]
  congr 1
  exact tsum_congr hcu

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Mild equations stable under changing spatial representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem mildAE_of_pointwise {q b L T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L F) u) :
    MildAE q b L T f₀ F := fun t _ => ae_of_all _ (fun p => hF (t,p))

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

section

/-! # Pasting positive local solutions across an a.e. time slice -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem measurable_paste {s : ℝ} {F G : ℝ × JetPrototype.Phase → ℝ}
    (hF : Measurable F) (hG : Measurable G) : Measurable (paste s F G) :=
  hF.ite (measurableSet_le measurable_fst measurable_const)
    (hG.comp ((measurable_fst.sub measurable_const).prodMk measurable_snd))

theorem paste_bounds {s R : ℝ} {F G : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (u : ℝ × JetPrototype.Phase) : 0 ≤ paste s F G u ∧ paste s F G u ≤ R := by
  unfold paste
  split_ifs
  · exact hF u
  · exact hG _

theorem paste_pull (s : ℝ) (F G : ℝ × JetPrototype.Phase → ℝ)
    (y : JetPrototype.Space) :
    WeightedTranslation.pull y (paste s F G) =
      paste s (WeightedTranslation.pull y F) (WeightedTranslation.pull y G) := rfl

theorem paste_mildAE {q b L s U S : ℝ} (hs : 0 ≤ s) (hU : 0 ≤ U) (hL : 0 ≤ L)
    {f₀ g₀ : JetPrototype.Phase → ℝ} {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hsource : ∀ u, |forcing q b L (paste s F G) u| ≤ S)
    (hF : MildAE q b L s f₀ F) (hG : MildAE q b L U g₀ G)
    (hinit : g₀ =ᵐ[FlightMeasure.phaseVolume] (fun p => F (s,p))) :
    MildAE q b L (s+U) f₀ (paste s F G) := by
  have hprefix (t : ℝ) (ht : t ∈ Icc 0 s) (p : JetPrototype.Phase) :
      PositiveIntegral.value (s+U) L JetBarrier.flight f₀
          (forcing q b L (paste s F G)) (t,p) =
        PositiveIntegral.value s L JetBarrier.flight f₀ (forcing q b L F) (t,p) := by
    apply PositiveIntegral.value_eq_at_time ⟨ht.1,by linarith [ht.2]⟩ ht.2
    intro r hr p
    exact forcing_paste_left (hr.2.trans ht.2) F G q b L p
  intro t ht
  by_cases hts : t ≤ s
  · filter_upwards [hF t ⟨ht.1,hts⟩] with p hp
    rw [paste,ite_eq_left hts,hprefix t ⟨ht.1,hts⟩ p]
    exact hp
  · have hst : s < t := lt_of_not_ge hts
    have htu : t-s ∈ Icc 0 U := ⟨by linarith,by linarith [ht.2]⟩
    have hi := (FlightMeasure.flight_measurePreserving (s-t)).quasiMeasurePreserving.ae
      ((hF s ⟨hs,le_rfl⟩).symm.trans hinit.symm)
    filter_upwards [hG (t-s) htu,hi] with p hp hip
    have hr := PositiveIntegral.restart (add_nonneg hs hU) hL hs hst.le ht.2 f₀
      (measurable_forcing (measurable_paste hFm hGm) q b L) hsource p
    rw [hprefix s ⟨hs,le_rfl⟩,hip] at hr
    have hrest : (∫ r in s..t, Real.exp (-L*(t-r))*
        forcing q b L (paste s F G) (r,JetBarrier.flight (r-t) p)) =
        ∫ r in s..t, Real.exp (-L*(t-r))*
          forcing q b L G (r-s,JetBarrier.flight (r-t) p) := by
      apply intervalIntegral.integral_congr_ae
      apply ae_of_all
      intro r hr
      rw [uIoc_of_le hst.le] at hr
      rw [forcing_paste_right hr.1]
    rw [hrest,← PositiveIntegral.shifted_value htu] at hr
    rw [paste,ite_eq_right hts,hr]
    exact hp

end BoltzmannNonuniqueness.WeightedLocal

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClampedMildAE
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extending a mild representative constantly beyond its time interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem mildAE_all_times {q b L T : ℝ} (hT : 0 ≤ T) {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ} (hF : MildAE q b L T f₀ F) :
    ∀ t, (fun p => clampTime T F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight f₀
        (forcing q b L (clampTime T F)) (t,p)) := by
  have hs : ∀ r ∈ Icc 0 T, ∀ p,
      forcing q b L (clampTime T F) (r,p) = forcing q b L F (r,p) := by
    intro r hr p
    rw [forcing_clampTime,GaussianLocal.time_eq hr]
  intro t
  filter_upwards [hF (PositiveIntegral.time T t) (PositiveIntegral.time_bounds hT t)] with p hp
  change F (PositiveIntegral.time T t,p) = _
  rw [PositiveIntegral.value_eq_of_time_eq hT L f₀ hs (t,p)]
  rw [← PositiveIntegral.value_time_clamp hT L f₀ (forcing q b L F) (t,p)]
  exact hp

end BoltzmannNonuniqueness.WeightedLocal

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotCanonicalFamily
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A canonical representative above each cold color -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotCanonical

variable {I : Type*} [Countable I]

theorem family_properties {F : ℝ × JetPrototype.Phase → ℝ}
    {c : I → ℝ × JetPrototype.Phase → ℝ} {R : ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hcs : ∀ u, Summable (fun i => c i u)) (hcF : ∀ u, (∑' i, c i u) ≤ F u)
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p)))) :
    Measurable (familyReplacement F c) ∧
      (∀ u, 0 ≤ familyReplacement F c u ∧ familyReplacement F c u ≤ R) ∧
      (∀ s : Finset I, ∀ u, ∑ i ∈ s, c i u ≤ familyReplacement F c u) ∧
      (∀ u, familyReplacement F c u-∑' i, c i u ≤
        PhaseEssSup.size (fun p => F (u.1,p)-∑' i, c i (u.1,p))) ∧
      familyReplacement F c =ᵐ[WeightedLocal.spacetimeVolume] F := by
  have hC (u) : 0 ≤ (∑' i, c i u) ∧ (∑' i, c i u) ≤ F u :=
    ⟨tsum_nonneg (fun i => hcn i u),hcF u⟩
  have hb := replacement_bounds hC
  refine ⟨measurable_replacement hFm (Measurable.tsum hcm) hnorm,?_,?_,?_,
    replacement_ae hFm (Measurable.tsum hcm) hF hC hnorm⟩
  · intro u
    exact ⟨(hC u).1.trans (hb u).1,(hb u).2.1.trans (hF u)⟩
  · intro s u
    exact (Summable.sum_le_tsum s (fun i _ => hcn i u) (hcs u)).trans (hb u).1
  · exact fun u => (hb u).2.2

end BoltzmannNonuniqueness.HotCanonical

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

/-! # Covariance of sums and sources under relabeling of a cold family -/

noncomputable section

open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocal

variable {I : Type*} [Countable I]

omit [Countable I] in
theorem family_sum_pull (y : JetPrototype.Space) (e : I ≃ I)
    {c : I → ℝ × JetPrototype.Phase → ℝ} (hc : ∀ i, pull y (c i) = c (e i))
    (u : ℝ × JetPrototype.Phase) :
    (∑' i, c i (u.1,shift y u.2)) = ∑' i, c i u := by
  have he (i) : c i (u.1,shift y u.2) = c (e i) u := congrFun (hc i) u
  simp_rw [he]
  exact e.tsum_eq (fun i => c i u)

omit [Countable I] in
theorem familyReplacement_pull (y : JetPrototype.Space) (e : I ≃ I)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hF : pull y F = F) (hc : ∀ i, pull y (c i) = c (e i)) :
    pull y (HotCanonical.familyReplacement F c) = HotCanonical.familyReplacement F c := by
  funext u
  simp only [pull,HotCanonical.familyReplacement,HotCanonical.replacement,PhaseEssSup.canonical]
  rw [family_sum_pull y e hc u,show F (u.1,shift y u.2) = F u from congrFun hF u]

omit [Countable I] in
theorem remainderForcing_pull (q b L : ℝ) (y : JetPrototype.Space) (e : I ≃ I)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hF : pull y F = F) (hc : ∀ i, pull y (c i) = c (e i)) :
    pull y (remainderForcing q b L F c) = remainderForcing q b L F c := by
  have hf : pull y (forcing q b L F) = forcing q b L F := by rw [← forcing_pull,hF]
  funext u
  change forcing q b L F (u.1,shift y u.2)-_ = forcing q b L F u-_
  rw [show forcing q b L F (u.1,shift y u.2) = forcing q b L F u from congrFun hf u]
  congr 1
  have he (i) : coldForcing q b L F (c i) (u.1,shift y u.2) = coldForcing q b L F (c (e i)) u := by
    have h := coldForcing_pull q b L y F (c i)
    rw [hF,hc i] at h
    exact (congrFun h u).symm
  simp_rw [he]
  exact e.tsum_eq (fun i => coldForcing q b L F (c i) u)

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

/-! # Spatial covariance of clipped cold limits and dominated representatives -/

noncomputable section

open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedColdPicard_pull (q b L T : ℝ) (y : JetPrototype.Space)
    (F : ℝ × JetPrototype.Phase → ℝ) (c₀ : JetPrototype.Phase → ℝ) (n : ℕ) :
    clippedColdPicard q b L T (pull y F) (fun p => c₀ (shift y p)) n =
      pull y (clippedColdPicard q b L T F c₀ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [clippedColdPicard,ih,coldForcing_pull,value_pull,pull]
    rfl

theorem clippedColdLimit_pull (q b L T : ℝ) (y : JetPrototype.Space)
    (F : ℝ × JetPrototype.Phase → ℝ) (c₀ : JetPrototype.Phase → ℝ) :
    clippedColdLimit q b L T (pull y F) (fun p => c₀ (shift y p)) =
      pull y (clippedColdLimit q b L T F c₀) := by
  funext u
  simp only [clippedColdLimit,clippedColdPicard_pull,pull]

theorem normalizedFamily_reindex {I : Type*} (e : I ≃ I)
    (F : ℝ × JetPrototype.Phase → ℝ) (c : I → ℝ × JetPrototype.Phase → ℝ) (i : I) :
    normalizedFamily F (fun j => c (e j)) i = normalizedFamily F c (e i) := by
  classical
  funext u
  have he : (∀ s : Finset I, (∑ j ∈ s, c (e j) u) ≤ F u) ↔
      ∀ s : Finset I, (∑ j ∈ s, c j u) ≤ F u := by
    constructor
    · intro h s
      simpa only [Finset.sum_map,Equiv.coe_toEmbedding,Equiv.apply_symm_apply] using
        h (s.map e.symm.toEmbedding)
    · intro h s
      simpa only [Finset.sum_map,Equiv.coe_toEmbedding] using h (s.map e.toEmbedding)
  simp only [normalizedFamily,he]

theorem rebuiltColdFamily_pull {I : Type*} (q b L T : ℝ) (y : JetPrototype.Space)
    (F : ℝ × JetPrototype.Phase → ℝ) (c₀ : I → JetPrototype.Phase → ℝ) (i : I) :
    rebuiltColdFamily q b L T (pull y F) (fun j p => c₀ j (shift y p)) i =
      pull y (rebuiltColdFamily q b L T F c₀ i) := by
  unfold rebuiltColdFamily
  simp only [clippedColdLimit_pull]
  rfl

theorem rebuiltColdFamily_reindex {I : Type*} (e : I ≃ I) (q b L T : ℝ)
    (F : ℝ × JetPrototype.Phase → ℝ) (c₀ : I → JetPrototype.Phase → ℝ) (i : I) :
    rebuiltColdFamily q b L T F (fun j => c₀ (e j)) i =
      rebuiltColdFamily q b L T F c₀ (e i) :=
  normalizedFamily_reindex e F (fun j => clippedColdLimit q b L T F (c₀ j)) i

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Time clamping of the reconstructed cold family -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem clippedColdPicard_time_clamp {T : ℝ} (hT : 0 ≤ T) (q b L : ℝ)
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, F (PositiveIntegral.time T u.1,u.2) = F u)
    (c₀ : JetPrototype.Phase → ℝ) (n : ℕ) (u : ℝ × JetPrototype.Phase) :
    clippedColdPicard q b L T F c₀ n (PositiveIntegral.time T u.1,u.2) =
      clippedColdPicard q b L T F c₀ n u := by
  cases n with
  | zero => rfl
  | succ n =>
    change min (F (PositiveIntegral.time T u.1,u.2)) _ = min (F u) _
    rw [hF u,PositiveIntegral.value_time_clamp hT]

theorem clippedColdLimit_time_clamp {T : ℝ} (hT : 0 ≤ T) (q b L : ℝ)
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, F (PositiveIntegral.time T u.1,u.2) = F u)
    (c₀ : JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) :
    clippedColdLimit q b L T F c₀ (PositiveIntegral.time T u.1,u.2) =
      clippedColdLimit q b L T F c₀ u := by
  unfold clippedColdLimit
  simp only [clippedColdPicard_time_clamp hT q b L hF]

theorem rebuiltColdFamily_time_clamp {I : Type*} {T : ℝ} (hT : 0 ≤ T) (q b L : ℝ)
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, F (PositiveIntegral.time T u.1,u.2) = F u)
    (c₀ : I → JetPrototype.Phase → ℝ) (i : I) (u : ℝ × JetPrototype.Phase) :
    rebuiltColdFamily q b L T F c₀ i (PositiveIntegral.time T u.1,u.2) =
      rebuiltColdFamily q b L T F c₀ i u := by
  classical
  simp only [rebuiltColdFamily,normalizedFamily,hF,
    clippedColdLimit_time_clamp hT q b L hF]

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

/-! # Uniqueness on each weighted local construction interval -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem normalized_unique {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    (f₀ : JetPrototype.Phase → ℝ) {f g : ℝ × JetPrototype.Phase → ℝ}
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ R) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ R)
    (hfeq : ∀ z, f z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L f) z)
    (hgeq : ∀ z, g z = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L g) z) : f = g := by
  funext z
  have h := normalized_difference hq hb hL hT hR (le_refl 0) hloss hsmall
    (fun p => by simp only [sub_self,abs_zero,le_refl]) hfm hgm hf hg hfeq hgeq z
  rw [zero_div] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

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

theorem lifespan_pos {q b A : ℝ} (hb : 0 ≤ b) (hA : 0 < A) : 0 < lifespan q b A := by
  obtain ⟨_,hS,hK⟩ := bounds (q := q) hb hA
  exact lt_min (div_pos hA (by positivity)) (div_pos (by norm_num) (by positivity))

theorem small {q b A : ℝ} (hb : 0 ≤ b) (hA : 0 < A) :
    lifespan q b A*lipschitz q b A < 1 := by
  obtain ⟨_,_,hK⟩ := bounds (q := q) hb hA
  have hT := lifespan_pos (q := q) hb hA
  have h := (le_div_iff₀ (by positivity : 0 < lipschitz q b A+1)).mp
    (min_le_right (A/(sourceBound q b A+1)) ((1/2)/(lipschitz q b A+1)))
  change lifespan q b A*(lipschitz q b A+1) ≤ 1/2 at h
  nlinarith

theorem exists_solution {q b A : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A)
    {f₀ : JetPrototype.Phase → ℝ} (hf₀m : Measurable f₀)
    (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A) :
    ∃ F : ℝ × JetPrototype.Phase → ℝ, Measurable F ∧
      (∀ z, 0 ≤ F z ∧ F z ≤ 2*A) ∧
      ∀ z, F z = PositiveIntegral.value (lifespan q b A) (damping q b A)
        JetBarrier.flight f₀ (WeightedLocal.forcing q b (damping q b A) F) z := by
  obtain ⟨hL,hS,_⟩ := bounds (q := q) hb hA
  have hT := lifespan_pos (q := q) hb hA
  have h := (le_div_iff₀ (by positivity : 0 < sourceBound q b A+1)).mp
    (min_le_left (A/(sourceBound q b A+1)) ((1/2)/(lipschitz q b A+1)))
  change lifespan q b A*(sourceBound q b A+1) ≤ A at h
  have hball : A+lifespan q b A*sourceBound q b A ≤ 2*A := by nlinarith
  exact WeightedLocal.exists_normalized hq hb hL hT.le hA.le (by positivity) le_rfl hball
    (small hb hA) hf₀m hf₀

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # Periodic covariance follows from the constructed local uniqueness -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.WeightedTranslation

theorem solution_covariance {q b L T R : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hsmall : T*(2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L) < 1)
    {f₀ : JetPrototype.Phase → ℝ} {F : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z ∧ F z ≤ R)
    (hFeq : ∀ z, F z = PositiveIntegral.value T L JetBarrier.flight f₀ (WeightedLocal.forcing q b L F) z)
    (y : Space) (hseed : ∀ p, f₀ (shift y p) = f₀ p) : pull y F = F := by
  have hseed' : (fun p => f₀ (shift y p)) = f₀ := funext hseed
  have hfix (z) := fixed_point_pull hFeq y z
  rw [hseed'] at hfix
  exact WeightedLocal.normalized_unique hq hb hL hT hR hloss hsmall f₀
    (measurable_pull hFm y) hFm (fun z => hF (z.1,shift y z.2)) hF hfix hFeq

end BoltzmannNonuniqueness.WeightedTranslation

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

theorem coefficient_le_amplitude {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K)
    (hd₀ : 0 ≤ d₀) (η : ℝ) {N : ℕ} (i : JetDatum.Index)
    (hi : i ∈ JetFiniteGaussian.indices N) :
    JetFiniteGaussian.coefficient s₀ η K d₀ i.1 ≤ JetFiniteGaussian.amplitude s₀ η K d₀ N := by
  classical
  have h : JetFiniteGaussian.coefficient s₀ η K d₀ i.1 ≤
      ∑ j ∈ JetFiniteGaussian.indices N, JetFiniteGaussian.coefficient s₀ η K d₀ j.1 :=
    Finset.single_le_sum (fun (j : JetDatum.Index) _ =>
      JetFiniteGaussian.coefficient_nonneg hs₀ hK hd₀ η j.1) hi
  exact h.trans (le_add_of_nonneg_left zero_le_one)

theorem color_bound {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 ≤ η) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (γ q : ℝ) (N : ℕ) (i : JetLattice.Label) (p : JetPrototype.Phase) :
    color s₀ η K α γ d₀ q N i p ≤ WeightedFiniteSeed.amplitude s₀ η K d₀ N := by
  classical
  unfold color
  split_ifs with hi
  · apply (div_le_iff₀ (H_pos q p.2)).mpr
    have hmem : (i.annulus,i.positive) ∈ JetFiniteGaussian.indices N := by
      simp [JetFiniteGaussian.indices,hi]
    have hcoef := coefficient_le_amplitude hs₀ hK hd₀.le η (i.annulus,i.positive) hmem
    calc
      _ ≤ JetFiniteGaussian.coefficient s₀ η K d₀ i.annulus * JetGaussianMoments.kernel 2 p.2 :=
        JetFiniteGaussian.term_bound hs₀ hsmax hη hK hd₀ hwidth hα hαmax γ
          (i.annulus,i.positive) (WeightedTranslation.shift (displacement i.lattice) p)
      _ ≤ JetFiniteGaussian.amplitude s₀ η K d₀ N * JetGaussianMoments.kernel 2 p.2 :=
        mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le
      _ ≤ JetFiniteGaussian.amplitude s₀ η K d₀ N * (tiltConstant*H q p.2) :=
        mul_le_mul_of_nonneg_left (JetGaussianEscape.gaussian_le_hot q p.2)
          (JetFiniteGaussian.amplitude_pos hs₀ hK hd₀.le η N).le
      _ = _ := by unfold WeightedFiniteSeed.amplitude; ring
  · exact (WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N).le

theorem seed_bounds {s₀ η K d₀ α : ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8)
    (hη : 0 < η) (hηmax : η ≤ Real.log 2) (hK : 0 ≤ K) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (γ q : ℝ) (N : ℕ) (p : JetPrototype.Phase) :
    0 ≤ seed s₀ η K α γ d₀ q N p ∧
      seed s₀ η K α γ d₀ q N p ≤ WeightedFiniteSeed.amplitude s₀ η K d₀ N := by
  classical
  refine ⟨tsum_nonneg (fun i => color_nonneg hs₀ hK hd₀.le η α γ q N i p),?_⟩
  by_cases h : ∃ i, color s₀ η K α γ d₀ q N i p ≠ 0
  · obtain ⟨i,hi⟩ := h
    unfold seed
    rw [tsum_eq_single i (fun j hj => color_disjoint hs₀ hsmax hη hηmax K α γ d₀ q N p i j hj.symm hi)]
    exact color_bound hs₀ hsmax hη.le hK hd₀ hwidth hα hαmax γ q N i p
  · have hz (i) : color s₀ η K α γ d₀ q N i p = 0 := not_ne_iff.mp (not_exists.mp h i)
    simp only [seed,hz,tsum_zero]
    exact (WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N).le

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

/-! # Exact periodicity of the labeled initial datum -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem displacement_add (m n : JetLattice.Lattice) :
    displacement (m+n) = displacement m+displacement n := by
  apply Prod.ext
  · ext k
    simp [displacement,JetLattice.transverseShift]
  · simp [displacement,JetLattice.axialShift]

theorem shift_shift (y z : Space) (p : JetPrototype.Phase) :
    shift y (shift z p) = shift (y+z) p := by
  apply Prod.ext
  · dsimp [shift]
    abel
  · rfl

theorem color_shift (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (n : JetLattice.Lattice)
    (i : JetLattice.Label) (p : JetPrototype.Phase) :
    color s₀ η K α γ d₀ q N i (shift (displacement n) p) =
      color s₀ η K α γ d₀ q N (relabel n i) p := by
  change (if i.annulus < N then
    JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
      (shift (displacement i.lattice) (shift (displacement n) p)) / VelocityWeight.H q p.2 else 0) =
    (if i.annulus < N then
    JetDatum.term s₀ η K α γ d₀ (i.annulus,i.positive)
      (shift (displacement (i.lattice+n)) p) / VelocityWeight.H q p.2 else 0)
  rw [displacement_add,shift_shift]

theorem seed_periodic (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (n : JetLattice.Lattice)
    (p : JetPrototype.Phase) :
    seed s₀ η K α γ d₀ q N (shift (displacement n) p) = seed s₀ η K α γ d₀ q N p := by
  unfold seed
  simp_rw [color_shift]
  exact (relabel n).tsum_eq (fun i => color s₀ η K α γ d₀ q N i p)

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

/-! # Reduction of every spatial point to a bounded fundamental cell -/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem spatialMap_surjective : Function.Surjective JetPeriodicDatum.spatialMap := by
  intro y
  refine ⟨split.symm (y.2,y.1),?_⟩
  have h := split.apply_symm_apply (y.2,y.1)
  rw [split_apply] at h
  exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)

theorem exists_shift_in_cell (y : JetPrototype.Space) :
    ∃ (n : JetLattice.Lattice) (x : Velocity), (∀ k, |x k| ≤ 1) ∧
      y-displacement n = JetPeriodicDatum.spatialMap x := by
  obtain ⟨v,hv⟩ := spatialMap_surjective y
  let n : JetLattice.Lattice := fun k => ⌊v k⌋
  let x : Velocity := WithLp.toLp 2 (fun k => v k-(n k : ℝ))
  refine ⟨n,x,?_,?_⟩
  · intro k
    change |v k-(⌊v k⌋ : ℝ)| ≤ 1
    exact abs_le.mpr ⟨by linarith [Int.floor_le (v k)],by linarith [Int.lt_floor_add_one (v k)]⟩
  · rw [← hv]
    apply Prod.ext
    · apply (WithLp.ext_iff 2).mpr
      funext k
      rfl
    · rfl

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedHotGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A uniform positive local interval from an essentially bounded time slice -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

theorem exists_extension {q b A s : ℝ} (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hFn : ∀ p, 0 ≤ F (s,p))
    (hFA : ∀ᵐ p ∂FlightMeasure.phaseVolume, F (s,p) ≤ A)
    (hper : ∀ n, pull (JetCopyDatum.displacement n) F = F) :
    ∃ G : ℝ × JetPrototype.Phase → ℝ, Measurable G ∧
      (∀ u, 0 ≤ G u ∧ G u ≤ 2*A) ∧
      (∀ u, G u = PositiveIntegral.value (lifespan q b A) (damping q b A)
        JetBarrier.flight (clippedSlice A F s) (WeightedLocal.forcing q b (damping q b A) G) u) ∧
      ((fun p => G (0,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => F (s,p))) ∧
      ∀ n, pull (JetCopyDatum.displacement n) G = G := by
  have hsm : Measurable (clippedSlice A F s) :=
    (hFm.comp (measurable_const.prodMk measurable_id)).min measurable_const
  have hsb (p) : 0 ≤ clippedSlice A F s p ∧ clippedSlice A F s p ≤ A :=
    ⟨le_min (hFn p) hA.le,min_le_right _ _⟩
  obtain ⟨G,hGm,hG,hGeq⟩ := exists_solution hq hb hA hsm hsb
  have hT : 0 ≤ lifespan q b A := (lifespan_pos hb hA).le
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  refine ⟨G,hGm,hG,hGeq,?_,?_⟩
  · filter_upwards [hFA] with p hp
    rw [hGeq (0,p)]
    have ht : PositiveIntegral.time (lifespan q b A) 0 = 0 := GaussianLocal.time_eq ⟨le_rfl,hT⟩
    simp [PositiveIntegral.value,ht,JetBarrier.flight,clippedSlice,min_eq_left hp]
  · intro n
    apply solution_covariance hq hb hL hT (by positivity)
      (show (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A from le_rfl)
      (small hb hA) hGm hG hGeq
    intro p
    have hp := congrFun (hper n) (s,p)
    change F (s,shift (JetCopyDatum.displacement n) p) = F (s,p) at hp
    unfold clippedSlice
    rw [hp]

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

section

/-! # Extending a bounded positive periodic solution from a bounded time slice -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.WeightedLocalControl

theorem exists_continuation_step {q b A s : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hA : 0 < A) (hs : 0 ≤ s) {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ 2*A)
    (hFA : ∀ᵐ p ∂FlightMeasure.phaseVolume, F (s,p) ≤ A)
    (hfix : MildAE q b (damping q b A) s f₀ F)
    (hper : ∀ n, pull (JetCopyDatum.displacement n) F = F) :
    ∃ H : ℝ × JetPrototype.Phase → ℝ, Measurable H ∧
      (∀ u, 0 ≤ H u ∧ H u ≤ 2*A) ∧
      (∀ t, (fun p => H (t,p)) =ᵐ[FlightMeasure.phaseVolume]
        (fun p => PositiveIntegral.value (s+lifespan q b A) (damping q b A)
          JetBarrier.flight f₀ (forcing q b (damping q b A) H) (t,p))) ∧
      (∀ n, pull (JetCopyDatum.displacement n) H = H) ∧
      ∀ t ∈ Icc 0 s, ∀ p, H (t,p) = F (t,p) := by
  obtain ⟨G,hGm,hG,hGeq,_,hGper⟩ := exists_extension hq hb hA hFm
    (fun p => (hF (s,p)).1) hFA hper
  let P := paste s F G
  have hPm : Measurable P := measurable_paste hFm hGm
  have hPb (u) : 0 ≤ P u ∧ P u ≤ 2*A := paste_bounds hF hG u
  have hδ : 0 ≤ lifespan q b A := (lifespan_pos hb hA).le
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hsrc (u) : |forcing q b (damping q b A) P u| ≤ sourceBound q b A := by
    have h := HotRepresentative.source_bounds hq hb (by positivity : 0 ≤ 2*A)
      (show (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A from le_rfl)
      (GaussianLocal.measurable_state hPm) (fun v => hPb (v.1.1,(v.1.2,v.2)))
      ((u.1,u.2.1),u.2.2)
    exact (abs_of_nonneg h.1).trans_le h.2
  have hclip : clippedSlice A F s =ᵐ[FlightMeasure.phaseVolume] (fun p => F (s,p)) := by
    filter_upwards [hFA] with p hp
    exact min_eq_left hp
  have hPeq : MildAE q b (damping q b A) (s+lifespan q b A) f₀ P :=
    paste_mildAE hs hδ hL hFm hGm hsrc hfix (mildAE_of_pointwise hGeq) hclip
  have hPper (n) : pull (JetCopyDatum.displacement n) P = P := by
    dsimp only [P]
    rw [paste_pull,hper n,hGper n]
  let H := clampTime (s+lifespan q b A) P
  have htot := add_nonneg hs hδ
  refine ⟨H,measurable_clampTime hPm _,fun u => hPb _,mildAE_all_times htot hPeq,?_,?_⟩
  · intro n
    funext u
    exact congrFun (hPper n) (PositiveIntegral.time (s+lifespan q b A) u.1,u.2)
  · intro t ht p
    change P (PositiveIntegral.time (s+lifespan q b A) t,p) = F (t,p)
    rw [GaussianLocal.time_eq ⟨ht.1,by linarith [ht.2]⟩]
    exact ite_eq_left ht.2

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicSourceBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A cellwise velocity estimate gives a spacetime almost-everywhere bound -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem ae_bound_of_cell {T : ℝ} {k : ℝ × JetPrototype.Phase → ℝ} {w : ℝ → ℝ}
    (hkm : Measurable k) (hwm : Measurable w)
    (hperiodic : ∀ n, pull (displacement n) k = k)
    (hcell : ∀ t ∈ Ioc 0 T, ∀ x : Velocity, (∀ j, |x j| ≤ 1) →
      ∀ᵐ v : Velocity, k (t,(JetPeriodicDatum.spatialMap x,v)) ≤ w t) :
    ∀ᵐ u ∂WeightedLocal.spacetimeVolume, u.1 ∈ Ioc 0 T → k u ≤ w u.1 := by
  have hall (t : ℝ) (ht : t ∈ Ioc 0 T) (y : JetPrototype.Space) :
      ∀ᵐ v : Velocity, k (t,(y,v)) ≤ w t := by
    obtain ⟨n,x,hx,he⟩ := exists_shift_in_cell y
    filter_upwards [hcell t ht x hx] with v hv
    have hk := congrFun (hperiodic n) (t,(y,v))
    change k (t,(y-displacement n,v)) = k (t,(y,v)) at hk
    rw [he] at hk
    rwa [← hk]
  have hgood : MeasurableSet {u : ℝ × JetPrototype.Phase |
      u.1 ∈ Ioc 0 T → k u ≤ w u.1} := by
    simp only [imp_iff_not_or]
    exact (measurableSet_Ioc.preimage measurable_fst).compl.union
      (measurableSet_le hkm (hwm.comp measurable_fst))
  apply (ae_prod_iff_ae_ae hgood).mpr
  apply ae_of_all
  intro t
  have hslice : MeasurableSet {p : JetPrototype.Phase |
      t ∈ Ioc 0 T → k (t,p) ≤ w t} :=
    hgood.preimage (measurable_const.prodMk measurable_id)
  apply (ae_prod_iff_ae_ae hslice).mpr
  apply ae_of_all
  intro y
  by_cases ht : t ∈ Ioc 0 T
  · filter_upwards [hall t ht y] with v hv
    exact fun _ => hv
  · exact ae_of_all _ (fun _ h => (ht h).elim)

end BoltzmannNonuniqueness.JetCopyDatum

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

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A finite cold-norm bound from one core and the escaped tail -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem colorAmplitude_nonneg {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (α : ℝ) : 0 ≤ colorAmplitude K α s d := by
  unfold colorAmplitude JetGaussianEscape.constant VelocityWeight.tiltConstant
  have := JetThermalKernel.bound_pos
  positivity

theorem color_le_amplitude {K α γ s d t q c : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1/16) (ht : 0 < t) (htmax : t ≤ 1)
    (hε : JetSupersolution.epsilon K s d ≤ 1) (η : ℝ) (a : Bool) (x : Space) (v : Velocity)
    (hc : VelocityWeight.H q v*c ≤ JetSupersolution.U η K α γ s d t a (x,v)) :
    c ≤ colorAmplitude K α s d := by
  have hh := hc.trans (JetEnvelopeBound.U_le_H hK hα hγ hs hd hdmax ht htmax hε η q a x v)
  change VelocityWeight.H q v*c ≤ colorAmplitude K α s d*VelocityWeight.H q v at hh
  nlinarith [VelocityWeight.H_pos q v]

theorem cold_sum_le_of_core_bound {s₀ η t B e : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (htmax : t ≤ 1/32) (N : ℕ) (x : Velocity) (f : JetLattice.Label → Velocity → ℝ)
    (hfs : ∀ v, Summable (fun i => f i v))
    (hzero : ∀ i, ¬i.annulus < N → ∀ v, f i v = 0)
    (htail : ∀ v, (∑' i, escaped s₀ η t N x (fun j => f j v) i) ≤ e)
    (hcore : ∀ i : JetLattice.Label, i.annulus ≤ N → ∀ v, f i v ≤ B) :
    ∀ v, (∑' i, f i v) ≤ B+e := by
  let c (i : JetLattice.Label) (p : Unit × Velocity) := f i p.2
  obtain ⟨i,hi,hh⟩ := select_remainder hs₀ hsmax hη hηmax htmax N x ()
    (fun p : Unit × Velocity => ∑' j, c j p) c hfs hzero (fun _ => sub_self _ |>.le) htail
  intro v
  have h := hh v
  have hc := hcore i hi v
  change (∑' j, f j v)-f i v ≤ 0+e at h
  linarith

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A finite uniform-in-time norm bound for the retained cold family -/

noncomputable section

open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem finiteAmplitude_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K)
    (hd₀ : 0 < d₀) (η α : ℝ) (N : ℕ) : 0 ≤ finiteAmplitude s₀ η K α d₀ N := by
  apply Finset.sum_nonneg
  intro j _
  have hs : 0 < JetGeometry.jetScale s₀ η j := DatumBounds.scale_pos hs₀ _
  exact colorAmplitude_nonneg hK hs (by positivity) α

theorem amplitude_le_finite {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K)
    (hd₀ : 0 < d₀) (η α : ℝ) {N j : ℕ} (hj : j ≤ N) :
    colorAmplitude K α (JetGeometry.jetScale s₀ η j) (d₀*JetGeometry.jetScale s₀ η j^10) ≤
      finiteAmplitude s₀ η K α d₀ N := by
  unfold finiteAmplitude
  apply Finset.single_le_sum (s := Finset.range (N+1)) (a := j)
    (f := fun i => colorAmplitude K α (JetGeometry.jetScale s₀ η i)
      (d₀*JetGeometry.jetScale s₀ η i^10))
  · intro i _
    have hs : 0 < JetGeometry.jetScale s₀ η i := DatumBounds.scale_pos hs₀ _
    exact colorAmplitude_nonneg hK hs (by positivity) α
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)

theorem cell_cold_sum_bound {s₀ η K α γ d₀ q t : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (ht : 0 < t) (htmax : t ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (N : ℕ) (x : Velocity) (hx : ∀ k, |x k| ≤ 1)
    (f : JetLattice.Label → Velocity → ℝ) (hfn : ∀ i v, 0 ≤ f i v)
    (hfs : ∀ v, Summable (fun i => f i v))
    (hzero : ∀ i, ¬i.annulus < N → ∀ v, f i v = 0)
    (hU : ∀ i v, VelocityWeight.H q v*f i v ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,v)) :
    ∀ v, (∑' i, f i v) ≤ finiteAmplitude s₀ η K α d₀ N+
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 0) := by
  apply cold_sum_le_of_core_bound hs₀ hsmax hη hηmax htmax N x f hfs hzero
  · intro v
    have h := normalized_escaped_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      ht htmax hsmall 0 q N (fun i => f i v) x v hx (fun i => hfn i v) (hfs v)
      (fun i _ => hU i v)
    simpa only [Real.rpow_zero,mul_one] using h
  · intro i hi v
    have hs : 0 < JetGeometry.jetScale s₀ η i.annulus := DatumBounds.scale_pos hs₀ _
    have hss := JetEscapedTotal.scale_bound hs₀ hη i.annulus
    have hd : 0 < d₀*JetGeometry.jetScale s₀ η i.annulus^10 := by positivity
    have hdmax : d₀*JetGeometry.jetScale s₀ η i.annulus^10 ≤ 1/16 := by
      calc
        _ ≤ 1*(1/8:ℝ)^10 := mul_le_mul hd₀max
          (pow_le_pow_left₀ hs.le (hss.trans hsmax) 10) (pow_nonneg hs.le _) (by norm_num)
        _ ≤ 1/16 := by norm_num
    have he := JetEscapedEnvelope.epsilon_small hK hd₀.le hs hss hsmall
    exact (color_le_amplitude hK hα hγ hs hd hdmax ht (htmax.trans (by norm_num)) he η i.positive
      (JetSpatialBox.shifted x i.lattice) v (hU i v)).trans
        (amplitude_le_finite hs₀ hK hd₀ η α hi)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A fixed-truncation bound for the full periodic cold sum -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem coldNormBound_nonneg {s₀ K d₀ : ℝ} (hs₀ : 0 < s₀) (hK : 0 ≤ K)
    (hd₀ : 0 < d₀) (η α : ℝ) (N : ℕ) : 0 ≤ coldNormBound s₀ η K α d₀ N :=
  add_nonneg (finiteAmplitude_nonneg hs₀ hK hd₀ η α N)
    (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _)

end BoltzmannNonuniqueness.JetCopyDatum

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

theorem rebuilt_shift {s₀ η K α γ d₀ q b L T : ℝ} {N : ℕ}
    {F : ℝ × JetPrototype.Phase → ℝ} (n : JetLattice.Lattice)
    (hF : pull (displacement n) F = F) (i : JetLattice.Label) :
    pull (displacement n) (rebuilt s₀ η K α γ d₀ q b L T N F i) =
      rebuilt s₀ η K α γ d₀ q b L T N F (relabel n i) := by
  unfold rebuilt
  rw [← rebuiltColdFamily_pull,hF]
  have hc : (fun j p => color s₀ η K α γ d₀ q N j (shift (displacement n) p)) =
      (fun j => color s₀ η K α γ d₀ q N (relabel n j)) := by
    funext j p
    exact color_shift s₀ η K α γ d₀ q N n j p
  rw [hc,rebuiltColdFamily_reindex]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The geometric hot-source estimate in polynomial comparison form -/

noncomputable section

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem scalarMajorant_eq_source (s₀ η K α γ d₀ q : ℝ) (N m : ℕ) {t : ℝ}
    (ht : 0 < t) (z : ℝ) :
    scalarMajorant s₀ η K α γ d₀ q (m+1 : ℕ) N t z =
      ZeroProfile.source (2*JetMainGain.coefficient K α γ q) (2*HotApplication.realBound q)
        ((2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
          JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ)))
        (JetGeometry.jetScale s₀ η N) m t z := by
  unfold scalarMajorant ZeroProfile.source
  rw [Real.rpow_natCast,pow_succ t m,add_comm (JetGeometry.jetScale s₀ η N) t]
  have he (E : ℝ) : E*(t^m*t)/t = E*t^m := by
    field_simp [ne_of_gt ht]
  rw [he]
  ring

theorem tail_small {E T t : ℝ} {m : ℕ} (hE : 0 ≤ E) (ht : 0 ≤ t) (htT : t ≤ T)
    (hT : E*T^(m+1) ≤ 1) : E*t^(m+1) ≤ 1 :=
  (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht htT (m+1)) hE).trans hT

end BoltzmannNonuniqueness.JetCopyDatum

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

theorem exists_extension {q b A T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b (damping q b A) T (2*A) f₀)
    (hq : q < 2) (hb : 0 ≤ b) (hA : 0 < A) (hT : 0 ≤ T)
    (hFA : ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (T,p) ≤ A) :
    Nonempty (PeriodicMildState q b (damping q b A) (T+lifespan q b A) (2*A) f₀) := by
  obtain ⟨G,hGm,hG,hGeq,hGper,_⟩ := exists_continuation_step hq hb hA hT
    F.measurable_value F.value_bounds hFA F.mild F.periodic
  have htotal : 0 ≤ T+lifespan q b A := add_nonneg hT (lifespan_pos (q := q) hb hA).le
  refine ⟨⟨clampTime (T+lifespan q b A) G,measurable_clampTime hGm _,
    fun u => hG _,?_,clampTime_idempotent htotal G,?_⟩⟩
  · exact fun t _ => mildAE_all_times htotal (fun r _ => hGeq r) t
  · intro n
    funext u
    exact congrFun (hGper n) (PositiveIntegral.time (T+lifespan q b A) u.1,u.2)

end PeriodicMildState

theorem exists_to_time_of_apriori {q b A τ : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hA : 0 < A) (hτ : 0 ≤ τ) {f₀ : JetPrototype.Phase → ℝ}
    (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ A)
    (hper : ∀ n p, f₀ (shift (JetCopyDatum.displacement n) p) = f₀ p)
    (hapriori : ∀ T, 0 ≤ T → T ≤ τ →
      ∀ F : PeriodicMildState q b (damping q b A) T (2*A) f₀,
        ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (T,p) ≤ A) :
    Nonempty (PeriodicMildState q b (damping q b A) τ (2*A) f₀) := by
  let δ := lifespan q b A
  have hδ : 0 < δ := lifespan_pos hb hA
  have hex : ∀ n : ℕ, Nonempty (PeriodicMildState q b (damping q b A)
      (min ((n:ℝ)*δ) τ) (2*A) f₀) := by
    intro n
    induction n with
    | zero =>
      simpa only [Nat.cast_zero,zero_mul,min_eq_left hτ] using
        (show Nonempty (PeriodicMildState q b (damping q b A) 0 (2*A) f₀) from
          ⟨PeriodicMildState.initial hA.le hf₀m hf₀ hper⟩)
    | succ n ih =>
      have hn : 0 ≤ (n:ℝ)*δ := mul_nonneg (Nat.cast_nonneg n) hδ.le
      by_cases hstop : τ ≤ (n:ℝ)*δ
      · have hnext : τ ≤ ((n+1:ℕ):ℝ)*δ := by
          rw [Nat.cast_add,Nat.cast_one]
          nlinarith
        rw [min_eq_right hnext,min_eq_right hstop] at *
        exact ih
      · obtain ⟨F⟩ := ih
        have hS : 0 ≤ min ((n:ℝ)*δ) τ := le_min hn hτ
        obtain ⟨G⟩ := F.exists_extension hq hb hA hS
          (hapriori _ hS (min_le_right _ _) F)
        have hnew : 0 ≤ min (((n+1:ℕ):ℝ)*δ) τ :=
          le_min (mul_nonneg (Nat.cast_nonneg _) hδ.le) hτ
        have hle : min (((n+1:ℕ):ℝ)*δ) τ ≤ min ((n:ℝ)*δ) τ+δ := by
          rw [min_eq_left (le_of_not_ge hstop)]
          calc
            _ ≤ (((n+1:ℕ):ℝ)*δ) := min_le_left _ _
            _ = (n:ℝ)*δ+δ := by rw [Nat.cast_add,Nat.cast_one]; ring
        exact ⟨G.restrict hnew hle⟩
  obtain ⟨n,hn⟩ := exists_nat_ge (τ/δ)
  have hreach : τ ≤ (n:ℝ)*δ := (div_le_iff₀ hδ).mp hn
  simpa only [min_eq_right hreach] using hex n

end BoltzmannNonuniqueness.WeightedLocalControl

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricColdSource
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The uniform source estimate for a dominated geometric cold family -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem geometric_family_source (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q b L t R z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (ht : 0 < t) (htmax : t ≤ 1/32) (hz : 0 ≤ z)
    (A : ℝ) (N : ℕ) (x : Velocity) (hx : ∀ k, |x k| ≤ 1)
    {G : ℝ × JetPrototype.Phase → ℝ} {c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ}
    (hGm : Measurable G) (hcm : ∀ i, Measurable (c i))
    (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R) (hc : ∀ i u, 0 ≤ c i u ∧ c i u ≤ R)
    (hSum : ∀ s : Finset JetLattice.Label, ∀ u, ∑ i ∈ s, c i u ≤ G u)
    (hzero : ∀ i, ¬i.annulus < N → c i = 0)
    (hhot : ∀ w, G (t,(JetPeriodicDatum.spatialMap x,w))-
      ∑' i, c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤ z)
    (hU : ∀ i w, VelocityWeight.H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
        (JetSpatialBox.shifted x i.lattice,w))
    (he : JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A ≤ 1) :
    ∀ᵐ v : Velocity, remainderForcing q b L G c (t,(JetPeriodicDatum.spatialMap x,v))-
        L*(G (t,(JetPeriodicDatum.spatialMap x,v))-
          ∑' i, c i (t,(JetPeriodicDatum.spatialMap x,v))) ≤
      (2*JetMainGain.coefficient K α γ q/(JetGeometry.jetScale s₀ η N+t))*z+
        2*HotApplication.realBound q*z^2+
        (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
          ((JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A)/t) := by
  let e := JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A
  have htail (w) : (∑' i, escaped s₀ η t N x
      (fun j => c j (t,(JetPeriodicDatum.spatialMap x,w))) i) ≤ e :=
    normalized_escaped_bound hs₀ hsmax hη hηmax hK hα.le hαmax hγ.le hd₀ hd₀max ht htmax hsmall A q N
      (fun j => c j (t,(JetPeriodicDatum.spatialMap x,w))) x w hx
      (fun i => (hc i _).1)
      (summable_of_sum_le (fun i => (hc i _).1) (fun s => hSum s _)) (fun i _ => hU i w)
  have he0 : 0 ≤ e := mul_nonneg
    (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α (JetEscapedEnvelope.exponent A))
    (Real.rpow_nonneg ht.le A)
  exact uniform_hot_source_q80 hcarleman hs₀ hsmax hη hηmax hK hα hγ hd₀ hd₀max hq₁ hq₂ ht htmax hz he0 he
    N x (t,JetPeriodicDatum.spatialMap x) (GaussianLocal.measurable_state hGm)
    (fun i => GaussianLocal.measurable_state (hcm i))
    (fun u => hG (u.1.1,(u.1.2,u.2))) (fun i u => hc i (u.1.1,(u.1.2,u.2)))
    (fun s u => hSum s (u.1.1,(u.1.2,u.2)))
    (fun i hi w => congrFun (hzero i hi) (t,(JetPeriodicDatum.spatialMap x,w))) hhot htail hU b L

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform-in-time bounds for a periodic geometric cold family -/

noncomputable section

open Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem geometric_cold_sum_bound {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hTmax : T ≤ 1/32)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (N : ℕ)
    {c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ}
    (hcn : ∀ i u, 0 ≤ c i u) (hcs : ∀ u, Summable (fun i => c i u))
    (hzero : ∀ i, ¬i.annulus < N → c i = 0)
    (hU : ∀ t ∈ Ioc 0 T, ∀ i (x w : Velocity),
      VelocityWeight.H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
        JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
          (JetSpatialBox.shifted x i.lattice,w))
    (hcperiodic : ∀ n i, pull (displacement n) (c i) = c (relabel n i)) :
    ∀ t ∈ Ioc 0 T, ∀ p : JetPrototype.Phase, (∑' i, c i (t,p)) ≤ coldNormBound s₀ η K α d₀ N := by
  intro t ht p
  obtain ⟨n,x,hx,he⟩ := exists_shift_in_cell p.1
  have hp : shift (displacement n) p = (JetPeriodicDatum.spatialMap x,p.2) := Prod.ext he rfl
  have hbound := cell_cold_sum_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    ht.1 (ht.2.trans hTmax) hsmall N x hx
    (fun i v => c i (t,(JetPeriodicDatum.spatialMap x,v)))
    (fun i v => hcn i (t,(JetPeriodicDatum.spatialMap x,v)))
    (fun v => hcs (t,(JetPeriodicDatum.spatialMap x,v)))
    (fun i hi v => congrFun (hzero i hi) (t,(JetPeriodicDatum.spatialMap x,v)))
    (fun i v => hU t ht i x v) p.2
  have hshift := family_sum_pull (displacement n) (relabel n) (hcperiodic n) (t,p)
  rw [hp] at hshift
  rw [← hshift]
  exact hbound

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Essential-norm source control for reconstructed geometric cold families -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem geometric_hot_norm_source (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q b L T R : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hL : 0 ≤ L) (hTmax : T ≤ 1/32)
    (A : ℝ) (N : ℕ)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : JetLattice.Label → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hcn : ∀ i u, 0 ≤ c i u)
    (hSum : ∀ s : Finset JetLattice.Label, ∀ u, ∑ i ∈ s, c i u ≤ F u)
    (hzero : ∀ i, ¬i.annulus < N → c i = 0)
    (hU : ∀ t ∈ Ioc 0 T, ∀ i (x w : Velocity),
      VelocityWeight.H q w*c i (t,(JetPeriodicDatum.spatialMap x,w)) ≤
        JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
          (JetSpatialBox.shifted x i.lattice,w))
    (hperiodic : ∀ n, pull (displacement n) F = F)
    (hcperiodic : ∀ n i, pull (displacement n) (c i) = c (relabel n i))
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p))))
    (he : ∀ t ∈ Ioc 0 T,
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent A)*t^A ≤ 1) :
    ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → remainderForcing q b L F c u ≤
      scalarMajorant s₀ η K α γ d₀ q A N u.1
        (PhaseEssSup.size (fun p => F (u.1,p)-∑' i, c i (u.1,p)))+
        L*PhaseEssSup.size (fun p => F (u.1,p)-∑' i, c i (u.1,p)) := by
  classical
  let G := HotCanonical.familyReplacement F c
  let z (t : ℝ) := PhaseEssSup.size (fun p => F (t,p)-∑' i, c i (t,p))
  let w (t : ℝ) := scalarMajorant s₀ η K α γ d₀ q A N t (z t)
  let k (u : ℝ × JetPrototype.Phase) := remainderForcing q b L G c u-L*(G u-∑' i, c i u)
  have hcb (i) (u) : 0 ≤ c i u ∧ c i u ≤ R := by
    refine ⟨hcn i u,?_⟩
    simpa only [Finset.sum_singleton] using (hSum {i} u).trans (hF u).2
  have hcs (u) : Summable (fun i => c i u) := summable_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hcF (u) : (∑' i, c i u) ≤ F u := Real.tsum_le_of_sum_le (fun i => hcn i u) (fun s => hSum s u)
  have hg := HotCanonical.family_properties hFm hcm (fun u => (hF u).2) hcn hcs hcF hnorm
  have hGp (n) : pull (displacement n) G = G :=
    familyReplacement_pull (displacement n) (relabel n) (hperiodic n) (hcperiodic n)
  have hkp (n) : pull (displacement n) k = k := by
    have hr : pull (displacement n) (remainderForcing q b L G c) = remainderForcing q b L G c :=
      remainderForcing_pull q b L (displacement n) (relabel n) (hGp n) (hcperiodic n)
    funext u
    have hsum := family_sum_pull (displacement n) (relabel n) (hcperiodic n) u
    change remainderForcing q b L G c (u.1,shift (displacement n) u.2)-
      L*(G (u.1,shift (displacement n) u.2)-_) = remainderForcing q b L G c u-L*(G u-_)
    rw [show remainderForcing q b L G c (u.1,shift (displacement n) u.2) =
      remainderForcing q b L G c u from congrFun hr u,
      show G (u.1,shift (displacement n) u.2) = G u from congrFun (hGp n) u,hsum]
  have hkm : Measurable k := ((measurable_forcing hg.1 q b L).sub
    (Measurable.tsum (fun i => measurable_coldForcing hg.1 (hcm i) q b L))).sub
      ((hg.1.sub (Measurable.tsum hcm)).const_mul L)
  have hwm : Measurable w := by
    have hzm : Measurable z := hnorm
    unfold w scalarMajorant
    fun_prop
  have hbound : ∀ᵐ u ∂spacetimeVolume, u.1 ∈ Ioc 0 T → k u ≤ w u.1 := by
    apply ae_bound_of_cell hkm hwm hkp
    intro t ht x hx
    exact geometric_family_source hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hsmall hq₁ hq₂ ht.1 (ht.2.trans hTmax) (PhaseEssSup.size_nonneg _) A N x hx
      hg.1 hcm hg.2.1 hcb hg.2.2.1 hzero
      (fun v => hg.2.2.2.1 (t,(JetPeriodicDatum.spatialMap x,v))) (fun i v => hU t ht i x v) (he t ht)
  have hcongr := remainderForcing_congr hg.2.2.2.2 q b L c
  filter_upwards [hbound,hcongr,hg.2.2.2.2] with u hu hcu hgu hut
  change G u = F u at hgu
  change remainderForcing q b L G c u = remainderForcing q b L F c u at hcu
  have hh := hg.2.2.2.1 u
  have hbnd := hu hut
  change G u-∑' i, c i u ≤ z u.1 at hh
  change remainderForcing q b L G c u-L*(G u-∑' i, c i u) ≤ w u.1 at hbnd
  rw [hgu] at hh hbnd
  rw [hcu] at hbnd
  have hmul := mul_le_mul_of_nonneg_left hh hL
  change remainderForcing q b L F c u ≤ w u.1+L*z u.1
  linarith

end BoltzmannNonuniqueness.JetCopyDatum

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

/-! # Total norm control for a reconstructed geometric decomposition -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_total_norm_le {s₀ η K α γ d₀ q b L T R Z : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (N : ℕ) {h₀ : JetPrototype.Phase → ℝ} (hh₀ : ∀ p, 0 ≤ h₀ p)
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N h₀ p ≤ R)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight
        (initial s₀ η K α γ d₀ q N h₀) (forcing q b L F) (t,p)))
    (hper : ∀ n, pull (displacement n) F = F) {t : ℝ} (ht : t ∈ Ioc 0 T)
    (hz : PhaseEssSup.size (fun p => F (t,p)-∑' i, rebuilt s₀ η K α γ d₀ q b L T N F i (t,p)) ≤ Z) :
    PhaseEssSup.size (fun p => F (t,p)) ≤ coldNormBound s₀ η K α d₀ N+Z := by
  let c := rebuilt s₀ η K α γ d₀ q b L T N F
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N hh₀
  have hcb (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧ color s₀ η K α γ d₀ q N i p ≤ R :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (hF₀ p)⟩
  have hp := rebuiltColdFamily_properties hq hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hcb hi.2 hFeq
  have hcn (i) (u) : 0 ≤ c i u := (hp.2.1 i u).1
  have hbound : ∀ p : JetPrototype.Phase, (∑' i, c i (t,p)) ≤ coldNormBound s₀ η K α d₀ N :=
    geometric_cold_sum_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hTmax hsmall N
      hcn (fun u => (hp.2.2.2.1 u).1)
      (rebuilt_zero s₀ η K α γ d₀ q b L T N (fun u => (hF u).1))
      (fun r hr i x w => rebuilt_envelope_q80 hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq hb hL hT hR
        (hTmax.trans (by norm_num)) hloss N hh₀ hFm hF hF₀ i hr (JetPeriodicDatum.spatialMap x,w))
      (fun n i => rebuilt_shift n (hper n) i) t ht
  exact PhaseEssSup.size_le_cold_add_hot
    (hFm.comp (measurable_const.prodMk measurable_id))
    ((Measurable.tsum hp.1).comp (measurable_const.prodMk measurable_id))
    (coldNormBound_nonneg hs₀ hK hd₀ η α N) (fun p => hF (t,p))
    (fun p => ⟨tsum_nonneg (fun i => hcn i (t,p)),(hp.2.2.2.1 (t,p)).2⟩) hbound hz

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Uniform zero-hot control after a.e. pasting and cold reconstruction -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem rebuilt_zero_hot_bound (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q b L T R D : ℝ} (m : ℕ)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (hR : 0 ≤ R) (hTmax : T ≤ 1/32) (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hD : 0 ≤ D)
    (hBD : (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ)) ≤ D)
    (hquad : (2*HotApplication.realBound q)*D*T ≤ 1)
    (hm : 2*JetMainGain.coefficient K α γ q+2 ≤ (m+1 : ℕ))
    (htail : JetEscapedEnvelope.constant s₀ η α K d₀
      (JetEscapedEnvelope.exponent (m+1 : ℕ))*T^(m+1) ≤ 1)
    (N : ℕ) {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R)
    (hF₀ : ∀ p, initial s₀ η K α γ d₀ q N (fun _ => 0) p ≤ R)
    (hFeq : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight
        (initial s₀ η K α γ d₀ q N (fun _ => 0)) (forcing q b L F) (t,p)))
    (hclamp : ∀ u, F (PositiveIntegral.time T u.1,u.2) = F u)
    (hperiodic : ∀ n, pull (displacement n) F = F) :
    ∀ t ∈ Icc 0 T, PhaseEssSup.size (fun p =>
      F (t,p)-∑' i, rebuilt s₀ η K α γ d₀ q b L T N F i (t,p)) ≤ D*t^(m+1) := by
  let c := rebuilt s₀ η K α γ d₀ q b L T N F
  let h (u : ℝ × JetPrototype.Phase) := F u-∑' i, c i u
  let g := remainderForcing q b L F c
  let S := HotApplication.realBound q*R^2+L*R
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀.le α γ q N
    (fun _ => le_rfl : ∀ _ : JetPrototype.Phase, (0:ℝ) ≤ 0)
  have hcb (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧ color s₀ η K α γ d₀ q N i p ≤ R :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (hF₀ p)⟩
  have hp := rebuiltColdFamily_properties hq₂ hb hL hT hR hloss hFm
    (measurable_color s₀ η K α γ d₀ q N) hF hcb hi.2 hFeq
  have hcm (i) : Measurable (c i) := hp.1 i
  have hcn (i) (u) : 0 ≤ c i u := (hp.2.1 i u).1
  have hsum (s : Finset JetLattice.Label) (u) : ∑ i ∈ s, c i u ≤ F u := hp.2.2.1 s u
  have hr := family_hot_bounds hq₂ hb hR hloss hFm hcm hF hcn hsum
  have hgain : 0 < HotApplication.realBound q := HotApplication.realBound_pos q
  have hS : 0 ≤ S := by dsimp [S] <;> positivity
  have hge (u) : 0 ≤ g u ∧ g u ≤ S := hr.2.2.2 u
  have hga (u) : |g u| ≤ S := by rw [abs_of_nonneg (hge u).1]; exact (hge u).2
  have hhe : ∀ t ∈ Icc 0 T, (fun p => h (t,p)) =ᵐ[FlightMeasure.phaseVolume]
      (fun p => PositiveIntegral.value T L JetBarrier.flight (fun _ => 0) g (t,p)) := by
    have hh := family_hot_mildAE hq₂ hb hL hT hR hloss hFm hcm hF hcn hsum
      (fun i p => (hi.1 i p).1) hi.2 (fun t _ => hFeq t) hp.2.2.2.2
    simpa only [initial,seed,add_zero,sub_self] using hh
  have hhc (u : ℝ × JetPrototype.Phase) : h (PositiveIntegral.time T u.1,u.2) = h u := by
    dsimp only [h]
    rw [hclamp u]
    congr 1
    apply tsum_congr
    intro i
    exact rebuiltColdFamily_time_clamp hT q b L hclamp _ i u
  have hnorm : Continuous (fun t => PhaseEssSup.size (fun p => h (t,p))) :=
    PhaseEssSup.continuous_size_of_mildAE hT hL (le_rfl : (0:ℝ) ≤ 0) hS
      measurable_const hr.2.2.1 (fun _ => ⟨le_rfl,le_rfl⟩) hge
      (mild_all_of_time_clamp hT L hhc hhe)
  have hE := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α
    (JetEscapedEnvelope.exponent (m+1 : ℕ))
  have hsource := geometric_hot_norm_source (b := b) hcarleman hs₀ hsmax hη hηmax hK hα hαmax hγ
    hd₀ hd₀max hsmall hq₁ hq₂ hL hTmax (m+1 : ℕ) N hFm hcm hF hcn hsum
    (rebuilt_zero s₀ η K α γ d₀ q b L T N (fun u => (hF u).1))
    (fun t ht i x w => rebuilt_envelope_q80 hs₀ hsmax hη hηmax hK hα.le hγ.le hd₀ hsmall hq₂ hb
      hL hT hR (hTmax.trans (by norm_num)) hloss N (fun _ => le_rfl) hFm hF hF₀ i ht
        (JetPeriodicDatum.spatialMap x,w))
    hperiodic (fun n i => rebuilt_shift n (hperiodic n) i) hnorm.measurable (by
      intro t ht
      rw [Real.rpow_natCast]
      exact tail_small hE ht.1.le ht.2 htail)
  have hM : 0 ≤ 2*JetMainGain.coefficient K α γ q :=
    mul_nonneg (by norm_num) (JetMainGain.coefficient_nonneg hK α γ q)
  have hC : 0 ≤ 2*HotApplication.realBound q := mul_nonneg (by norm_num) hgain.le
  have hB : 0 ≤ (2*JetMainGain.coefficient K α γ q+2*HotApplication.realBound q)*
      JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent (m+1 : ℕ)) :=
    mul_nonneg (add_nonneg hM hC) hE
  apply PhaseEssSup.zero_seed_bound_ae hT (hTmax.trans (by norm_num)) hL hR hM hC hB hBD hD
    (DatumBounds.scale_pos hs₀ (N+1)) hquad hm hr.2.2.1 hr.1 hga hr.2.1 hnorm.continuousOn
    (ae_of_all _ (fun _ => le_rfl)) hhe
  filter_upwards [hsource] with u hu ht
  have hh := hu ht
  rw [scalarMajorant_eq_source s₀ η K α γ d₀ q N m ht.1] at hh
  exact hh

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A time independent of the truncation controls every zero-seed local solution -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_uniform_rebuilt_zero_control (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/32 ∧
      ∀ (N : ℕ) (b L T R : ℝ), 0 ≤ b → 0 ≤ L → 0 ≤ T → T ≤ τ → 0 ≤ R →
        R*CutoffLipschitz.frequencyConstant q b ≤ L →
        ∀ F : ℝ × JetPrototype.Phase → ℝ, Measurable F →
          (∀ u, 0 ≤ F u ∧ F u ≤ R) →
          (∀ p, initial s₀ η K α γ d₀ q N (fun _ => 0) p ≤ R) →
          (∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
            (fun p => PositiveIntegral.value T L JetBarrier.flight
              (initial s₀ η K α γ d₀ q N (fun _ => 0)) (forcing q b L F) (t,p))) →
          (∀ u, F (PositiveIntegral.time T u.1,u.2) = F u) →
          (∀ n, pull (displacement n) F = F) →
          ∀ t ∈ Icc 0 T, PhaseEssSup.size (fun p =>
            F (t,p)-∑' i, rebuilt s₀ η K α γ d₀ q b L T N F i (t,p)) ≤ t^2 := by
  let M := 2*JetMainGain.coefficient K α γ q
  let C := 2*HotApplication.realBound q
  let E (m : ℕ) := JetEscapedEnvelope.constant s₀ η α K d₀
    (JetEscapedEnvelope.exponent (m+1 : ℕ))
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (JetMainGain.coefficient_nonneg hK α γ q)
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (HotApplication.realBound_pos q).le
  have hE (m : ℕ) : 0 ≤ E m := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _
  obtain ⟨m,D,τ,hm₂,hD,hτ,hτmax,hm,hBD,hquad,htail,hDτ⟩ :=
    ZeroProfile.parameters_exist hM hC E hE
  refine ⟨τ,hτ,hτmax,?_⟩
  intro N b L T R hb hL hT hTτ hR hloss F hFm hF hF₀ hFeq hclamp hperiodic t ht
  have hquadT : C*D*T ≤ 1 :=
    (mul_le_mul_of_nonneg_left hTτ (mul_nonneg hC hD.le)).trans hquad
  have htailT : E m*T^(m+1) ≤ 1 :=
    tail_small (hE m) hT hTτ htail
  have hz := rebuilt_zero_hot_bound hcarleman m hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq₁ hq₂ hb hL hT hR (hTτ.trans hτmax) hloss hD.le hBD hquadT hm htailT N
    hFm hF hF₀ hFeq hclamp hperiodic t ht
  exact hz.trans (ZeroProfile.profile_le_square hD.le
    ((hTτ.trans hτmax).trans (by norm_num))
    ((mul_le_mul_of_nonneg_left hTτ hD.le).trans hDτ) hm₂ ht)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Zero-hot construction with any sufficiently large common amplitude -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedTranslation

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_uniform_zero_solution_large_q80_oai (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1/32 ∧ ∀ (N : ℕ) (b A T : ℝ), 0 ≤ b →
      continuationAmplitude s₀ η K α d₀ N ≤ A → 0 ≤ T → T ≤ τ →
      ∃ F : PeriodicMildState q b (damping q b A)
        T (2*A) (initial s₀ η K α γ d₀ q N (fun _ => 0)),
        ∀ t ∈ Icc 0 T, PhaseEssSup.size (fun p => F.value (t,p)-
          ∑' i, rebuilt s₀ η K α γ d₀ q b (damping q b A)
            T N F.value i (t,p)) ≤ t^2 := by
  have hαone : α ≤ 1 := hαmax.trans (by norm_num)
  obtain ⟨τ,hτ,hτmax,hcontrol⟩ := exists_uniform_rebuilt_zero_control hcarleman hs₀ hsmax hη hηmax
    hK hα hαone hγ hd₀ hd₀max hsmall hq₁ hq₂
  refine ⟨τ,hτ,hτmax,?_⟩
  intro N b A T hb hAle hT hTτ
  let f₀ := initial s₀ η K α γ d₀ q N (fun _ => 0)
  have hamp : 0 < WeightedFiniteSeed.amplitude s₀ η K d₀ N :=
    WeightedFiniteSeed.amplitude_pos hs₀ hK hd₀.le η N
  have hcold : 0 ≤ coldNormBound s₀ η K α d₀ N := coldNormBound_nonneg hs₀ hK hd₀ η α N
  have hA : 0 < A := by
    unfold continuationAmplitude at hAle
    linarith
  have hR : 0 ≤ 2*A := by positivity
  have hL : 0 ≤ damping q b A := (bounds hb hA).1
  have hloss : (2*A)*CutoffLipschitz.frequencyConstant q b ≤ damping q b A := le_rfl
  have hf₀m : Measurable f₀ := (measurable_seed s₀ η K α γ d₀ q N).add measurable_const
  have hf₀ (p) : 0 ≤ f₀ p ∧ f₀ p ≤ A := by
    have h := seed_bounds hs₀ hsmax hη hηmax hK hd₀ hwidth hα.le hαmax γ q N p
    constructor
    · simpa only [f₀,initial,add_zero] using h.1
    · change seed s₀ η K α γ d₀ q N p+0 ≤ A
      unfold continuationAmplitude at hAle
      linarith [h.2]
  have hf₀R (p) : f₀ p ≤ 2*A := (hf₀ p).2.trans (by linarith)
  have hfper (n) (p) : f₀ (shift (displacement n) p) = f₀ p := by
    simp only [f₀,initial,add_zero,seed_periodic]
  have hapriori (S : ℝ) (hS : 0 ≤ S) (hST : S ≤ T)
      (F : PeriodicMildState q b (damping q b A) S (2*A) f₀) :
      ∀ᵐ p ∂FlightMeasure.phaseVolume, F.value (S,p) ≤ A := by
    have hSτ : S ≤ τ := hST.trans hTτ
    by_cases hTzero : S = 0
    · subst S
      filter_upwards [F.mild 0 ⟨le_rfl,le_rfl⟩] with p hp
      have he : PositiveIntegral.value 0 (damping q b A) JetBarrier.flight f₀
          (forcing q b (damping q b A) F.value) (0,p) = f₀ p := by
        simp [PositiveIntegral.value,PositiveIntegral.time,JetBarrier.flight]
      rw [he] at hp
      exact hp.le.trans (hf₀ p).2
    · have hTpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hTzero)
      have hz := hcontrol N b (damping q b A) S (2*A) hb hL hS hSτ hR hloss
        F.value F.measurable_value F.value_bounds hf₀R (F.all_mild hS) F.clamped F.periodic S ⟨hS,le_rfl⟩
      have hn := rebuilt_total_norm_le hs₀ hsmax hη hηmax hK hα.le hαone hγ.le hd₀ hd₀max hsmall
        hq₂ hb hL hS hR (hSτ.trans hτmax) hloss N (fun _ => le_rfl) F.measurable_value
        F.value_bounds hf₀R (F.all_mild hS) F.periodic ⟨hTpos,le_rfl⟩ hz
      have hnA : PhaseEssSup.size (fun p => F.value (S,p)) ≤ A := by
        have ht1 : S ≤ 1 := (hSτ.trans hτmax).trans (by norm_num)
        unfold continuationAmplitude at hAle
        nlinarith [sq_nonneg S]
      have hae := PhaseEssSup.ae_abs_le_size
        (F.measurable_value.comp (measurable_const.prodMk measurable_id))
        (fun p => show |F.value (S,p)| ≤ 2*A from by
          rw [abs_of_nonneg (F.value_bounds (S,p)).1]
          exact (F.value_bounds (S,p)).2)
      filter_upwards [hae] with p hp
      exact (le_abs_self _).trans (hp.trans hnA)
  obtain ⟨F⟩ := exists_to_time_of_apriori hq₂ hb hA hT hf₀m hf₀ hfper hapriori
  refine ⟨F,?_⟩
  exact hcontrol N b (damping q b A) T (2*A) hb hL hT hTτ hR hloss
    F.value F.measurable_value F.value_bounds hf₀R (F.all_mild hT) F.clamped F.periodic

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_zero_solution_large_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_uniform_zero_solution_large_q80_oai
