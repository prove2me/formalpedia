-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_away_axis_weak_limit_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:54:43.670731+00:00
-- url     : https://prove2.me/submissions/4f2a5dcb-b345-4003-8190-62b14b59860c

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotLimitExtraction_coldLabel_average_free_L1_limit_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotLimitExtraction_cold_mesh_average_L1_limit_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotLimitExtraction_eventually_coldLabelAverage_bound_q80

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

theorem J_integrable : Integrable J := bump.integrable_normed

theorem J_integral : ∫ v, J v = 1 := bump.integral_normed

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

/-! # Dilated annular margins vanish away from the limiting interfaces -/

noncomputable section

open Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem mem_annularCore_dilation {r : ℝ} (hr : 0 < r) (η s : ℝ) (y : Transverse) :
    r • y ∈ annularCore η (r*s) ↔
      s+gapCoefficient η*r*s^2 < ‖y‖ ∧ ‖y‖ < Real.exp η*s-gapCoefficient η*r*s^2 := by
  change r*s+gapCoefficient η*(r*s)^2 < ‖r • y‖ ∧
    ‖r • y‖ < Real.exp η*(r*s)-gapCoefficient η*(r*s)^2 ↔ _
  rw [norm_smul,Real.norm_of_nonneg hr.le]
  rw [show r*s+gapCoefficient η*(r*s)^2 = r*(s+gapCoefficient η*r*s^2) by ring,
    show Real.exp η*(r*s)-gapCoefficient η*(r*s)^2 =
      r*(Real.exp η*s-gapCoefficient η*r*s^2) by ring]
  simp only [mul_lt_mul_iff_right₀ hr]

theorem eventually_annularCore_dilation {r s d : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    (η t : ℝ) (y w : Transverse)
    (hy : ‖y‖ ≠ μ) (hy' : ‖y‖ ≠ Real.exp η*μ) :
    ∀ᶠ n in atTop,
      (r n • (y-t • (d n • w)) ∈ annularCore η (r n*s n) ↔
        μ < ‖y‖ ∧ ‖y‖ < Real.exp η*μ) := by
  have hnorm : Tendsto (fun n => ‖y-t • (d n • w)‖) atTop (𝓝 ‖y‖) := by
    simpa only [zero_smul,smul_zero,sub_zero] using
      ((tendsto_const_nhds (x := y)).sub ((hdlim.smul_const w).const_smul t)).norm
  have hmargin : Tendsto (fun n => gapCoefficient η*r n*s n^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (hrlim.const_mul (gapCoefficient η)).mul (hslim.pow 2)
  have hlo : Tendsto (fun n => s n+gapCoefficient η*r n*s n^2) atTop (𝓝 μ) := by
    simpa only [add_zero] using hslim.add hmargin
  have hhi : Tendsto (fun n => Real.exp η*s n-gapCoefficient η*r n*s n^2) atTop
      (𝓝 (Real.exp η*μ)) := by simpa only [sub_zero] using (hslim.const_mul (Real.exp η)).sub hmargin
  by_cases hl : μ < ‖y‖
  · by_cases hu : ‖y‖ < Real.exp η*μ
    · filter_upwards [hlo.eventually_lt hnorm hl,hnorm.eventually_lt hhi hu] with n hn hn'
      rw [mem_annularCore_dilation (hr n)]
      exact iff_of_true ⟨hn,hn'⟩ ⟨hl,hu⟩
    · have hu' : Real.exp η*μ < ‖y‖ := lt_of_le_of_ne (le_of_not_gt hu) (Ne.symm hy')
      filter_upwards [hhi.eventually_lt hnorm hu'] with n hn
      rw [mem_annularCore_dilation (hr n)]
      exact iff_of_false (fun h => (not_lt_of_ge hn.le) h.2) (fun h => hu h.2)
  · have hl' : ‖y‖ < μ := lt_of_le_of_ne (le_of_not_gt hl) hy
    filter_upwards [hnorm.eventually_lt hlo hl'] with n hn
    rw [mem_annularCore_dilation (hr n)]
    exact iff_of_false (fun h => (not_lt_of_ge hn.le) h.1) (fun h => hl h.1)

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # The vanishing stripe period and relative thermal shift -/

noncomputable section

open Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem stripe_dilation {r : ℝ} (hr : 0 < r) (s : ℝ) (a : Bool) (y : Transverse) :
    r • y ∈ stripe (r*s) a ↔ y ∈ stripeAtPeriod (r*s^2) a := by
  change (∃ k : ℤ, ((k:ℝ)+(if a then 0 else 1/2))*(r*s)^2 < r*y 0 ∧
    r*y 0 < ((k:ℝ)+(if a then 0 else 1/2)+1/4)*(r*s)^2) ↔ _
  have he (b : ℝ) : b*(r*s)^2 = r*(b*(r*s^2)) := by ring
  simp_rw [he,mul_lt_mul_iff_right₀ hr]
  rfl

theorem stripe_period_tendsto_zero {r s : ℕ → ℝ} {μ : ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (hs : Tendsto s atTop (𝓝 μ)) :
    Tendsto (fun n => r n*s n^2) atTop (𝓝 0) := by
  simpa only [zero_mul] using hr.mul (hs.pow 2)

end BoltzmannNonuniqueness.JetGeometry

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SheetGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end BoltzmannNonuniqueness.SheetMeasures

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

/-! # Weak limits are unchanged by a vanishing L1 error -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.of_integral_abs_sub
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f h : ℕ → X → ℝ} {g : X → ℝ}
    (hg : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ)
    (hh : ∀ n, Integrable (h n) μ)
    (herr : Tendsto (fun n => ∫ x, |h n x-f n x| ∂μ) atTop (𝓝 0)) :
    WeakL1Converges μ h g := by
  refine ⟨hg.1,hg.2.1,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have hC' (x) : |ψ x| ≤ |C| := (hC x).trans (le_abs_self C)
  have hi (n) : Integrable (fun x => ψ x*(h n x-f n x)) μ :=
    ((hh n).sub (hf n)).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC')
  have he : Tendsto (fun n => ∫ x, ψ x*(h n x-f n x) ∂μ) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => norm_integral_le_of_norm_le (((hh n).sub (hf n)).abs.const_mul |C|)
        (ae_of_all _ (fun x => by
          rw [Real.norm_eq_abs,abs_mul]
          exact mul_le_mul_of_nonneg_right (hC' x) (abs_nonneg _))))
    simpa only [integral_const_mul,mul_zero,Pi.sub_apply] using herr.const_mul |C|
  have ht := he.add (hg.2.2 ψ hψ ⟨C,hC⟩)
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [] with n
  rw [← integral_add (hi n) ((hf n).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC'))]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Bounded multipliers and uniqueness for weak L¹ limits -/

noncomputable section

open MeasureTheory Filter Set

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.congr_limit {μ : Measure X} {f : ℕ → X → ℝ} {g h : X → ℝ}
    (hg : WeakL1Converges μ f g) (hh : Measurable h) (he : g =ᵐ[μ] h) :
    WeakL1Converges μ f h := by
  refine ⟨hh,hg.2.1.congr he,?_⟩
  intro ψ hψ hB
  have ht := hg.2.2 ψ hψ hB
  have hi : (∫ x, ψ x*g x ∂μ) = ∫ x, ψ x*h x ∂μ :=
    integral_congr_ae (he.mono (fun x hx => congrArg (fun y => ψ x*y) hx))
  rw [hi] at ht
  exact ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Combining weak limits of time slices on finite windows -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.prod_of_fibers
    {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    {ν : Measure T} {μ : Measure X} [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    {f : ℕ → T × X → ℝ} {g : T × X → ℝ}
    (hf : ∀ n, Integrable (f n) (ν.prod μ)) (hgm : Measurable g) (hgi : Integrable g (ν.prod μ))
    {C : ℝ} (hbound : ∀ᶠ n in atTop, ∀ᵐ z ∂ν.prod μ, |f n z| ≤ C)
    (hlim : ∀ᵐ t ∂ν, WeakL1Converges μ (fun n x => f n (t,x)) (fun x => g (t,x))) :
    WeakL1Converges (ν.prod μ) f g := by
  refine ⟨hgm,hgi,?_⟩
  intro ψ hψ hB
  obtain ⟨D,hD⟩ := hB
  have hD' (z) : |ψ z| ≤ |D| := (hD z).trans (le_abs_self D)
  have hi (n) := (hf n).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hD')
  have hli := hgi.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hD')
  have htest := tendsto_integral_filter_of_norm_le_const
    (μ := ν) (l := (atTop : Filter ℕ)) (F := fun n t => ∫ x, ψ (t,x)*f n (t,x) ∂μ)
    (f := fun t => ∫ x, ψ (t,x)*g (t,x) ∂μ)
    (Eventually.of_forall (fun n => (hi n).integral_prod_left.aestronglyMeasurable))
    ?_ ?_
  · have heq (n) := integral_prod (fun z => ψ z*f n z) (hi n)
    have hgeq := integral_prod (fun z => ψ z*g z) hli
    simpa only [← heq,← hgeq] using htest
  · refine ⟨(|D| * C)*μ.real Set.univ,?_⟩
    filter_upwards [hbound] with n hn
    filter_upwards [Measure.ae_ae_of_ae_prod hn] with t ht
    have h := norm_integral_le_of_norm_le (f := fun x => ψ (t,x)*f n (t,x)) (integrable_const (μ := μ) (|D| * C)) ?_
    · simpa only [integral_const,smul_eq_mul,mul_comm] using h
    · filter_upwards [ht] with x hx
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hD' (t,x)) hx (abs_nonneg _) (abs_nonneg D)
  · filter_upwards [hlim] with t ht
    exact ht.2.2 (fun x => ψ (t,x)) (hψ.comp (measurable_const.prodMk measurable_id))
      ⟨D,fun x => hD (t,x)⟩

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AxialSecondMismatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Dilation identities for the implicit axial flow and compressed core -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.AxialFlow

theorem profile_dilation {r : ℝ} (hr : r ≠ 0) (σ α γ s z : ℝ) :
    profile σ α γ (r*s) (r*z) = profile σ α γ s z := by
  unfold profile
  congr 2
  field_simp

theorem velocity_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (σ z : ℝ) :
    velocity σ α γ (r*s) (r*t) (r*z) = velocity σ α γ s t z := by
  symm
  apply velocity_unique hα hγ (mul_pos hr hs) (mul_nonneg hr.le ht)
  rw [show r*z-r*t*velocity σ α γ s t z = r*(z-t*velocity σ α γ s t z) by ring,
    profile_dilation hr.ne']
  exact velocity_spec hα

theorem velocity_scale_tendsto {s : ℕ → ℝ} {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hslim : Tendsto s atTop (𝓝 μ)) (σ z : ℝ) :
    Tendsto (fun n => velocity σ α γ (s n) t z) atTop (𝓝 (velocity σ α γ μ t z)) := by
  let u := velocity σ α γ μ t z
  have htanh : Continuous Real.tanh := by
    convert continuous_profile 0 1 1 1 using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    simp [profile]
  have harg : Tendsto (fun n => γ*(z-t*u)/s n) atTop (𝓝 (γ*(z-t*u)/μ)) :=
    tendsto_const_nhds.div hslim hμ.ne'
  have hp : Tendsto (fun n => profile σ α γ (s n) (z-t*u)) atTop
      (𝓝 (profile σ α γ μ (z-t*u))) :=
    tendsto_const_nhds.add ((htanh.continuousAt.tendsto.comp harg).const_mul α)
  have hres : Tendsto (fun n => residual σ α γ (s n) t z u) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := u)).sub hp
    have hu : u-profile σ α γ μ (z-t*u) = 0 := sub_eq_zero.mpr (velocity_spec hα)
    simpa only [residual,hu] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_) (by simpa only [abs_zero] using hres.abs)
  have h := residual_inverse_lipschitz (σ := σ) (z := z) (u := velocity σ α γ (s n) t z) (v := u)
    hα hγ (hs n) ht
  have hz : residual σ α γ (s n) t z (velocity σ α γ (s n) t z) = 0 :=
    sub_eq_zero.mpr (velocity_spec hα)
  simpa only [hz,zero_sub,abs_neg,Real.norm_eq_abs,u] using h

end BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreMap

theorem axialMap_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (σ d z w : ℝ) :
    axialMap σ α γ (r*s) d (r*t) (r*z) w = axialMap σ α γ s d t z w := by
  unfold axialMap
  rw [show r*z-r*t*d*w = r*(z-t*d*w) by ring,
    AxialFlow.velocity_dilation hr hα hγ hs ht]

theorem axialMap_error_le {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 ≤ d) (ht : 0 ≤ t) (σ z w : ℝ) :
    |axialMap σ α γ s d t z w-AxialFlow.velocity σ α γ s t z| ≤ d*|w| := by
  have h := AxialFlow.thermal_velocity_error hα hγ hs ht (axialMap_spec hα σ γ s d t z w)
  simpa only [abs_mul,abs_of_nonneg hd] using h

end BoltzmannNonuniqueness.JetCoreMap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetCoreConvergence
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Limits of the compressed axial amplitude in thermal coordinates -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetCoreMap

theorem axialMap_tendsto {s d : ℕ → ℝ} {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hd : ∀ n, 0 ≤ d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hslim : Tendsto s atTop (𝓝 μ))
    (hdlim : Tendsto d atTop (𝓝 0)) (σ z w : ℝ) :
    Tendsto (fun n => axialMap σ α γ (s n) (d n) t z w) atTop
      (𝓝 (AxialFlow.velocity σ α γ μ t z)) := by
  have hdiff : Tendsto (fun n => axialMap σ α γ (s n) (d n) t z w-
      AxialFlow.velocity σ α γ (s n) t z) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => by simpa only [Real.norm_eq_abs] using axialMap_error_le hα hγ (hs n) (hd n) ht σ z w)
    simpa only [zero_mul] using hdlim.mul_const |w|
  have h := hdiff.add (AxialFlow.velocity_scale_tendsto hα hγ hs hμ ht hslim σ z)
  simpa only [sub_add_cancel,zero_add] using h

theorem sourceFoot_tendsto {s d : ℕ → ℝ} {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hd : ∀ n, 0 ≤ d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hslim : Tendsto s atTop (𝓝 μ))
    (hdlim : Tendsto d atTop (𝓝 0)) (σ z w : ℝ) :
    Tendsto (fun n => sourceFoot σ α γ (s n) (d n) t z w) atTop
      (𝓝 (AxialFlow.foot σ α γ μ t z)) := by
  simp_rw [sourceFoot_eq]
  exact tendsto_const_nhds.sub ((axialMap_tendsto hα hγ hs hd hμ ht hslim hdlim σ z w).const_mul t)

end BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem compressed_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (K ζ : ℝ) :
    r*compressed K α γ (r*s) (r*t) (r*ζ) = compressed K α γ s t ζ := by
  have harg : γ*(r*ζ)/(r*s) = γ*ζ/s := by field_simp
  have hSp : 0 ≤ S (γ*ζ/s) := (S_pos _).le
  have hden : s+t*α*γ*S (γ*ζ/s) ≠ 0 := ne_of_gt (by positivity)
  unfold compressed
  rw [harg]
  field_simp

theorem compressed_tendsto {s ζ : ℕ → ℝ} {α γ μ t z : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hslim : Tendsto s atTop (𝓝 μ)) (hζlim : Tendsto ζ atTop (𝓝 z)) (K : ℝ) :
    Tendsto (fun n => compressed K α γ (s n) t (ζ n)) atTop (𝓝 (compressed K α γ μ t z)) := by
  have harg := (hζlim.const_mul γ).div hslim hμ.ne'
  have hS := continuous_S.continuousAt.tendsto.comp harg
  have hSp : 0 ≤ S (γ*z/μ) := (S_pos _).le
  have hden : μ+t*α*γ*S (γ*z/μ) ≠ 0 := ne_of_gt (by positivity)
  have h := (hS.const_mul K).div (hslim.add (hS.const_mul (t*α*γ)))
    (by simpa only [mul_assoc] using hden)
  change Tendsto (fun n => K*S (γ*ζ n/s n)/(s n+(t*α*γ)*S (γ*ζ n/s n)))
    atTop (𝓝 (K*S (γ*z/μ)/(μ+(t*α*γ)*S (γ*z/μ)))) at h
  simpa only [compressed,mul_assoc] using h

theorem compressed_sourceFoot_tendsto {s d : ℕ → ℝ} {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hd : ∀ n, 0 ≤ d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hslim : Tendsto s atTop (𝓝 μ))
    (hdlim : Tendsto d atTop (𝓝 0)) (σ K z w : ℝ) :
    Tendsto (fun n => compressed K α γ (s n) t (JetCoreMap.sourceFoot σ α γ (s n) (d n) t z w))
      atTop (𝓝 (compressed K α γ μ t (AxialFlow.foot σ α γ μ t z))) :=
  compressed_tendsto hα hγ hμ ht hslim
    (JetCoreMap.sourceFoot_tendsto hα hγ hs hd hμ ht hslim hdlim σ z w) K

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # The actual thermal coordinate map converges to the axial atom -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.PlaneChart

theorem join_sub (y u : Transverse) (z v : ℝ) :
    join y z-join u v = join (y-u) (z-v) := by
  apply split.injective
  simp only [split_apply,transverse_sub,axial_sub,transverse_join,axial_join]

theorem join_tendsto {y : ℕ → Transverse} {z : ℕ → ℝ} {u : Transverse} {v : ℝ}
    (hy : Tendsto y atTop (𝓝 u)) (hz : Tendsto z atTop (𝓝 v)) :
    Tendsto (fun n => join (y n) (z n)) atTop (𝓝 (join u v)) := by
  have hyn : Tendsto (fun n => ‖y n-u‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hy.sub (tendsto_const_nhds (x := u))).norm
  have hzn : Tendsto (fun n => z n-v) atTop (𝓝 0) := by
    simpa only [sub_self] using hz.sub (tendsto_const_nhds (x := v))
  have he (n) : ‖join (y n) (z n)-join u v‖ =
      Real.sqrt (‖y n-u‖^2+(z n-v)^2) := by
    rw [join_sub,← norm_join_sq,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp_rw [he]
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp ((hyn.pow 2).add (hzn.pow 2))
  change Tendsto (fun n => Real.sqrt (‖y n-u‖^2+(z n-v)^2)) atTop
    (𝓝 (Real.sqrt ((0:ℝ)^2+0^2))) at h
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,Real.sqrt_zero] using h

end BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.JetCoreMeasure

theorem velocityMap_tendsto {s d : ℕ → ℝ} {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hd : ∀ n, 0 ≤ d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hslim : Tendsto s atTop (𝓝 μ))
    (hdlim : Tendsto d atTop (𝓝 0)) (σ z : ℝ) (w : Transverse × ℝ) :
    Tendsto (fun n => velocityMap σ α γ (s n) (d n) t z w) atTop
      (𝓝 (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))) := by
  apply PlaneChart.join_tendsto
  · simpa only [zero_smul] using hdlim.smul_const w.1
  · exact JetCoreMap.axialMap_tendsto hα hγ hs hd hμ ht hslim hdlim σ z w.2

end BoltzmannNonuniqueness.JetCoreMeasure

end

end

section

/-! # Convergence of the smooth factor of a cold core

The spatial stripe indicator is treated separately. This is the full thermal
integral of the compressed amplitude and a bounded continuous velocity test.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem continuous_compressed {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (K : ℝ) : Continuous (compressed K α γ s t) := by
  have hc : Continuous (fun ζ : ℝ => S (γ*ζ/s)) :=
    continuous_S.comp ((continuous_const.mul continuous_id).div_const s)
  apply (continuous_const.mul hc).div (continuous_const.add (continuous_const.mul hc))
  intro ζ
  change s+(t*α*γ)*S (γ*ζ/s) ≠ 0
  have := (S_pos (γ*ζ/s)).le
  exact ne_of_gt (by positivity)

theorem compressed_le_scale {K α γ s t a : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (ha : 0 < a) (hs : a ≤ s) (ht : 0 ≤ t) (ζ : ℝ) :
    compressed K α γ s t ζ ≤ K/a := by
  have hp := (S_pos (γ*ζ/s)).le
  have hden : a ≤ s+t*α*γ*S (γ*ζ/s) := le_add_of_le_of_nonneg hs (by positivity)
  calc
    compressed K α γ s t ζ ≤ K/(s+t*α*γ*S (γ*ζ/s)) :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_right hK (S_le_one _))
        (ha.le.trans hden)
    _ ≤ K/a := div_le_div_of_nonneg_left hK ha hden

theorem sourceFoot_continuous {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (σ d z : ℝ) :
    Continuous (JetCoreMap.sourceFoot σ α γ s d t z) :=
  (AxialFlow.foot_lipschitzWith hα hγ hs ht).continuous.comp
    (continuous_const.sub (continuous_const.mul continuous_id))

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # The physical axial cutoff disappears on the thermal support -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreMap

theorem sourceFoot_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (σ d z w : ℝ) :
    sourceFoot σ α γ (r*s) d (r*t) (r*z) w = r*sourceFoot σ α γ s d t z w := by
  rw [sourceFoot_eq,sourceFoot_eq,axialMap_dilation hr hα hγ hs ht]
  ring

theorem sourceFoot_abs_le {α d t : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (σ γ s z w : ℝ) (hw : |w| ≤ 1) :
    |sourceFoot σ α γ s d t z w| ≤ |z|+t*(|σ|+α+d) := by
  have hv : |axialMap σ α γ s d t z w| ≤ |σ|+α+d := by
    calc
      |axialMap σ α γ s d t z w| ≤ |d*w|+|AxialFlow.velocity σ α γ s t (z-t*d*w)| :=
        abs_add_le _ _
      _ ≤ d+(|σ|+α) := by
        rw [abs_mul,abs_of_nonneg hd]
        exact add_le_add (by nlinarith) (AxialTransport.velocity_abs_le hα)
      _ = _ := by ring
  rw [sourceFoot_eq]
  calc
    |z-t*axialMap σ α γ s d t z w| ≤ |z|+|t*axialMap σ α γ s d t z w| := abs_sub z _
    _ ≤ _ := by rw [abs_mul,abs_of_nonneg ht]; gcongr

end BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermal_parameter_axial_le_one {w : Transverse × ℝ}
    (hw : JetThermalKernel.J (SheetMeasures.join w) ≠ 0) : |w.2| ≤ 1 := by
  have hj : ‖SheetMeasures.join w‖ < 1 := by
    by_contra hn
    exact hw (JetThermalKernel.J_zero (le_of_not_gt hn))
  have he : ‖SheetMeasures.join w‖^2 = ‖w.1‖^2+w.2^2 := PlaneChart.norm_join_sq w.1 w.2
  nlinarith [sq_nonneg ‖w.1‖,norm_nonneg (SheetMeasures.join w),sq_abs w.2,abs_nonneg w.2]

theorem eventually_axial_cutoff {r s d : ℕ → ℝ} {α t : ℝ}
    (hα : 0 ≤ α) (hd : ∀ n, 0 ≤ d n) (ht : 0 ≤ t)
    (hrlim : Tendsto r atTop (𝓝 0)) (hdlim : Tendsto d atTop (𝓝 0)) (σ γ z : ℝ) :
    ∀ᶠ n in atTop, ∀ w : Transverse × ℝ,
      JetThermalKernel.J (SheetMeasures.join w) ≠ 0 →
      r n*JetCoreMap.sourceFoot σ α γ (s n) (d n) t z w.2 ∈
        Ioo (-(1/8:ℝ)) (1/8) := by
  have hsmall : ∀ᶠ n in atTop, |r n| * (|z|+t*(|σ|+α+1)) < (1/8:ℝ) := by
    have h := hrlim.abs.mul_const (|z|+t*(|σ|+α+1))
    have he := h.eventually (gt_mem_nhds (by norm_num : |(0:ℝ)| * (|z|+t*(|σ|+α+1)) < 1/8))
    exact he
  have hdsmall : ∀ᶠ n in atTop, d n < 1 := hdlim.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hsmall,hdsmall] with n hn hdn w hw
  apply abs_lt.mp
  rw [abs_mul]
  apply lt_of_le_of_lt _ hn
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (JetCoreMap.sourceFoot_abs_le hα (hd n) ht σ γ (s n) z w.2
    (thermal_parameter_axial_le_one hw)).trans (by gcongr)

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Thermal L1 convergence before spatial stripe averaging -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem testCoefficient_measurable {α γ s d t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (K σ z : ℝ) {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    Measurable (testCoefficient K α γ s d t σ z ψ) := by
  have hc : Continuous (fun w : Transverse × ℝ =>
      compressed K α γ s t (JetCoreMap.sourceFoot σ α γ s d t z w.2)) :=
    (continuous_compressed hα hγ hs ht K).comp
      ((sourceFoot_continuous hα hγ hs ht σ d z).comp continuous_snd)
  exact hc.measurable.mul (hψ.measurable.comp
    (JetCoreMeasure.velocity_measurePreserving hα hγ hs hd ht σ z).measurable)

theorem testCoefficient_abs_le {K α γ s t a B : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a)
    (hs : a ≤ s) (ht : 0 ≤ t) {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B)
    (d σ z : ℝ) (w : Transverse × ℝ) :
    |testCoefficient K α γ s d t σ z ψ w| ≤ K/a*B := by
  rw [testCoefficient,abs_mul,abs_of_nonneg (compressed_nonneg hK hα hγ (ha.trans_le hs) ht _)]
  exact mul_le_mul (compressed_le_scale hK hα hγ ha hs ht _) (hψB _)
    (abs_nonneg _) (div_nonneg hK ha.le)

theorem testCoefficient_tendsto {s d : ℕ → ℝ} {K α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hd : ∀ n, 0 ≤ d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hslim : Tendsto s atTop (𝓝 μ))
    (hdlim : Tendsto d atTop (𝓝 0)) {ψ : Velocity → ℝ} (hψ : Continuous ψ)
    (σ z : ℝ) (w : Transverse × ℝ) :
    Tendsto (fun n => testCoefficient K α γ (s n) (d n) t σ z ψ w) atTop
      (𝓝 (compressed K α γ μ t (AxialFlow.foot σ α γ μ t z) *
        ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)))) :=
  (compressed_sourceFoot_tendsto hα hγ hs hd hμ ht hslim hdlim σ K z w.2).mul
    (hψ.continuousAt.tendsto.comp
      (JetCoreMeasure.velocityMap_tendsto hα hγ hs hd hμ ht hslim hdlim σ z w))

theorem thermal_coefficient_error_tendsto {s d : ℕ → ℝ} {K α γ μ t a B : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a)
    (hs : ∀ n, a ≤ s n) (hd : ∀ n, 0 < d n) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) (σ z : ℝ) :
    Tendsto (fun n => ∫ w : Transverse × ℝ,
      |testCoefficient K α γ (s n) (d n) t σ z ψ w -
        compressed K α γ μ t (AxialFlow.foot σ α γ μ t z) *
          ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))| *
        JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume) atTop (𝓝 0) := by
  let c := compressed K α γ μ t (AxialFlow.foot σ α γ μ t z) *
    ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))
  have hsp (n) : 0 < s n := ha.trans_le (hs n)
  have hJ := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  have hmJ := JetThermalKernel.J_smooth.continuous.measurable.comp SheetMeasures.join.measurable
  have hl := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure Transverse).prod volume)
    (F := fun n w => |testCoefficient K α γ (s n) (d n) t σ z ψ w-c| *
      JetThermalKernel.J (SheetMeasures.join w)) (f := fun _ => (0:ℝ))
    (fun w => (K/a*B+|c|)*JetThermalKernel.J (SheetMeasures.join w))
    (fun n => (((testCoefficient_measurable hα hγ (hsp n) (hd n) ht K σ z hψ).sub
      measurable_const).abs.mul hmJ).aestronglyMeasurable) (hJ.const_mul _) ?_ ?_
  · simpa only [integral_zero] using hl
  · intro n
    filter_upwards [] with w
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (JetThermalKernel.J_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (JetThermalKernel.J_nonneg _)
    exact (abs_sub _ _).trans (add_le_add
      (testCoefficient_abs_le hK hα hγ ha (hs n) ht hψB (d n) σ z w) le_rfl)
  · filter_upwards [] with w
    have hc := testCoefficient_tendsto (K := K) hα hγ hsp (fun n => (hd n).le)
      hμ ht hslim hdlim hψ σ z w
    have h := ((hc.sub (tendsto_const_nhds (x := c))).abs).mul_const
      (JetThermalKernel.J (SheetMeasures.join w))
    simpa only [c,sub_self,abs_zero,zero_mul] using h

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Replacing the thermal coefficient inside arbitrary bounded masks -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

private theorem masked_error_le {f χ : Transverse × ℝ → ℝ} {S c : ℝ}
    (hf : Measurable f) (hχ : Measurable χ) (hfS : ∀ w, |f w| ≤ S)
    (hχ1 : ∀ w, |χ w| ≤ 1) :
    |(∫ w, χ w*f w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)-
      c*(∫ w, χ w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)| ≤
      ∫ w, |f w-c| *JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume := by
  have hJ := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  have hmJ := JetThermalKernel.J_smooth.continuous.measurable.comp SheetMeasures.join.measurable
  have hiχ : Integrable (fun w => χ w*JetThermalKernel.J (SheetMeasures.join w))
      ((volume : Measure Transverse).prod volume) := by
    apply hJ.mono' (hχ.mul hmJ).aestronglyMeasurable
    filter_upwards [] with w
    change ‖χ w*JetThermalKernel.J (SheetMeasures.join w)‖ ≤ JetThermalKernel.J (SheetMeasures.join w)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχ1 w) (JetThermalKernel.J_nonneg _)
  have hif : Integrable (fun w => χ w*f w*JetThermalKernel.J (SheetMeasures.join w))
      ((volume : Measure Transverse).prod volume) := by
    apply (hJ.const_mul S).mono' ((hχ.mul hf).mul hmJ).aestronglyMeasurable
    filter_upwards [] with w
    change ‖χ w*f w*JetThermalKernel.J (SheetMeasures.join w)‖ ≤ S*JetThermalKernel.J (SheetMeasures.join w)
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
    apply mul_le_mul_of_nonneg_right _ (JetThermalKernel.J_nonneg _)
    exact (mul_le_mul_of_nonneg_right (hχ1 w) (abs_nonneg _)).trans (by simpa using hfS w)
  have hierr : Integrable (fun w => |f w-c| *JetThermalKernel.J (SheetMeasures.join w))
      ((volume : Measure Transverse).prod volume) := by
    apply (hJ.const_mul (S+|c|)).mono' (((hf.sub measurable_const).abs).mul hmJ).aestronglyMeasurable
    filter_upwards [] with w
    change ‖|f w-c| *JetThermalKernel.J (SheetMeasures.join w)‖ ≤ (S+|c|)*JetThermalKernel.J (SheetMeasures.join w)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (JetThermalKernel.J_nonneg _))]
    exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (add_le_add (hfS w) le_rfl))
      (JetThermalKernel.J_nonneg _)
  have hidiff := hif.sub (hiχ.const_mul c)
  have he : (∫ w, χ w*f w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)-
      c*(∫ w, χ w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume) =
      ∫ w, χ w*f w*JetThermalKernel.J (SheetMeasures.join w)-
        c*(χ w*JetThermalKernel.J (SheetMeasures.join w))
        ∂(volume : Measure Transverse).prod volume := by
    rw [integral_sub hif (hiχ.const_mul c),integral_const_mul]
  rw [he]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono hidiff.norm hierr
  intro w
  change ‖χ w*f w*JetThermalKernel.J (SheetMeasures.join w)-
    c*(χ w*JetThermalKernel.J (SheetMeasures.join w))‖ ≤
    |f w-c| *JetThermalKernel.J (SheetMeasures.join w)
  rw [show χ w*f w*JetThermalKernel.J (SheetMeasures.join w)-
      c*(χ w*JetThermalKernel.J (SheetMeasures.join w)) =
      χ w*(f w-c)*JetThermalKernel.J (SheetMeasures.join w) by ring,
    Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχ1 w) (abs_nonneg (f w-c)))
    (JetThermalKernel.J_nonneg _)

theorem thermal_masked_error_tendsto {s d : ℕ → ℝ} {K α γ μ t a B : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a)
    (hs : ∀ n, a ≤ s n) (hd : ∀ n, 0 < d n) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    {χ : ℕ → Transverse × ℝ → ℝ} (hχ : ∀ n, Measurable (χ n))
    (hχ1 : ∀ n w, |χ n w| ≤ 1) (σ z : ℝ) :
    Tendsto (fun n =>
      (∫ w, χ n w*testCoefficient K α γ (s n) (d n) t σ z ψ w *
        JetThermalKernel.J (SheetMeasures.join w) ∂(volume : Measure Transverse).prod volume)-
      (compressed K α γ μ t (AxialFlow.foot σ α γ μ t z)*
        ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))) *
      (∫ w, χ n w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_) (thermal_coefficient_error_tendsto hK hα hγ ha hs hd hμ ht hslim hdlim hψ hψB σ z)
  rw [Real.norm_eq_abs]
  exact masked_error_le
    (testCoefficient_measurable hα hγ (ha.trans_le (hs n)) (hd n) ht K σ z hψ) (hχ n)
    (testCoefficient_abs_le hK hα hγ ha (hs n) ht hψB (d n) σ z) (hχ1 n)

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # The exact thermal-coordinate integral of the physical free core -/

noncomputable section

open MeasureTheory Set Filter
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCoreMeasure

theorem velocityMap_dilation {r α γ s t : ℝ} (hr : 0 < r) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (σ d z : ℝ) (w : Transverse × ℝ) :
    velocityMap σ α γ (r*s) d (r*t) (r*z) w = velocityMap σ α γ s d t z w := by
  unfold velocityMap
  rw [JetCoreMap.axialMap_dilation hr hα hγ hs ht]

end BoltzmannNonuniqueness.JetCoreMeasure

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem weight_measurable {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (η K d : ℝ) (a : Bool) (x : Space) :
    Measurable (weight η K α γ s d t a x) := by
  have hm : Measurable (fun w : Transverse × ℝ =>
      (JetGeometry.mask η s a).indicator (fun _ => (1:ℝ)) (x.1-t • (d • w.1))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η s a)).comp (by fun_prop)
  have hf := ((sourceFoot_continuous hα hγ hs ht (sign a) d x.2).comp
    (continuous_snd : Continuous (Prod.snd : Transverse × ℝ → ℝ))).measurable
  have hc := ((continuous_compressed hα hγ hs ht K).measurable.indicator
    (measurableSet_Ioo : MeasurableSet (Ioo (-(1/8:ℝ)) (1/8)))).comp hf
  exact (hm.mul hc).mul (JetThermalKernel.J_smooth.continuous.measurable.comp
    SheetMeasures.join.measurable)

theorem weight_nonneg {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η d : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    0 ≤ weight η K α γ s d t a x w := by
  unfold weight
  apply mul_nonneg _ (JetThermalKernel.J_nonneg _)
  apply mul_nonneg
  · exact indicator_nonneg (fun _ _ => zero_le_one) _
  · exact indicator_nonneg (fun ζ _ => compressed_nonneg hK hα hγ hs ht ζ) _

theorem free_test_integral {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (η : ℝ) (a : Bool) (x : Space) {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    (∫ v, JetFreeTransport.free η K α γ s d t a (x,v)*ψ v) =
      ∫ w : Transverse × ℝ, weight η K α γ s d t a x w *
        ψ (JetCoreMeasure.velocityMap (sign a) α γ s d t x.2 w)
        ∂(volume : Measure Transverse).prod volume := by
  have hfm : Measurable (fun v => JetFreeTransport.free η K α γ s d t a (x,v)) :=
    (JetFreeTransport.measurable_free η K α γ s d t a).comp
      (measurable_const.prodMk measurable_id)
  have hwm := weight_measurable hα hγ hs ht η K d a x
  have hi := measure_identity hα hγ hs hd ht η K a x
  have hvm := (JetCoreMeasure.velocity_measurePreserving hα hγ hs hd ht (sign a) x.2).measurable
  calc
    _ = ∫ v, ψ v ∂volume.withDensity
        (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x,v))) := by
      rw [integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (JetFreeTransport.free_nonneg hK hs.le hd.le η α γ t a _),
        smul_eq_mul]
    _ = ∫ w, ψ (JetCoreMeasure.velocityMap (sign a) α γ s d t x.2 w)
        ∂((volume : Measure Transverse).prod volume).withDensity
          (fun w => ENNReal.ofReal (weight η K α γ s d t a x w)) := by
      rw [← hi,integral_map hvm.aemeasurable hψ.measurable.aestronglyMeasurable]
    _ = _ := by
      rw [integral_withDensity_eq_integral_toReal_smul hwm.ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (weight_nonneg hK hα hγ hs ht η d a x _),smul_eq_mul]

theorem weight_dilation {r α γ s t : ℝ} (hr : 0 < r) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η K d : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    r*weight η K α γ (r*s) d (r*t) a (r • x) w =
      (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • x.1-(r*t) • (d • w.1)) *
      (Ioo (-(1/8:ℝ)) (1/8)).indicator (fun _ => (1:ℝ))
        (r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
      compressed K α γ s t (JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
      JetThermalKernel.J (SheetMeasures.join w) := by
  unfold weight
  change r * (_ * (Ioo (-(1/8:ℝ)) (1/8)).indicator (compressed K α γ (r*s) (r*t))
    (JetCoreMap.sourceFoot (sign a) α γ (r*s) d (r*t) (r*x.2) w.2) * _) = _
  rw [JetCoreMap.sourceFoot_dilation hr hα hγ hs ht]
  by_cases hz : r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2 ∈ Ioo (-(1/8:ℝ)) (1/8)
  · simp only [indicator_of_mem hz,mul_one]
    change r * ((JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • x.1-(r*t) • (d • w.1)) * compressed K α γ (r*s) (r*t)
        (r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
        JetThermalKernel.J (SheetMeasures.join w)) = _
    rw [show r * ((JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • x.1-(r*t) • (d • w.1)) * compressed K α γ (r*s) (r*t)
        (r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
        JetThermalKernel.J (SheetMeasures.join w)) =
      (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • x.1-(r*t) • (d • w.1)) * (r*compressed K α γ (r*s) (r*t)
        (r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2)) *
        JetThermalKernel.J (SheetMeasures.join w) by ring]
    rw [compressed_dilation hr hα hγ hs ht]
  · simp only [indicator_of_notMem hz,mul_zero,zero_mul]

theorem dilated_free_test_integral {r K α γ s d t : ℝ} (hr : 0 < r)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 ≤ t) (η : ℝ) (a : Bool) (x : Space)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    (∫ v, r*JetFreeTransport.free η K α γ (r*s) d (r*t) a (r • x,v)*ψ v) =
      ∫ w : Transverse × ℝ,
        (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
          (r • x.1-(r*t) • (d • w.1)) *
        (Ioo (-(1/8:ℝ)) (1/8)).indicator (fun _ => (1:ℝ))
          (r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
        compressed K α γ s t (JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
        ψ (JetCoreMeasure.velocityMap (sign a) α γ s d t x.2 w) *
        JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume := by
  have hi := free_test_integral hK hα hγ (mul_pos hr hs) hd (mul_nonneg hr.le ht) η a (r • x) hψ
  calc
    _ = r * (∫ v, JetFreeTransport.free η K α γ (r*s) d (r*t) a (r • x,v)*ψ v) := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    _ = r * (∫ w : Transverse × ℝ, weight η K α γ (r*s) d (r*t) a (r • x) w *
        ψ (JetCoreMeasure.velocityMap (sign a) α γ (r*s) d (r*t) (r • x).2 w)
        ∂(volume : Measure Transverse).prod volume) := by rw [hi]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      rw [← mul_assoc,weight_dilation hr hα hγ hs ht]
      change _ * ψ (JetCoreMeasure.velocityMap (sign a) α γ (r*s) d (r*t) (r*x.2) w) = _
      rw [JetCoreMeasure.velocityMap_dilation hr hα hγ hs ht]
      ring

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Reduction of the actual dilated free core to its spatial mask average -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem dilatedMask_measurable (r η s d t : ℝ) (a : Bool) (x : Space) :
    Measurable (dilatedMask r η s d t a x) :=
  (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η (r*s) a)).comp (by fun_prop)

theorem dilatedMask_abs_le (r η s d t : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    |dilatedMask r η s d t a x w| ≤ 1 := by
  unfold dilatedMask
  by_cases h : r • x.1-(r*t) • (d • w.1) ∈ JetGeometry.mask η (r*s) a
  · simp only [indicator_of_mem h,abs_one,le_refl]
  · simp only [indicator_of_notMem h,abs_zero,zero_le_one]

theorem dilated_free_thermal_reduction {r s d : ℕ → ℝ} {K α γ μ t b B : ℝ}
    (hr : ∀ n, 0 < r n) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hb : 0 < b) (hs : ∀ n, b ≤ s n) (hd : ∀ n, 0 < d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hrlim : Tendsto r atTop (𝓝 0))
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (η : ℝ) (a : Bool) (x : Space) :
    Tendsto (fun n =>
      (∫ v, r n*JetFreeTransport.free η K α γ (r n*s n) (d n) (r n*t) a (r n • x,v)*ψ v)-
      (compressed K α γ μ t (AxialFlow.foot (sign a) α γ μ t x.2)*
        ψ (PlaneChart.join 0 (AxialFlow.velocity (sign a) α γ μ t x.2))) *
      (∫ w, dilatedMask (r n) η (s n) (d n) t a x w *
        JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)) atTop (𝓝 0) := by
  have hbase := thermal_masked_error_tendsto hK hα hγ hb hs hd hμ ht hslim hdlim hψ hψB
    (fun n => dilatedMask_measurable (r n) η (s n) (d n) t a x)
    (fun n w => dilatedMask_abs_le (r n) η (s n) (d n) t a x w) (sign a) x.2
  apply hbase.congr'
  filter_upwards [eventually_axial_cutoff (s := s) hα (fun n => (hd n).le) ht hrlim hdlim
    (sign a) γ x.2] with n hn
  congr 1
  rw [dilated_free_test_integral (hr n) hK hα hγ (hb.trans_le (hs n)) (hd n) ht η a x hψ]
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : JetThermalKernel.J (SheetMeasures.join w) = 0
  · simp only [hw,mul_zero]
  · rw [indicator_of_mem (hn w hw),mul_one]
    unfold testCoefficient dilatedMask
    ring

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Removing the annular margins in local thermal L1 -/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem measurableSet_scaleShell (η μ : ℝ) : MeasurableSet (scaleShell η μ) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

theorem ae_norm_ne (a : ℝ) : ∀ᵐ y : Transverse, ‖y‖ ≠ a := by
  apply ae_iff.mpr
  have he : {y : Transverse | ¬‖y‖ ≠ a} = sphere 0 a := by
    ext y
    simp only [not_not,mem_ofPred_eq,mem_sphere,dist_zero_right]
  rw [he]
  exact Measure.addHaar_sphere volume 0 a

theorem ae_annular_indicator_tendsto {r s d : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    (η t : ℝ) (Ω : Set Transverse) :
    ∀ᵐ p : Transverse × (Transverse × ℝ) ∂(volume.restrict Ω).prod
      ((volume : Measure Transverse).prod volume),
      Tendsto (fun n => |(annularCore η (r n*s n)).indicator (fun _ => (1:ℝ))
        (r n • (p.1-t • (d n • p.2.1)))-
        (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1| *
        JetThermalKernel.J (SheetMeasures.join p.2)) atTop (𝓝 0) := by
  have hy : ∀ᵐ y ∂(volume : Measure Transverse).restrict Ω,
      ‖y‖ ≠ μ ∧ ‖y‖ ≠ Real.exp η*μ :=
    ae_restrict_of_ae ((ae_norm_ne μ).and (ae_norm_ne (Real.exp η*μ)))
  have hp : ∀ᵐ p : Transverse × (Transverse × ℝ) ∂((volume : Measure Transverse).restrict Ω).prod
      ((volume : Measure Transverse).prod volume),
      ‖p.1‖ ≠ μ ∧ ‖p.1‖ ≠ Real.exp η*μ :=
    (Measure.quasiMeasurePreserving_fst (ν := (volume : Measure Transverse).prod volume)).ae hy
  filter_upwards [hp] with p hp
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_annularCore_dilation hr hrlim hslim hdlim η t p.1 p.2.1 hp.1 hp.2]
    with n hn
  have he : (annularCore η (r n*s n)).indicator (fun _ => (1:ℝ))
      (r n • (p.1-t • (d n • p.2.1))) =
      (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1 := by
    by_cases h : μ < ‖p.1‖ ∧ ‖p.1‖ < Real.exp η*μ
    · rw [indicator_of_mem (hn.mpr h),indicator_of_mem (show p.1 ∈ scaleShell η μ from h)]
    · rw [indicator_of_notMem (fun h' => h (hn.mp h')),
        indicator_of_notMem (show p.1 ∉ scaleShell η μ from h)]
  simp only [he,sub_self,abs_zero,zero_mul]

end BoltzmannNonuniqueness.JetGeometry

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

theorem spatial_mask_L1_tendsto {r s d : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    (η t : ℝ) (a : Bool) (Ω : Set Transverse) (hΩ : volume Ω < ⊤) :
    Tendsto (fun n => ∫ p : Transverse × (Transverse × ℝ),
      |(mask η (r n*s n) a).indicator (fun _ => (1:ℝ))
          (r n • (p.1-t • (d n • p.2.1))) -
        (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1 *
          (stripe (r n*s n) a).indicator (fun _ => (1:ℝ))
            (r n • (p.1-t • (d n • p.2.1)))| *
      JetThermalKernel.J (SheetMeasures.join p.2)
      ∂(volume.restrict Ω).prod ((volume : Measure Transverse).prod volume))
      atTop (𝓝 0) := by
  let _ : IsFiniteMeasure ((volume : Measure Transverse).restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hΩ⟩
  have hm (n) : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (mask η (r n*s n) a).indicator (fun _ => (1:ℝ))
        (r n • (p.1-t • (d n • p.2.1)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η (r n*s n) a)).comp (by fun_prop)
  have hstripe (n) : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (stripe (r n*s n) a).indicator (fun _ => (1:ℝ))
        (r n • (p.1-t • (d n • p.2.1)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_stripe (r n*s n) a)).comp (by fun_prop)
  have hshell : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1) :=
    (measurable_const.indicator (measurableSet_scaleShell η μ)).comp measurable_fst
  have hJ := (HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable).comp_snd ((volume : Measure Transverse).restrict Ω)
  have hmJ : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      JetThermalKernel.J (SheetMeasures.join p.2)) :=
    (JetThermalKernel.J_smooth.continuous.measurable.comp SheetMeasures.join.measurable).comp measurable_snd
  have hl := tendsto_integral_of_dominated_convergence
    (μ := (volume.restrict Ω).prod ((volume : Measure Transverse).prod volume))
    (F := fun n p => |(mask η (r n*s n) a).indicator (fun _ => (1:ℝ))
      (r n • (p.1-t • (d n • p.2.1)))-
      (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1 *
      (stripe (r n*s n) a).indicator (fun _ => (1:ℝ))
        (r n • (p.1-t • (d n • p.2.1)))| *JetThermalKernel.J (SheetMeasures.join p.2))
    (f := fun _ => (0:ℝ)) (fun p => 2*JetThermalKernel.J (SheetMeasures.join p.2))
    (fun n => (((hm n).sub (hshell.mul (hstripe n))).abs.mul hmJ).aestronglyMeasurable)
    (hJ.const_mul 2) ?_ ?_
  · simpa only [integral_zero] using hl
  · intro n
    filter_upwards [] with p
    change ‖|_ - _| *JetThermalKernel.J (SheetMeasures.join p.2)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (JetThermalKernel.J_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (JetThermalKernel.J_nonneg _)
    apply (mask_error_le η (r n*s n) μ a _ _).trans
    have hbound (A : Set Transverse) (y : Transverse) : |A.indicator (fun _ => (1:ℝ)) y| ≤ 1 := by
      by_cases h : y ∈ A <;> simp [Set.indicator,h]
    exact (abs_sub _ _).trans ((add_le_add (hbound _ _) (hbound _ _)).trans (by norm_num))
  · filter_upwards [ae_annular_indicator_tendsto hr hrlim hslim hdlim η t Ω] with p hp
    apply squeeze_zero (fun _ => mul_nonneg (abs_nonneg _) (JetThermalKernel.J_nonneg _))
      (fun n => mul_le_mul_of_nonneg_right (mask_error_le η (r n*s n) μ a _ _)
        (JetThermalKernel.J_nonneg _)) hp

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Annular mask error after integrating out the thermal variable -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem maskError_measurable (r η s d μ t : ℝ) (a : Bool) :
    Measurable (maskError r η s d μ t a) := by
  have hm : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (mask η s a).indicator (fun _ => (1:ℝ)) (r • (p.1-t • (d • p.2.1)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η s a)).comp (by fun_prop)
  have hs : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (stripe s a).indicator (fun _ => (1:ℝ)) (r • (p.1-t • (d • p.2.1)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_stripe s a)).comp (by fun_prop)
  have hc : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1) :=
    (measurable_const.indicator (measurableSet_scaleShell η μ)).comp measurable_fst
  exact (hm.sub (hc.mul hs)).mul
    ((JetThermalKernel.J_smooth.continuous.measurable.comp SheetMeasures.join.measurable).comp
      measurable_snd)

theorem maskError_abs_le (r η s d μ t : ℝ) (a : Bool) (p : Transverse × (Transverse × ℝ)) :
    |maskError r η s d μ t a p| ≤ 2*JetThermalKernel.J (SheetMeasures.join p.2) := by
  have hi (A : Set Transverse) (y : Transverse) : |A.indicator (fun _ => (1:ℝ)) y| ≤ 1 := by
    by_cases h : y ∈ A <;> simp [h]
  unfold maskError
  rw [abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
  apply mul_le_mul_of_nonneg_right _ (JetThermalKernel.J_nonneg _)
  apply (abs_sub _ _).trans
  have hp : |(scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1*
      (stripe s a).indicator (fun _ => (1:ℝ)) (r • (p.1-t • (d • p.2.1)))| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul (hi _ _) (hi _ _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  linarith [hi (mask η s a) (r • (p.1-t • (d • p.2.1)))]

theorem maskError_integrable (r η s d μ t : ℝ) (a : Bool)
    (ν : Measure Transverse) [IsFiniteMeasure ν] :
    Integrable (maskError r η s d μ t a) (ν.prod ((volume : Measure Transverse).prod volume)) := by
  have hJ := (HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable).comp_snd ν
  apply (hJ.const_mul 2).mono' (maskError_measurable r η s d μ t a).aestronglyMeasurable
  filter_upwards [] with p
  exact maskError_abs_le r η s d μ t a p

theorem maskError_average_L1_le (r η s d μ t : ℝ) (a : Bool)
    (ν : Measure Transverse) [IsFiniteMeasure ν] :
    (∫ y, |∫ w, maskError r η s d μ t a (y,w)
      ∂(volume : Measure Transverse).prod volume| ∂ν) ≤
    ∫ p, |maskError r η s d μ t a p| ∂ν.prod ((volume : Measure Transverse).prod volume) := by
  have hi := maskError_integrable r η s d μ t a ν
  change (∫ y, ‖∫ w, maskError r η s d μ t a (y,w)
    ∂(volume : Measure Transverse).prod volume‖ ∂ν) ≤
    ∫ p, ‖maskError r η s d μ t a p‖ ∂ν.prod ((volume : Measure Transverse).prod volume)
  rw [integral_prod _ hi.norm]
  apply integral_mono hi.integral_prod_left.norm hi.integral_norm_prod_left
  intro y
  exact norm_integral_le_integral_norm _

theorem maskError_average_L1_tendsto {r s d : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    (η t : ℝ) (a : Bool) (Ω : Set Transverse) (hΩ : volume Ω < ⊤) :
    Tendsto (fun n => ∫ y, |∫ w, maskError (r n) η (r n*s n) (d n) μ t a (y,w)
      ∂(volume : Measure Transverse).prod volume| ∂volume.restrict Ω) atTop (𝓝 0) := by
  let _ : IsFiniteMeasure ((volume : Measure Transverse).restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hΩ⟩
  have hb := spatial_mask_L1_tendsto hr hrlim hslim hdlim η t a Ω hΩ
  have he : Tendsto (fun n => ∫ p, |maskError (r n) η (r n*s n) (d n) μ t a p|
      ∂(volume.restrict Ω).prod ((volume : Measure Transverse).prod volume)) atTop (𝓝 0) := by
    simpa only [maskError,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)] using hb
  exact squeeze_zero (fun n => integral_nonneg (fun y => abs_nonneg _))
    (fun n => maskError_average_L1_le (r n) η (r n*s n) (d n) μ t a _) he

end BoltzmannNonuniqueness.JetGeometry

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

theorem phase_bounds {η : ℝ} (hη : 0 < η) (a : ℝ) :
    phase a η ∈ Icc 1 (Real.exp η) := by
  constructor
  · exact Real.one_le_exp_iff.mpr (mul_nonneg hη.le (Int.fract_nonneg _))
  · apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left (Int.fract_lt_one (Real.log a/η)).le hη.le).trans_eq (mul_one η)

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

/-! # Disjoint annuli in the limiting geometric mesh -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.GeometricMesh

theorem point_mono {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) : Monotone (point θ η) := by
  intro i j hij
  unfold point
  apply mul_le_mul_of_nonneg_left _ hθ
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hij) hη

theorem point_succ (θ η : ℝ) (k : ℤ) : point θ η (k+1) = Real.exp η*point θ η k := by
  unfold point
  rw [Int.cast_add,Int.cast_one,mul_add,mul_one,Real.exp_add]
  ring

theorem point_gap {θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) {i j : ℤ} (hij : i < j) :
    Real.exp η*point θ η i ≤ point θ η j := by
  rw [← point_succ]
  exact point_mono hθ hη (by omega)

theorem phase_lt_exp {η : ℝ} (hη : 0 < η) (a : ℝ) : phase a η < Real.exp η := by
  apply Real.exp_lt_exp.mpr
  exact (mul_lt_mul_of_pos_left (Int.fract_lt_one _) hη).trans_eq (mul_one η)

theorem cell_bounds {θ η ρ : ℝ} (hθ : 0 < θ) (hη : 0 < η) (hρ : 0 < ρ) :
    point θ η (index (ρ/θ) η) ≤ ρ ∧
      ρ < Real.exp η*point θ η (index (ρ/θ) η) := by
  have hp := point_pos hθ η (index (ρ/θ) η)
  have he : ρ = phase (ρ/θ) η*point θ η (index (ρ/θ) η) := by
    have h := normalization (div_pos hρ hθ) hη.ne'
    calc
      ρ = θ*(ρ/θ) := by field_simp
      _ = θ*(phase (ρ/θ) η*Real.exp (η*(index (ρ/θ) η:ℝ))) := congrArg (θ*·) h
      _ = _ := by unfold point; ring
  constructor
  · calc
      _ ≤ phase (ρ/θ) η*point θ η (index (ρ/θ) η) :=
        le_mul_of_one_le_left hp.le (phase_bounds hη _).1
      _ = ρ := he.symm
  · calc
      ρ = phase (ρ/θ) η*point θ η (index (ρ/θ) η) := he
      _ < _ := mul_lt_mul_of_pos_right (phase_lt_exp hη _) hp

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

/-! # The atomic background on the limiting geometric mesh -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem scale_eq_of_shell {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η)
    {k : ℤ} {y : Transverse} (hy : y ∈ JetGeometry.scaleShell η (GeometricMesh.point θ η k)) :
    scale θ η y = GeometricMesh.point θ η k := by
  have hρ : 0 < ‖y‖ := (GeometricMesh.point_pos hθ η k).trans hy.1
  have hb := GeometricMesh.cell_bounds hθ hη hρ
  have hi : GeometricMesh.index (‖y‖/θ) η = k := by
    rcases lt_trichotomy (GeometricMesh.index (‖y‖/θ) η) k with h | h | h
    · exact False.elim ((hb.2.trans_le (GeometricMesh.point_gap hθ.le hη.le h)).not_ge hy.1.le)
    · exact h
    · exact False.elim ((hy.2.trans_le (GeometricMesh.point_gap hθ.le hη.le h)).not_ge hb.1)
  exact congrArg (GeometricMesh.point θ η) hi

theorem background_on_shell {θ η l K α γ t : ℝ} (hθ : 0 < θ) (hη : 0 < η)
    {k : ℤ} {x : JetPrototype.Space}
    (hx : x.1 ∈ JetGeometry.scaleShell η (GeometricMesh.point θ η k))
    (hl : l < GeometricMesh.point θ η k) :
    background θ η l K α γ t x = AxialBackground.cell K α γ (GeometricMesh.point θ η k) t x.2 := by
  have hs := scale_eq_of_shell hθ hη hx
  have ha : active θ η l x.1 := by rw [active,hs]; exact ⟨hl,hx⟩
  rw [background,ite_eq_left ha,hs]

end BoltzmannNonuniqueness.GeometricBackground

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

section

/-! # Only finitely many geometric shells meet a fixed radial window -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.GeometricMesh

theorem point_strictMono {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) :
    StrictMono (point θ η) := by
  intro i j hij
  apply mul_lt_mul_of_pos_left _ hθ
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_left (by exact_mod_cast hij) hη

theorem shell_index {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η)
    {k : ℤ} {y : VelocityWeight.Transverse}
    (hy : y ∈ JetGeometry.scaleShell η (point θ η k)) :
    index (‖y‖/θ) η = k :=
  (point_strictMono hθ hη).injective (GeometricBackground.scale_eq_of_shell hθ hη hy)

theorem index_mono {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hη : 0 < η) :
    index a η ≤ index b η :=
  Int.floor_mono (div_le_div_of_nonneg_right (Real.log_le_log ha hab) hη.le)

theorem shell_index_window {θ η δ R : ℝ} (hθ₁ : 1 ≤ θ) (hθ₂ : θ ≤ Real.exp η)
    (hη : 0 < η) (hδ : 0 < δ) {k : ℤ} {y : VelocityWeight.Transverse}
    (hy : y ∈ JetGeometry.scaleShell η (point θ η k)) (hlo : δ ≤ ‖y‖) (hhi : ‖y‖ ≤ R) :
    index (δ/Real.exp η) η ≤ k ∧ k ≤ index R η := by
  have hθ : 0 < θ := zero_lt_one.trans_le hθ₁
  have hl : δ/Real.exp η ≤ ‖y‖/θ := by
    apply (div_le_div_iff₀ (Real.exp_pos η) hθ).mpr
    exact (mul_le_mul_of_nonneg_left hθ₂ hδ.le).trans
      (mul_le_mul_of_nonneg_right hlo (Real.exp_pos η).le)
  have hu : ‖y‖/θ ≤ R := by
    apply (div_le_iff₀ hθ).mpr
    exact hhi.trans (le_mul_of_one_le_right ((norm_nonneg y).trans hhi) hθ₁)
  have hidx := shell_index hθ hη hy
  exact ⟨hidx ▸ index_mono (div_pos hδ (Real.exp_pos η)) hl hη,
    hidx ▸ index_mono (div_pos (hδ.trans_le hlo) hθ) hu hη⟩

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Reindexing a finite cold sum on a fixed geometric mesh window -/

noncomputable section

namespace BoltzmannNonuniqueness.GeometricMesh

theorem meshIndex_at_jetIndex (s₀ η : ℝ) (r : ℕ → ℝ) (n : ℕ) {k : ℤ}
    (hk : k < index (s₀/r n) η) :
    jetMeshIndex s₀ η (r n) (jetIndex s₀ η r k n) = k := by
  unfold jetMeshIndex jetIndex annularIndex
  have he := Int.toNat_of_nonneg (by omega : 0 ≤ index (s₀/r n) η-k)
  omega

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Discreteness of the normalized geometric scales at a positive limit -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

theorem scale_succ (s₀ η : ℝ) (m : ℕ) :
    Real.exp η*DatumBounds.scale s₀ η (m+1) = DatumBounds.scale s₀ η m := by
  unfold DatumBounds.scale
  rw [mul_left_comm,← Real.exp_add]
  congr 2
  push_cast
  ring

theorem scale_gap {s₀ η : ℝ} (hs₀ : 0 ≤ s₀) (hη : 0 ≤ η) {m n : ℕ} (hmn : m < n) :
    Real.exp η*DatumBounds.scale s₀ η n ≤ DatumBounds.scale s₀ η m := by
  calc
    _ ≤ Real.exp η*DatumBounds.scale s₀ η (m+1) :=
      mul_le_mul_of_nonneg_left (JetGeometry.scale_antitone hs₀ hη hmn) (Real.exp_pos η).le
    _ = _ := scale_succ s₀ η m

theorem indices_eventually_eq_of_same_positive_limit {s₀ η μ : ℝ}
    (hs₀ : 0 ≤ s₀) (hη : 0 < η) (hμ : 0 < μ)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) {m n : ℕ → ℕ}
    (hm : Tendsto (fun j => DatumBounds.scale s₀ η (m j)/r j) atTop (𝓝 μ))
    (hn : Tendsto (fun j => DatumBounds.scale s₀ η (n j)/r j) atTop (𝓝 μ)) :
    ∀ᶠ j in atTop, m j = n j := by
  have hgap : μ < Real.exp η*μ := by
    have he : 1 < Real.exp η := Real.one_lt_exp_iff.mpr hη
    nlinarith
  have hmn := hm.eventually_lt (hn.const_mul (Real.exp η)) hgap
  have hnm := hn.eventually_lt (hm.const_mul (Real.exp η)) hgap
  filter_upwards [hmn,hnm] with j hj₁ hj₂
  rcases lt_trichotomy (m j) (n j) with h | h | h
  · have hb := div_le_div_of_nonneg_right (scale_gap hs₀ hη.le h) (hr j).le
    rw [mul_div_assoc] at hb
    exact False.elim ((not_lt_of_ge hb) hj₁)
  · exact h
  · have hb := div_le_div_of_nonneg_right (scale_gap hs₀ hη.le h) (hr j).le
    rw [mul_div_assoc] at hb
    exact False.elim ((not_lt_of_ge hb) hj₂)

end BoltzmannNonuniqueness.GeometricMesh

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakL1ToWeakStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Extending bounded cold-average convergence to all L1 tests -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Compactness

private theorem bounded_pairing_error {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g a : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (ha : Measurable a) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hab : ∀ᵐ x ∂μ, |a x| ≤ C)
    (hdiff : eLpNorm (f-g) 1 μ ≤ ENNReal.ofReal δ) :
    |(∫ x, f x*a x ∂μ)-(∫ x, g x*a x ∂μ)| ≤ C*δ := by
  have hfg := hf.sub hg
  have hfa : Integrable (fun x => f x*a x) μ :=
    (hf.bdd_mul ha.aestronglyMeasurable hab).congr (ae_of_all _ (fun x => mul_comm _ _))
  have hga : Integrable (fun x => g x*a x) μ :=
    (hg.bdd_mul ha.aestronglyMeasurable hab).congr (ae_of_all _ (fun x => mul_comm _ _))
  have hi : (∫ x, ‖f x-g x‖ ∂μ) ≤ δ := by
    apply (ENNReal.ofReal_le_ofReal_iff hδ).mp
    change ENNReal.ofReal (∫ x, ‖(f-g) x‖ ∂μ) ≤ ENNReal.ofReal δ
    rw [ofReal_integral_norm_eq_lintegral_enorm hfg]
    rwa [eLpNorm_one_eq_lintegral_enorm] at hdiff
  rw [← integral_sub hfa hga,← Real.norm_eq_abs]
  have he : (fun x => f x*a x-g x*a x) = (fun x => (f x-g x)*a x) := by
    funext x
    ring
  rw [he]
  apply (norm_integral_le_of_norm_le (hfg.norm.const_mul C) ?_).trans
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hi hC
  · filter_upwards [hab] with x hx
    change ‖(f x-g x)*a x‖ ≤ C*‖f x-g x‖
    rw [norm_mul,Real.norm_eq_abs (a x)]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem weakStar_of_continuous_compact_tests
    {X : Type*} [MetricSpace X] [SecondCountableTopology X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} [μ.Regular]
    {a : ℕ → X → ℝ} {b : X → ℝ}
    (ham : ∀ n, Measurable (a n)) (hbm : Measurable b)
    {C : ℝ} (hC : 0 ≤ C)
    (hab : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |a n x| ≤ C)
    (hbb : ∀ᵐ x ∂μ, |b x| ≤ C)
    (htest : ∀ g : X → ℝ, Continuous g → HasCompactSupport g →
      Tendsto (fun n => ∫ x, g x*a n x ∂μ) atTop (𝓝 (∫ x, g x*b x ∂μ))) :
    WeakStarLInfConverges μ a b := by
  refine ⟨hbm,fun f hf => Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  let δ := ε/(3*(2*C+1))
  have hden : 0 < 3*(2*C+1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ*(3*(2*C+1)) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨g,hgc,hfg,hg,hgm⟩ :=
    (memLp_one_iff_integrable.mpr hf).exists_hasCompactSupport_eLpNorm_sub_le
      (by norm_num : (1:ℝ≥0∞) ≠ ⊤) (ne_of_gt (ENNReal.ofReal_pos.mpr hδ))
  have hgi : Integrable g μ := memLp_one_iff_integrable.mp hgm
  have hmid := Metric.tendsto_nhds.mp (htest g hg hgc) (ε/3) (by positivity)
  filter_upwards [hab,hmid] with n han hgn
  rw [Real.dist_eq] at hgn ⊢
  have hleft := bounded_pairing_error hf hgi (ham n) hC hδ.le han hfg
  have hright := bounded_pairing_error hf hgi hbm hC hδ.le hbb hfg
  have htri₁ := abs_sub_le (∫ x, f x*a n x ∂μ) (∫ x, g x*a n x ∂μ) (∫ x, f x*b x ∂μ)
  have htri₂ := abs_sub_le (∫ x, g x*a n x ∂μ) (∫ x, g x*b x ∂μ) (∫ x, f x*b x ∂μ)
  rw [abs_sub_comm (∫ x, g x*b x ∂μ)] at htri₂
  nlinarith

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Integrating bounded weak-star limits over additional variables -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

theorem weakStar_zero_of_fibers
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {g : ℕ → X × Y → ℝ} (hm : ∀ n, Measurable (g n))
    (hb : ∀ n z, |g n z| ≤ 1)
    (hf : ∀ y, WeakStarLInfConverges μ (fun n x => g n (x,y)) (fun _ => 0)) :
    WeakStarLInfConverges (μ.prod ν) g (fun _ => 0) := by
  refine ⟨measurable_const,?_⟩
  intro ψ hψ
  have hi (n) : Integrable (fun z => ψ z*g n z) (μ.prod ν) := by
    exact (hψ.bdd_mul (hm n).aestronglyMeasurable (ae_of_all _ (hb n))).congr
      (ae_of_all _ (fun z => mul_comm _ _))
  have ht := tendsto_integral_of_dominated_convergence
    (μ := ν) (F := fun n y => ∫ x, ψ (x,y)*g n (x,y) ∂μ)
    (f := fun _ => (0:ℝ)) (fun y => ∫ x, ‖ψ (x,y)‖ ∂μ)
    (fun n => (hi n).integral_prod_right.aestronglyMeasurable)
    hψ.integral_norm_prod_right ?_ ?_
  · simp only [mul_zero,integral_zero] at ht ⊢
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact integral_prod_symm _ (hi n)
  · intro n
    filter_upwards [hψ.prod_left_ae] with y hy
    apply norm_integral_le_of_norm_le hy.norm
    filter_upwards [] with x
    rw [norm_mul,Real.norm_eq_abs (g n (x,y))]
    exact (mul_le_mul_of_nonneg_left (hb n (x,y)) (norm_nonneg _)).trans_eq (mul_one _)
  · filter_upwards [hψ.prod_left_ae] with y hy
    simpa only [mul_zero,integral_zero] using (hf y).2 (fun x => ψ (x,y)) hy

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Weak-star convergence under measure-preserving coordinates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Compactness

theorem WeakStarLInfConverges.comp_measurableEquiv {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) {f : ℕ → Y → ℝ} {g : Y → ℝ}
    (h : WeakStarLInfConverges ν f g) :
    WeakStarLInfConverges μ (fun n => f n ∘ e) (g ∘ e) := by
  refine ⟨h.1.comp e.measurable,?_⟩
  intro ψ hψ
  have hi := (MeasurePreserving.symm e he).integrable_comp_of_integrable hψ
  have ht := h.2 (ψ ∘ e.symm) hi
  have hid (k : Y → ℝ) :
      (∫ y, (ψ ∘ e.symm) y*k y ∂ν) = ∫ x, ψ x*(k ∘ e) x ∂μ := by
    rw [← he.integral_comp' (fun y => (ψ ∘ e.symm) y*k y)]
    simp only [Function.comp_apply,MeasurableEquiv.symm_apply_apply]
  simpa only [hid] using ht

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Localizing bounded weak-star convergence -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Compactness

theorem WeakStarLInfConverges.restrict {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {a : ℕ → X → ℝ} {b : X → ℝ}
    (h : WeakStarLInfConverges μ a b) {s : Set X} (hs : MeasurableSet s) :
    WeakStarLInfConverges (μ.restrict s) a b := by
  refine ⟨h.1,?_⟩
  intro ψ hψ
  have ht := h.2 (s.indicator ψ) ((integrable_indicator_iff hs).mpr hψ)
  have heq (f : X → ℝ) : (∫ x, s.indicator ψ x*f x ∂μ) = ∫ x, ψ x*f x ∂μ.restrict s := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ s <;> simp [hx]
  simpa only [heq] using ht

end BoltzmannNonuniqueness.Compactness

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

/-! # The three-dimensional Jacobian in the cold dilation -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace BoltzmannNonuniqueness.ColdDilationMeasure

theorem space_finrank : Module.finrank ℝ JetPrototype.Space = 3 := by
  simp [JetPrototype.Space,VelocityWeight.Transverse,Module.finrank_prod]

end BoltzmannNonuniqueness.ColdDilationMeasure

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetFamilyBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform bounds for the free-core velocity averages -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermal_integral_one :
    (∫ w : Transverse × ℝ, JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume) = 1 := by
  rw [HotRectangleDensity.join_measurePreserving.integral_comp
    SheetMeasures.join.measurableEmbedding, JetThermalKernel.J_integral]

theorem masked_thermal_bound {χ : Transverse × ℝ → ℝ}
    (hχ : ∀ w, |χ w| ≤ 1) :
    |∫ w, χ w*JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume| ≤ 1 := by
  have hJ := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  dsimp only [Function.comp_def] at hJ
  rw [← Real.norm_eq_abs, ← thermal_integral_one]
  apply norm_integral_le_of_norm_le hJ
  filter_upwards [] with w
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hχ w) (JetThermalKernel.J_nonneg _)

theorem free_average_bound {K α γ s d t B : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s)
    (hd : 0 < d) (ht : 0 < t) (η : ℝ) (a : Bool) (x : JetPrototype.Space)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    |∫ v, JetFreeTransport.free η K α γ s d t a (x,v)*ψ v| ≤
      ((K*max 1 (α*γ)⁻¹)/t)*B := by
  rw [free_test_integral hK hα.le hγ.le hs hd ht.le η a x hψ,← Real.norm_eq_abs]
  let C := (K*max 1 (α*γ)⁻¹)/t
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hK (le_max_of_le_left zero_le_one)) ht.le
  have hJ := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  dsimp only [Function.comp_def] at hJ
  have hb (w) : weight η K α γ s d t a x w ≤ C*JetThermalKernel.J (SheetMeasures.join w) := by
    apply (weight_bound hK hα hγ hs ht.le η d a x w).trans
    apply mul_le_mul_of_nonneg_right _ (JetThermalKernel.J_nonneg _)
    exact div_le_div_of_nonneg_left
      (mul_nonneg hK (le_max_of_le_left zero_le_one)) ht (by linarith)
  calc
    _ ≤ ∫ w, (C*B)*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume := by
      apply norm_integral_le_of_norm_le (hJ.const_mul (C*B))
      filter_upwards [] with w
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (weight_nonneg hK hα.le hγ.le hs ht.le η d a x w)]
      exact (mul_le_mul (hb w) (hψB _) (abs_nonneg _) (mul_nonneg hC
        (JetThermalKernel.J_nonneg _))).trans_eq (by ring)
    _ = C*B := by rw [integral_const_mul,thermal_integral_one,mul_one]

theorem dilated_free_average_bound {r K α γ s d t B : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 < t) (η : ℝ) (a : Bool) (x : JetPrototype.Space)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    |∫ v, r*JetFreeTransport.free η K α γ s d (r*t) a (r • x,v)*ψ v| ≤
      ((K*max 1 (α*γ)⁻¹)/t)*B := by
  have hb := mul_le_mul_of_nonneg_left
    (free_average_bound hK hα hγ hs hd (mul_pos hr ht) η a (r • x) hψ hψB) hr.le
  simp_rw [mul_assoc r,integral_const_mul,abs_mul,abs_of_pos hr]
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  field_simp

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Separating the shell factor from the thermal stripe average -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem masked_thermal_integrable {χ : Transverse × ℝ → ℝ}
    (hχ : Measurable χ) (hb : ∀ w, |χ w| ≤ 1) :
    Integrable (fun w => χ w*JetThermalKernel.J (SheetMeasures.join w))
      ((volume : Measure Transverse).prod volume) := by
  have hJ := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  dsimp only [Function.comp_def] at hJ
  apply hJ.mono' (hχ.mul (JetThermalKernel.J_smooth.continuous.measurable.comp
    SheetMeasures.join.measurable)).aestronglyMeasurable
  filter_upwards [] with w
  change ‖χ w*JetThermalKernel.J (SheetMeasures.join w)‖ ≤
    JetThermalKernel.J (SheetMeasures.join w)
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb w) (JetThermalKernel.J_nonneg _)

theorem dilatedMask_eq (r η s d t : ℝ) (a : Bool) (x : JetPrototype.Space)
    (w : Transverse × ℝ) :
    dilatedMask r η s d t a x w =
      (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • (x.1-t • (d • w.1))) := by
  unfold dilatedMask
  congr 1
  module

end BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetGeometry

theorem maskError_average_eq (r η s d μ t : ℝ) (a : Bool) (x : JetPrototype.Space) :
    (∫ w, maskError r η (r*s) d μ t a (x.1,w)
      ∂(volume : Measure Transverse).prod volume) =
    (∫ w, JetCoreDensity.dilatedMask r η s d t a x w*JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume)-
    (scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1*
      (∫ w, (stripe (r*s) a).indicator (fun _ => (1:ℝ))
        (r • (x.1-t • (d • w.1)))*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume) := by
  have hb (A : Set Transverse) (w : Transverse × ℝ) :
      |A.indicator (fun _ => (1:ℝ)) (r • (x.1-t • (d • w.1)))| ≤ 1 := by
    by_cases h : r • (x.1-t • (d • w.1)) ∈ A <;> simp [h]
  have hm (A : Set Transverse) (hA : MeasurableSet A) :
      Measurable (fun w : Transverse × ℝ =>
        A.indicator (fun _ => (1:ℝ)) (r • (x.1-t • (d • w.1)))) :=
    (measurable_const.indicator hA).comp (by fun_prop)
  have hi := JetCoreDensity.masked_thermal_integrable
    (hm _ (JetMaskMeasure.measurableSet_mask η (r*s) a)) (hb _)
  have hs := JetCoreDensity.masked_thermal_integrable
    (hm _ (JetMaskMeasure.measurableSet_stripe (r*s) a)) (hb _)
  simp_rw [maskError,JetCoreDensity.dilatedMask_eq,sub_mul,mul_assoc]
  rw [integral_sub hi (hs.const_mul _),integral_const_mul]

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # Spatial regularity of the two terms in thermal concentration -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem limitingCoefficient_measurable {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (K σ : ℝ) {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    Measurable (limitingCoefficient K α γ μ t σ ψ) := by
  have hp : Continuous (fun x : JetPrototype.Space => (t,x.2)) :=
    continuous_const.prodMk continuous_snd
  have hf := (AxialFlow.clamped_foot_continuous (σ := σ) hα hγ hμ).comp hp
  have hv := (AxialFlow.clamped_velocity_continuous (σ := σ) hα hγ hμ).comp hp
  dsimp only [Function.comp_def] at hf hv
  simp only [max_eq_right ht] at hf hv
  have hj : Measurable (fun x : JetPrototype.Space =>
      PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t x.2)) :=
    VelocityWeight.split.symm.measurable.comp (hv.measurable.prodMk measurable_const)
  exact ((continuous_compressed hα hγ hμ ht K).comp hf).measurable.mul (hψ.measurable.comp hj)

theorem limitingCoefficient_bound {K α γ μ t B : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ) (ht : 0 < t)
    {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) (σ : ℝ) (x : JetPrototype.Space) :
    |limitingCoefficient K α γ μ t σ ψ x| ≤ ((K*max 1 (α*γ)⁻¹)/t)*B := by
  rw [limitingCoefficient,abs_mul,abs_of_nonneg (compressed_nonneg hK hα.le hγ.le hμ ht.le _)]
  apply mul_le_mul _ (hψB _) (abs_nonneg _) (by positivity)
  exact (compressed_bound hK hα hγ hμ ht.le _).trans
    (div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one)) ht (by linarith))

theorem free_average_measurable (r η K α γ s d t : ℝ) (a : Bool)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun x : JetPrototype.Space =>
      ∫ v, r*JetFreeTransport.free η K α γ s d (r*t) a (r • x,v)*ψ v) := by
  have hp : Measurable (fun p : JetPrototype.Space × Velocity => (r • p.1,p.2)) :=
    by fun_prop
  have hm : Measurable (fun p : JetPrototype.Space × Velocity =>
      r*JetFreeTransport.free η K α γ s d (r*t) a (r • p.1,p.2)*ψ p.2) :=
    (measurable_const.mul
    ((JetFreeTransport.measurable_free η K α γ s d (r*t) a).comp hp)).mul
      (hψ.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem mask_average_measurable (r η s d t : ℝ) (a : Bool) :
    Measurable (fun x : JetPrototype.Space => ∫ w,
      dilatedMask r η s d t a x w*JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume) := by
  have hp : Measurable (fun p : JetPrototype.Space × (Transverse × ℝ) =>
      r • p.1.1-(r*t) • (d • p.2.1)) := by fun_prop
  have hmask : Measurable (fun p : JetPrototype.Space × (Transverse × ℝ) =>
      (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • p.1.1-(r*t) • (d • p.2.1))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η (r*s) a)).comp hp
  have hm := hmask.mul
      ((JetThermalKernel.J_smooth.continuous.measurable.comp
        SheetMeasures.join.measurable).comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end BoltzmannNonuniqueness.JetCoreDensity

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

/-! # Scalar scales at an attained cap time -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Cap

theorem dilation_radius_pos {t δ : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) : 0 < t+δ :=
  add_pos_of_nonneg_of_pos ht hδ

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

section

/-! # Small primitives of bounded periodic functions of mean zero -/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.PeriodicAveraging

theorem bounded_intervalIntegrable {g : ℝ → ℝ} (hm : Measurable g)
    (hb : ∀ x, |g x| ≤ 1) (a b : ℝ) : IntervalIntegrable g volume a b := by
  apply (intervalIntegrable_const (c := (1:ℝ))).mono_fun' hm.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x)

theorem primitive_bound {g : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hper : Function.Periodic g p) (hm : Measurable g) (hb : ∀ x, |g x| ≤ 1)
    (hmean : (∫ x in 0..p, g x) = 0) (x : ℝ) :
    |∫ t in 0..x, g t| ≤ p := by
  let e := Int.fract (x/p)*p
  have he : e ∈ Ico 0 p := Int.fract_div_mul_self_mem_Ico p x hp
  have hi := bounded_intervalIntegrable hm hb
  have heq : (∫ t in 0..x, g t) = ∫ t in 0..e, g t := by
    rw [← Int.fract_div_mul_self_add_zsmul_eq p x hp.ne',
      ← intervalIntegral.integral_add_adjacent_intervals (hi 0 e) (hi e _),
      hper.intervalIntegral_add_zsmul_eq _ e hi,hper.intervalIntegral_add_eq e 0,
      zero_add,hmean,smul_zero,add_zero]
  rw [heq]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := e) (C := (1:ℝ)) (f := g) (fun t _ => by simpa only [Real.norm_eq_abs] using hb t)
  simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg he.1,one_mul] at hnorm
  exact hnorm.trans he.2.le

theorem interval_bound {g : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hper : Function.Periodic g p) (hm : Measurable g) (hb : ∀ x, |g x| ≤ 1)
    (hmean : (∫ x in 0..p, g x) = 0) (a b : ℝ) :
    |∫ t in a..b, g t| ≤ 2*p := by
  have hi := bounded_intervalIntegrable hm hb
  have heq := intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a b)
  have ha := primitive_bound hp hper hm hb hmean a
  have hb' := primitive_bound hp hper hm hb hmean b
  have htri := abs_sub_le (∫ t in 0..b, g t) 0 (∫ t in 0..a, g t)
  rw [sub_zero,zero_sub,abs_neg] at htri
  have hsub : (∫ t in a..b, g t) = (∫ t in 0..b, g t)-(∫ t in 0..a, g t) := by linarith
  rw [hsub]
  linarith

theorem test_bound {g φ : ℝ → ℝ} {p a b : ℝ} (hp : 0 < p) (hab : a ≤ b)
    (hper : Function.Periodic g p) (hm : Measurable g) (hb : ∀ x, |g x| ≤ 1)
    (hmean : (∫ x in 0..p, g x) = 0)
    (hφ : AbsolutelyContinuousOnInterval φ a b) :
    |∫ t in a..b, φ t*g t| ≤ (2*p)*(|φ b|+∫ t in a..b, |deriv φ t|) := by
  let G : ℝ → ℝ := fun x => ∫ t in a..x, g t
  have hi := bounded_intervalIntegrable hm hb a b
  have hG : AbsolutelyContinuousOnInterval G a b :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hder : ∀ᵐ x, x ∈ uIcc a b → deriv G x = g x := by
    filter_upwards [hi.ae_hasDerivAt_integral] with x hx hxab
    exact (hx hxab a (by simp)).deriv
  have heq : (∫ t in a..b, φ t*g t) = φ b*G b-(∫ t in a..b, deriv φ t*G t) := by
    calc
      _ = ∫ t in a..b, φ t*deriv G t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hder] with x hx hxab
        rw [hx (uIoc_subset_uIcc hxab)]
      _ = _ := by
        rw [hφ.integral_mul_deriv_eq_deriv_mul hG]
        simp [G]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab
    (f := fun t => deriv φ t*G t) (g := fun t => (2*p)*|deriv φ t|) ?_
    (hφ.intervalIntegrable_deriv.norm.const_mul (2*p))
  · rw [Real.norm_eq_abs,intervalIntegral.integral_const_mul] at hnorm
    rw [heq]
    have hGb := interval_bound hp hper hm hb hmean a b
    have hm := mul_le_mul_of_nonneg_left hGb (abs_nonneg (φ b))
    have ht := abs_sub (φ b*G b) (∫ t in a..b, deriv φ t*G t)
    rw [abs_mul] at ht
    nlinarith
  · filter_upwards [] with x _
    have hGB := interval_bound hp hper hm hb hmean a x
    change |deriv φ x*G x| ≤ (2*p)*|deriv φ x|
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hGB (abs_nonneg _)).trans_eq (mul_comm _ _)

end BoltzmannNonuniqueness.PeriodicAveraging

end

end

section

/-! # Weak averaging on bounded intervals, uniformly over the phase -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.PeriodicAveraging

theorem ac_test_tendsto_zero {g : ℕ → ℝ → ℝ} {p : ℕ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hp : ∀ n, 0 < p n) (hplim : Tendsto p atTop (𝓝 0))
    (hper : ∀ n, Function.Periodic (g n) (p n)) (hm : ∀ n, Measurable (g n))
    (hb : ∀ n x, |g n x| ≤ 1) (hmean : ∀ n, (∫ x in 0..p n, g n x) = 0)
    {φ : ℝ → ℝ} (hφ : AbsolutelyContinuousOnInterval φ a b) :
    Tendsto (fun n => ∫ x in a..b, φ x*g n x) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _)
    (fun n => test_bound (hp n) hab (hper n) (hm n) (hb n) (hmean n) hφ)
  simpa only [mul_zero,zero_mul] using
    (hplim.const_mul 2).mul_const (|φ b|+∫ x in a..b, |deriv φ x|)

theorem uniformContinuous_test_tendsto_zero {g : ℕ → ℝ → ℝ} {p : ℕ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hp : ∀ n, 0 < p n) (hplim : Tendsto p atTop (𝓝 0))
    (hper : ∀ n, Function.Periodic (g n) (p n)) (hm : ∀ n, Measurable (g n))
    (hb : ∀ n x, |g n x| ≤ 1) (hmean : ∀ n, (∫ x in 0..p n, g n x) = 0)
    {φ : ℝ → ℝ} (hφ : UniformContinuous φ) :
    Tendsto (fun n => ∫ x in a..b, φ x*g n x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(2*(|b-a|+1))
  have hden : 0 < 2*(|b-a|+1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hδε : δ*(2*(|b-a|+1)) = ε := div_mul_cancel₀ ε hden.ne'
  obtain ⟨f,hfc,hf⟩ := hφ.exists_contDiff_dist_le hδ
  have hfAC : AbsolutelyContinuousOnInterval f a b :=
    (hfc.contDiffOn.of_le (by norm_num)).absolutelyContinuousOnInterval
  have hfzero := ac_test_tendsto_zero hab hp hplim hper hm hb hmean hfAC
  have hfsmall := Metric.tendsto_nhds.mp hfzero (ε/2) (by positivity)
  filter_upwards [hfsmall] with n hn
  have hiφ := (bounded_intervalIntegrable (hm n) (hb n) a b).continuousOn_mul
    hφ.continuous.continuousOn
  have hif := (bounded_intervalIntegrable (hm n) (hb n) a b).continuousOn_mul
    hfc.continuous.continuousOn
  have hdiff : (∫ x in a..b, φ x*g n x)-(∫ x in a..b, f x*g n x) =
      ∫ x in a..b, (φ x-f x)*g n x := by
    rw [← intervalIntegral.integral_sub hiφ hif]
    congr 1
    funext x
    ring
  have herr : |(∫ x in a..b, φ x*g n x)-(∫ x in a..b, f x*g n x)| ≤ δ*|b-a| := by
    rw [hdiff,← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x _
    rw [Real.norm_eq_abs,abs_mul]
    have hx : |φ x-f x| ≤ δ := by
      simpa only [Real.dist_eq,abs_sub_comm] using (hf x).le
    exact (mul_le_mul_of_nonneg_left (hb n x) (abs_nonneg _)).trans
      (by simpa only [mul_one] using hx)
  rw [Real.dist_eq,sub_zero] at hn ⊢
  have htri := abs_sub_le (∫ x in a..b, φ x*g n x) (∫ x in a..b, f x*g n x) 0
  simp only [sub_zero] at htri
  nlinarith

end BoltzmannNonuniqueness.PeriodicAveraging

end

end

section

/-! # Vanishing periodic oscillations against every L1 test -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.PeriodicAveraging

theorem weakStar_zero {g : ℕ → ℝ → ℝ} {p : ℕ → ℝ}
    (hp : ∀ n, 0 < p n) (hplim : Tendsto p atTop (𝓝 0))
    (hper : ∀ n, Function.Periodic (g n) (p n)) (hm : ∀ n, Measurable (g n))
    (hb : ∀ n x, |g n x| ≤ 1) (hmean : ∀ n, (∫ x in 0..p n, g n x) = 0) :
    Compactness.WeakStarLInfConverges volume g (fun _ => 0) := by
  apply Compactness.weakStar_of_continuous_compact_tests hm measurable_const
    (C := 1) (by norm_num) (Eventually.of_forall (fun n => ae_of_all _ (hb n)))
    (ae_of_all _ (fun _ => by norm_num))
  intro φ hφ hc
  obtain ⟨R,hR,hball⟩ := hc.isBounded.subset_ball_lt 0 (0:ℝ)
  have hzero (x : ℝ) (hx : x ∉ Ioc (-R) R) : φ x = 0 := by
    by_contra hxφ
    have hnorm : |x| < R := by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using hball (subset_closure hxφ)
    exact hx ⟨(abs_lt.mp hnorm).1,(abs_lt.mp hnorm).2.le⟩
  have heq (n : ℕ) : (∫ x, φ x*g n x) = ∫ x in (-R)..R, φ x*g n x := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hzero x hx,zero_mul])).symm
  simp only [mul_zero,integral_zero]
  simp_rw [heq]
  exact uniformContinuous_test_tendsto_zero (by linarith) hp hplim hper hm hb hmean
    (hc.uniformContinuous_of_continuous hφ)

end BoltzmannNonuniqueness.PeriodicAveraging

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetContinuation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrability of the spatial thermal-reduction error -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermal_error_integrable {r K α γ s d μ t B : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hs : 0 < s) (hd : 0 < d) (hμ : 0 < μ) (ht : 0 < t)
    (η : ℝ) (a : Bool) {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    Integrable (fun x => (∫ v, r*JetFreeTransport.free η K α γ s d (r*t) a (r • x,v)*ψ v)-
      limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
        (∫ w, dilatedMask r η (s/r) d t a x w*JetThermalKernel.J (SheetMeasures.join w)
          ∂(volume : Measure Transverse).prod volume)) ρ := by
  have hm := (free_average_measurable r η K α γ s d t a hψ.measurable).sub
    ((limitingCoefficient_measurable hα.le hγ.le hμ ht.le K (JetPrototype.sign a) hψ).mul
      (mask_average_measurable r η (s/r) d t a))
  apply Integrable.of_bound hm.aestronglyMeasurable (2*(((K*max 1 (α*γ)⁻¹)/t)*B))
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  dsimp only [Pi.sub_apply,Pi.mul_apply]
  apply (abs_sub _ _).trans
  have hf := dilated_free_average_bound hr hK hα hγ hs hd ht η a x hψ hψB
  have hc := limitingCoefficient_bound hK hα hγ hμ ht hψB (JetPrototype.sign a) x
  have hb := masked_thermal_bound (dilatedMask_abs_le r η (s/r) d t a x)
  have hp : |limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
      (∫ w, dilatedMask r η (s/r) d t a x w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)| ≤ ((K*max 1 (α*γ)⁻¹)/t)*B := by
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hb).trans hc
  linarith

end BoltzmannNonuniqueness.JetCoreDensity

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

end AttainedCapSequence
end BoltzmannNonuniqueness.JetCopyDatum

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

theorem HotLimitExtraction.coldLabel_scale_tendsto_zero (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) :
    Tendsto (fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus) atTop (𝓝 0) := by
  have h := ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop).mul
    (E.coldLabel_scale_limit hs₀ hη k a)
  simpa only [Function.comp_def,zero_mul,mul_div_cancel₀ _ (S.radius_pos hs₀ _).ne'] using h

theorem HotLimitExtraction.coldLabel_width_tendsto_zero (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) :
    Tendsto (fun n => d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
      atTop (𝓝 0) := by
  simpa only [zero_pow (by decide : (10:ℕ) ≠ 0),mul_zero] using
    ((E.coldLabel_scale_tendsto_zero hs₀ hη k a).pow 10).const_mul d₀

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The positive terminal cap scale is an excluded cold label -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_at_endpoint (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hfrac : 0 < E.fraction) (k : ℤ) (a : Bool)
    (hk : E.phase*Real.exp (η*(k:ℝ)) = E.fraction) :
    ∀ᶠ n in atTop, (E.coldLabel k a n).annulus = F.indices (E.indices n) := by
  have hm := E.coldLabel_scale_limit hs₀ hη k a
  rw [hk] at hm
  have he := GeometricMesh.indices_eventually_eq_of_same_positive_limit hs₀.le hη hfrac
    (fun n => S.radius_pos hs₀ (E.indices n)) hm E.fraction_limit
  filter_upwards [he] with n hn
  exact Nat.add_right_cancel hn

theorem HotLimitExtraction.coldLabel_below_endpoint (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool)
    (hk : E.phase*Real.exp (η*(k:ℝ)) < E.fraction) :
    ∀ᶠ n in atTop, F.indices (E.indices n) < (E.coldLabel k a n).annulus := by
  have he := (E.coldLabel_scale_limit hs₀ hη k a).eventually_lt E.fraction_limit hk
  filter_upwards [he] with n hn
  by_contra h
  have hb := JetGeometry.scale_antitone hs₀.le hη.le
    (Nat.add_le_add_right (le_of_not_gt h) 1)
  exact (not_lt_of_ge hb)
    ((div_lt_div_iff_of_pos_right (S.radius_pos hs₀ (E.indices n))).mp hn)

theorem HotLimitExtraction.coldLabel_retained_iff (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) :
    ∀ᶠ n in atTop, ((E.coldLabel k a n).annulus < F.indices (E.indices n) ↔
      E.fraction < E.phase*Real.exp (η*(k:ℝ))) := by
  rcases lt_trichotomy E.fraction (E.phase*Real.exp (η*(k:ℝ))) with h | h | h
  · filter_upwards [E.coldLabel_retained hs₀ hη k a h] with n hn
    exact iff_of_true hn h
  · have hp : 0 < E.fraction := by
      rw [h]
      exact mul_pos (lt_of_lt_of_le zero_lt_one E.phase_mem.1) (Real.exp_pos _)
    filter_upwards [E.coldLabel_at_endpoint hs₀ hη hp k a h.symm] with n hn
    rw [hn,h]
    simp only [lt_self_iff_false]
  · filter_upwards [E.coldLabel_below_endpoint hs₀ hη k a h] with n hn
    exact iff_of_false (not_lt_of_ge hn.le) (not_lt_of_ge h.le)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Thermal mask replacement on finite spatial cylinders -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_mask_average_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) (t : ℝ)
    (Ω : Set Transverse) (hΩ : volume Ω < ⊤) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    let r := fun n => S.radius (E.indices n)
    let s := fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
    let d := fun n => d₀*(s n)^10
    let μ := E.phase*Real.exp (η*(k:ℝ))
    Tendsto (fun n => ∫ x : JetPrototype.Space,
      |∫ w, JetGeometry.maskError (r n) η (s n) (d n) μ t a (x.1,w)
        ∂(volume : Measure Transverse).prod volume| ∂(volume.restrict Ω).prod ν)
      atTop (𝓝 0) := by
  intro r s d μ
  have hr (n) : 0 < r n := S.radius_pos hs₀ (E.indices n)
  have hrlim : Tendsto r atTop (𝓝 0) :=
    (S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop
  have hb := JetGeometry.maskError_average_L1_tendsto hr hrlim
    (E.coldLabel_scale_limit hs₀ hη k a) (E.coldLabel_width_tendsto_zero hs₀ hη k a)
    η t a Ω hΩ
  change Tendsto (fun n => ∫ y, |∫ w,
    JetGeometry.maskError (r n) η (r n*(s n/r n)) (d n) μ t a (y,w)
      ∂(volume : Measure Transverse).prod volume| ∂volume.restrict Ω) atTop (𝓝 0) at hb
  simp only [mul_div_cancel₀ _ (hr _).ne'] at hb
  have h := hb.const_mul (ν.real univ)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [] with n
  exact (integral_fun_fst (μ := volume.restrict Ω) (ν := ν)
    (fun y => |∫ w, JetGeometry.maskError (r n) η (s n) (d n) μ t a (y,w)
      ∂(volume : Measure Transverse).prod volume|)).symm

theorem HotLimitExtraction.coldLabel_mask_average_integrable (E : HotLimitExtraction S)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ)
    (Ω : Set Transverse) (hΩ : volume Ω < ⊤) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Integrable (fun x : JetPrototype.Space => ∫ w,
      JetGeometry.maskError (S.radius (E.indices n)) η
        (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)
        (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10)
        (E.phase*Real.exp (η*(k:ℝ))) t a (x.1,w)
      ∂(volume : Measure Transverse).prod volume) ((volume.restrict Ω).prod ν) := by
  let _ : IsFiniteMeasure ((volume : Measure Transverse).restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hΩ⟩
  exact (JetGeometry.maskError_integrable _ _ _ _ _ _ _
    ((volume : Measure Transverse).restrict Ω)).integral_prod_left.comp_fst ν

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

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

/-! # Thermal concentration for the actual mesh labels -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_thermal_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 ≤ t) {B : ℝ} {ψ : Velocity → ℝ}
    (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) (x : JetPrototype.Space) :
    let r := fun n => S.radius (E.indices n)
    let s := fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
    let d := fun n => d₀*(s n)^10
    let μ := E.phase*Real.exp (η*(k:ℝ))
    Tendsto (fun n => (∫ v, r n*JetFreeTransport.free η K α γ (s n) (d n)
        (r n*t) a (r n • x,v)*ψ v)-
      (JetCoreDensity.compressed K α γ μ t (AxialFlow.foot (JetPrototype.sign a) α γ μ t x.2)*
        ψ (PlaneChart.join 0 (AxialFlow.velocity (JetPrototype.sign a) α γ μ t x.2)))*
      (∫ w, JetCoreDensity.dilatedMask (r n) η (s n/r n) (d n) t a x w*
        JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)) atTop (𝓝 0) := by
  intro r s d μ
  have hr (n) : 0 < r n := S.radius_pos hs₀ (E.indices n)
  have hs (n) : 0 < s n := DatumBounds.scale_pos hs₀ _
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hrlim : Tendsto r atTop (𝓝 0) :=
    (S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop
  have hslim : Tendsto (fun n => s n/r n) atTop (𝓝 μ) := E.coldLabel_scale_limit hs₀ hη k a
  have hdlim : Tendsto d atTop (𝓝 0) := E.coldLabel_width_tendsto_zero hs₀ hη k a
  have hclip : Tendsto (fun n => max (μ/2) (s n/r n)) atTop (𝓝 μ) := by
    have hm : Tendsto (fun n => max (μ/2) (s n/r n)) atTop (𝓝 (max (μ/2) μ)) :=
      tendsto_const_nhds.max hslim
    simpa only [max_eq_right (show μ/2 ≤ μ by linarith)] using hm
  have hbase := JetCoreDensity.dilated_free_thermal_reduction hr hK hα hγ
    (by positivity : 0 < μ/2) (fun n => le_max_left (μ/2) (s n/r n))
    (fun n => mul_pos hd₀ (pow_pos (hs n) 10)) hμ ht hrlim hclip hdlim hψ hψB η a x
  apply hbase.congr'
  filter_upwards [hslim.eventually (lt_mem_nhds (show μ/2 < μ by linarith))] with n hn
  rw [max_eq_right hn.le,mul_div_cancel₀ _ (hr n).ne']

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Spatial L1 thermal reduction for the actual retained-scale labels -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_thermal_L1_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 < t) {B : ℝ} {ψ : Velocity → ℝ}
    (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    let r := fun n => S.radius (E.indices n)
    let s := fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
    let d := fun n => d₀*(s n)^10
    let μ := E.phase*Real.exp (η*(k:ℝ))
    Tendsto (fun n => ∫ x, |(∫ v, r n*JetFreeTransport.free η K α γ (s n) (d n)
        (r n*t) a (r n • x,v)*ψ v)-
      JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
        (∫ w, JetCoreDensity.dilatedMask (r n) η (s n/r n) (d n) t a x w*
          JetThermalKernel.J (SheetMeasures.join w)
          ∂(volume : Measure Transverse).prod volume)| ∂ρ) atTop (𝓝 0) := by
  intro r s d μ
  let f : ℕ → JetPrototype.Space → ℝ := fun n x =>
    (∫ v, r n*JetFreeTransport.free η K α γ (s n) (d n) (r n*t) a (r n • x,v)*ψ v)-
      JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
        (∫ w, JetCoreDensity.dilatedMask (r n) η (s n/r n) (d n) t a x w*
          JetThermalKernel.J (SheetMeasures.join w)
          ∂(volume : Measure Transverse).prod volume)
  have hr (n) : 0 < r n := S.radius_pos hs₀ (E.indices n)
  have hs (n) : 0 < s n := DatumBounds.scale_pos hs₀ _
  have hd (n) : 0 < d n := mul_pos hd₀ (pow_pos (hs n) 10)
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hfm (n) : Measurable (f n) :=
    (JetCoreDensity.free_average_measurable (r n) η K α γ (s n) (d n) t a hψ.measurable).sub
      ((JetCoreDensity.limitingCoefficient_measurable hα.le hγ.le hμ ht.le K
        (JetPrototype.sign a) hψ).mul
          (JetCoreDensity.mask_average_measurable (r n) η (s n/r n) (d n) t a))
  have hl (x) : Tendsto (fun n => f n x) atTop (𝓝 0) :=
    E.coldLabel_thermal_limit hs₀ hη hK hα.le hγ.le hd₀ k a ht.le hψ hψB x
  let C := ((K*max 1 (α*γ)⁻¹)/t)*B
  have hb (n x) : |f n x| ≤ 2*C := by
    have hfree := JetCoreDensity.dilated_free_average_bound (hr n) hK hα hγ
      (hs n) (hd n) ht η a x hψ hψB
    have hc := JetCoreDensity.limitingCoefficient_bound hK hα hγ hμ ht hψB
      (JetPrototype.sign a) x
    have hm := JetCoreDensity.masked_thermal_bound
      (JetCoreDensity.dilatedMask_abs_le (r n) η (s n/r n) (d n) t a x)
    have hp : |JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x*
        (∫ w, JetCoreDensity.dilatedMask (r n) η (s n/r n) (d n) t a x w*
          JetThermalKernel.J (SheetMeasures.join w)
          ∂(volume : Measure Transverse).prod volume)| ≤ C := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) hm).trans hc
    exact (abs_sub _ _).trans ((add_le_add hfree hp).trans_eq (by dsimp [C] <;> ring))
  have h := tendsto_integral_of_dominated_convergence (μ := ρ)
    (F := fun n x => |f n x|) (f := fun _ => (0:ℝ)) (fun _ => 2*C)
    (fun n => (hfm n).abs.aestronglyMeasurable) (integrable_const _)
    (fun n => ae_of_all _ (fun x => by
      rw [Real.norm_of_nonneg (abs_nonneg _)]
      exact hb n x)) (ae_of_all _ (fun x => by simpa only [abs_zero] using (hl x).abs))
  simpa only [integral_zero] using h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual free-core average reduces to its limiting shell and fine stripes -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_free_striped_L1_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 < t) {B : ℝ} {ψ : Velocity → ℝ}
    (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (Ω : Set Transverse) (hΩ : volume Ω < ⊤) (ν : Measure ℝ) [IsFiniteMeasure ν] :
    Tendsto (fun n => ∫ x, |E.coldLabelFreeAverage k a n t ψ x-
      E.coldLabelStripedProfile k a n t ψ x| ∂(volume.restrict Ω).prod ν) atTop (𝓝 0) := by
  let _ : IsFiniteMeasure ((volume : Measure Transverse).restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hΩ⟩
  let ρ := (volume.restrict Ω).prod ν
  let r := fun n => S.radius (E.indices n)
  let s := fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
  let d := fun n => d₀*(s n)^10
  let μ := E.phase*Real.exp (η*(k:ℝ))
  let c := JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ
  let m := fun n x => ∫ w, JetCoreDensity.dilatedMask (r n) η (s n/r n) (d n) t a x w*
    JetThermalKernel.J (SheetMeasures.join w) ∂(volume : Measure Transverse).prod volume
  let e := fun n (x : JetPrototype.Space) => ∫ w,
    JetGeometry.maskError (r n) η (s n) (d n) μ t a (x.1,w)
    ∂(volume : Measure Transverse).prod volume
  let f := E.coldLabelFreeAverage k a
  let C := ((K*max 1 (α*γ)⁻¹)/t)*B
  have hr (n) : 0 < r n := S.radius_pos hs₀ (E.indices n)
  have hs (n) : 0 < s n := DatumBounds.scale_pos hs₀ _
  have hd (n) : 0 < d n := mul_pos hd₀ (pow_pos (hs n) 10)
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have htlim := E.coldLabel_thermal_L1_limit hs₀ hη hK hα hγ hd₀ k a ht hψ hψB ρ
  have hmlim := E.coldLabel_mask_average_limit hs₀ hη k a t Ω hΩ ν
  change Tendsto (fun n => ∫ x, |f n t ψ x-c x*m n x| ∂ρ) atTop (𝓝 0) at htlim
  change Tendsto (fun n => ∫ x, |e n x| ∂ρ) atTop (𝓝 0) at hmlim
  have hlim := htlim.add (hmlim.const_mul C)
  simp only [mul_zero,zero_add] at hlim
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) _ hlim
  intro n
  have hi₁ : Integrable (fun x => f n t ψ x-c x*m n x) ρ :=
    JetCoreDensity.thermal_error_integrable (hr n) hK hα hγ (hs n) (hd n) hμ ht η a hψ hψB ρ
  have hi₂ : Integrable (e n) ρ := E.coldLabel_mask_average_integrable k a n t Ω hΩ ν
  rw [← integral_const_mul,← integral_add hi₁.abs (hi₂.abs.const_mul C)]
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
    (hi₁.abs.add (hi₂.abs.const_mul C))
  filter_upwards [] with x
  have he : e n x = m n x-(JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1*
      E.coldLabelStripeAverage k a n t x.1 := by
    have hb := JetGeometry.maskError_average_eq (r n) η (s n/r n) (d n) μ t a x
    simp only [mul_div_cancel₀ _ (hr n).ne'] at hb
    simpa only [e,m,r,s,d,coldLabelStripeAverage] using hb
  have hid : f n t ψ x-E.coldLabelStripedProfile k a n t ψ x =
      (f n t ψ x-c x*m n x)+c x*e n x := by
    rw [he]
    change f n t ψ x-c x*((JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1*
      E.coldLabelStripeAverage k a n t x.1) = _
    ring
  rw [hid]
  apply (abs_add_le _ _).trans
  apply add_le_add le_rfl
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right
    (JetCoreDensity.limitingCoefficient_bound hK hα hγ hμ ht hψB (JetPrototype.sign a) x)
    (abs_nonneg _)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

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

/-! # The local weak limit is a limit of the physical, unextended cap shots -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.congr_eventually {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f k : ℕ → X → ℝ} {g : X → ℝ}
    (hg : WeakL1Converges μ f g) (he : ∀ᶠ n in atTop, f n =ᵐ[μ] k n) :
    WeakL1Converges μ k g := by
  refine ⟨hg.1,hg.2.1,?_⟩
  intro ψ hψ hB
  apply (hg.2.2 ψ hψ hB).congr'
  filter_upwards [he] with n hn
  exact integral_congr_ae (hn.mono (fun x hx => congrArg (fun y => ψ x*y) hx))

end BoltzmannNonuniqueness.Published

end

end

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

namespace AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem rescaledColdDensity_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) :
    Measurable (S.rescaledColdDensity n) := by
  have hc := ((F.approximation n).coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le).1
  have hm : Measurable (fun z : HotKineticPhase =>
      (S.radius n*z.1.1,(S.radius n • z.1.2,z.2))) := by fun_prop
  exact (((ChartKernel.measurable_H q).comp measurable_snd).const_mul _).mul (hc.comp hm)

theorem rescaledColdDensity_bounds (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (z : HotKineticPhase) :
    0 ≤ S.rescaledColdDensity n z ∧ S.rescaledColdDensity n z ≤
      (S.radius n*(2*(F.approximation n).amplitude))*H q z.2 := by
  have hc := ((F.approximation n).coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos n).le).2
      (S.radius n*z.1.1,(S.radius n • z.1.2,z.2))
  have hrH := mul_nonneg (S.radius_pos hs₀ n).le (H_nonneg q z.2)
  refine ⟨mul_nonneg hrH hc.2.1,?_⟩
  calc
    _ ≤ S.radius n*H q z.2*(2*(F.approximation n).amplitude) :=
      mul_le_mul_of_nonneg_left (hc.2.2.trans ((F.approximation n).solution.value_bounds _).2) hrH
    _ = _ := by ring

end AttainedCapSequence
end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteHorizonRatio
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite mesh representation of the atomic background on a radial window -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem AxialBackground.integral_cell_eq_sum {K α γ μ t : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (x : JetPrototype.Space) (ψ : Velocity → ℝ) :
    (∫ v, ψ v ∂AxialBackground.cell K α γ μ t x.2) =
      ∑ a : Bool, (1/4)*JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ x := by
  rw [AxialBackground.integral_cell hK hα hγ hμ ht]
  simp only [Fintype.sum_bool,JetPrototype.sign,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
  unfold AxialBackground.weight JetCoreDensity.limitingCoefficient
  ring

theorem GeometricBackground.integral_finite_window {θ η l K α γ t δ R : ℝ}
    (hθ₁ : 1 ≤ θ) (hθ₂ : θ ≤ Real.exp η) (hη : 0 < η) (hδ : 0 < δ)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (x : JetPrototype.Space) (hlo : δ ≤ ‖x.1‖) (hhi : ‖x.1‖ ≤ R) (ψ : Velocity → ℝ) :
    (∫ v, ψ v ∂background θ η l K α γ t x) =
      ∑ a : Bool, ∑ k ∈ Finset.Icc (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η),
        if l < GeometricMesh.point θ η k then
          JetCoreDensity.limitingCoefficient K α γ (GeometricMesh.point θ η k) t
            (JetPrototype.sign a) ψ x*
              ((JetGeometry.scaleShell η (GeometricMesh.point θ η k)).indicator
                (fun _ => (1:ℝ)) x.1*(1/4)) else 0 := by
  classical
  have hθ : 0 < θ := zero_lt_one.trans_le hθ₁
  by_cases ha : active θ η l x.1
  · let j := GeometricMesh.index (‖x.1‖/θ) η
    have hs : scale θ η x.1 = GeometricMesh.point θ η j := rfl
    have hy : x.1 ∈ JetGeometry.scaleShell η (GeometricMesh.point θ η j) := by
      simpa only [hs] using ha.2
    have hl : l < GeometricMesh.point θ η j := by simpa only [hs] using ha.1
    have hj := GeometricMesh.shell_index_window hθ₁ hθ₂ hη hδ hy hlo hhi
    rw [background_on_shell hθ hη hy hl,AxialBackground.integral_cell_eq_sum
      hK hα hγ (GeometricMesh.point_pos hθ η j) ht]
    apply Finset.sum_congr rfl
    intro a _
    symm
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left hl,indicator_of_mem hy]
      ring
    · intro k _ hkj
      have hn : x.1 ∉ JetGeometry.scaleShell η (GeometricMesh.point θ η k) := by
        intro hk
        exact hkj (GeometricMesh.shell_index hθ hη hk).symm
      simp only [indicator_of_notMem hn,zero_mul,mul_zero,ite_self]
    · intro hj'
      exact (hj' (Finset.mem_Icc.mpr hj)).elim
  · rw [background,ite_eq_right ha,integral_zero_measure]
    symm
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro k _
    by_cases hl : l < GeometricMesh.point θ η k
    · have hn : x.1 ∉ JetGeometry.scaleShell η (GeometricMesh.point θ η k) := by
        intro hk
        apply ha
        rw [active,scale_eq_of_shell hθ hη hk]
        exact ⟨hl,hk⟩
      simp only [hl,ite_true, if_true,indicator_of_notMem hn,zero_mul,mul_zero]
    · simp only [hl,ite_false, if_false]

end BoltzmannNonuniqueness

end

end

section

/-! # Finite sums of weak L1 limits -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.finset_sum {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} (s : Finset ι) {f : ι → ℕ → X → ℝ} {g : ι → X → ℝ}
    (h : ∀ i ∈ s, WeakL1Converges μ (f i) (g i))
    (hf : ∀ i ∈ s, ∀ n, Integrable (f i n) μ) :
    WeakL1Converges μ (fun n x => ∑ i ∈ s, f i n x) (fun x => ∑ i ∈ s, g i x) := by
  refine ⟨Finset.measurable_sum s (fun i hi => (h i hi).1),
    integrable_finsetSum s (fun i hi => (h i hi).2.1),?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have heq (u : ι → X → ℝ) (hu : ∀ i ∈ s, Integrable (u i) μ) :
      (∫ x, ψ x*(∑ i ∈ s, u i x) ∂μ) = ∑ i ∈ s, ∫ x, ψ x*u i x ∂μ := by
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum s (fun i hi =>
      (hu i hi).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC))
  have ht := tendsto_finsetSum s (fun i hi => (h i hi).2.2 ψ hψ ⟨C,hC⟩)
  simp_rw [heq (fun i => f i _) (fun i hi => hf i hi _),
    heq g (fun i hi => (h i hi).2.1)]
  exact ht

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_StripeCells
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact period and mean of the cold stripes -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetGeometry

theorem stripeAtPeriod_mem_iff (p : ℝ) (a : Bool) (y : VelocityWeight.Transverse) :
    y ∈ stripeAtPeriod p a ↔ y 0 ∈ stripeLine p a := Iff.rfl

theorem stripeLine_measurable (p : ℝ) (a : Bool) : MeasurableSet (stripeLine p a) := by
  unfold stripeLine
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion (fun k => measurableSet_Ioo)

theorem stripeLine_add_period (p x : ℝ) (a : Bool) :
    x+p ∈ stripeLine p a ↔ x ∈ stripeLine p a := by
  constructor
  · rintro ⟨k,hk₁,hk₂⟩
    refine ⟨k-1,?_,?_⟩ <;> push_cast <;> nlinarith
  · rintro ⟨k,hk₁,hk₂⟩
    refine ⟨k+1,?_,?_⟩ <;> push_cast <;> nlinarith

theorem stripeLine_indicator_periodic (p : ℝ) (a : Bool) :
    Function.Periodic ((stripeLine p a).indicator (fun _ => (1:ℝ))) p := by
  intro x
  classical
  by_cases hx : x ∈ stripeLine p a
  · rw [indicator_of_mem hx,indicator_of_mem ((stripeLine_add_period p x a).mpr hx)]
  · rw [indicator_of_notMem hx,indicator_of_notMem (mt (stripeLine_add_period p x a).mp hx)]

theorem stripeLine_on_cell {p : ℝ} (hp : 0 < p) (a : Bool) {x : ℝ}
    (hx : x ∈ Ioc 0 p) :
    x ∈ stripeLine p a ↔ x ∈ Ioo ((if a then 0 else 1/2)*p)
      (((if a then 0 else 1/2)+1/4)*p) := by
  constructor
  · rintro ⟨k,hk₁,hk₂⟩
    have hc₀ : (0:ℝ) ≤ (if a then 0 else 1/2) := by split <;> norm_num
    have hc₁ : (if a then 0 else 1/2) ≤ (3/4:ℝ) := by split <;> norm_num
    have hk : k = 0 := by
      rcases lt_trichotomy k 0 with hn | hz | hn
      · have hn' : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        have hmul := mul_nonpos_of_nonpos_of_nonneg
          (show (k:ℝ)+(if a then 0 else 1/2)+1/4 ≤ 0 by linarith) hp.le
        linarith [hx.1]
      · exact hz
      · have hn' : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
        have hmul := mul_le_mul_of_nonneg_right
          (show (1:ℝ) ≤ (k:ℝ)+(if a then 0 else 1/2) by linarith) hp.le
        linarith [hx.2]
    simpa only [hk,Int.cast_zero,zero_add,mem_Ioo] using And.intro hk₁ hk₂
  · intro hx
    exact ⟨0,by simpa using hx.1,by simpa using hx.2⟩

theorem stripeLine_integral_period {p : ℝ} (hp : 0 < p) (a : Bool) :
    (∫ x in 0..p, (stripeLine p a).indicator (fun _ => (1:ℝ)) x) = p/4 := by
  let c : ℝ := if a then 0 else 1/2
  have hc₀ : 0 ≤ c := by dsimp [c]; split <;> norm_num
  have hc₁ : c+1/4 ≤ (1:ℝ) := by dsimp [c]; split <;> norm_num
  have hsub : Ioo (c*p) ((c+1/4)*p) ⊆ Ioc 0 p := by
    intro x hx
    exact ⟨(mul_nonneg hc₀ hp.le).trans_lt hx.1,
      hx.2.le.trans (by nlinarith)⟩
  rw [intervalIntegral.integral_of_le hp.le]
  calc
    _ = ∫ x in Ioc 0 p, (Ioo (c*p) ((c+1/4)*p)).indicator (fun _ => (1:ℝ)) x := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      classical
      by_cases hy : x ∈ stripeLine p a
      · rw [indicator_of_mem hy,indicator_of_mem ((stripeLine_on_cell hp a hx).mp hy)]
      · rw [indicator_of_notMem hy,indicator_of_notMem (mt (stripeLine_on_cell hp a hx).mpr hy)]
    _ = volume.real (Ioo (c*p) ((c+1/4)*p) ∩ Ioc 0 p) := by
      rw [integral_indicator_const (1:ℝ) measurableSet_Ioo,smul_eq_mul,mul_one,
        measureReal_restrict_apply measurableSet_Ioo]
    _ = p/4 := by
      rw [inter_eq_left.mpr hsub,Real.volume_real_Ioo]
      rw [max_eq_left (by nlinarith : 0 ≤ (c+1/4)*p-c*p)]
      ring

end BoltzmannNonuniqueness.JetGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ShiftedStripe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Centered stripe estimates uniform in spatial phase -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetGeometry

theorem centeredStripe_measurable (p d : ℝ) (a : Bool) :
    Measurable (centeredStripe p d a) :=
  (((measurable_const.indicator (stripeLine_measurable p a)).comp
    (measurable_id.sub_const d)).sub_const (1/4))

theorem centeredStripe_bound (p d : ℝ) (a : Bool) (x : ℝ) :
    |centeredStripe p d a x| ≤ 1 := by
  classical
  by_cases hx : x-d ∈ stripeLine p a <;> simp [centeredStripe,hx] <;> norm_num

theorem centeredStripe_periodic (p d : ℝ) (a : Bool) :
    Function.Periodic (centeredStripe p d a) p := by
  intro x
  have h := stripeLine_indicator_periodic p a (x-d)
  simpa only [centeredStripe,add_sub_right_comm] using congrArg (fun z : ℝ => z-1/4) h

theorem centeredStripe_mean {p : ℝ} (hp : 0 < p) (d : ℝ) (a : Bool) :
    (∫ x in 0..p, centeredStripe p d a x) = 0 := by
  let f := (stripeLine p a).indicator (fun _ => (1:ℝ))
  have hm : Measurable (fun x => f (x-d)) :=
    (measurable_const.indicator (stripeLine_measurable p a)).comp (measurable_id.sub_const d)
  have hb (x : ℝ) : |f (x-d)| ≤ 1 := by
    classical
    by_cases hx : x-d ∈ stripeLine p a <;> simp [f,hx]
  have hi := PeriodicAveraging.bounded_intervalIntegrable hm hb 0 p
  change (∫ x in 0..p, f (x-d)-1/4) = 0
  rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_comp_sub_right,intervalIntegral.integral_const]
  have heq : p-d = (0-d)+p := by ring
  rw [heq,(stripeLine_indicator_periodic p a).intervalIntegral_add_eq (0-d) 0,zero_add,
    stripeLine_integral_period hp a]
  simp only [sub_zero,smul_eq_mul]
  ring

end BoltzmannNonuniqueness.JetGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_TransverseStripeWeak
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Stripe averaging on the transverse plane and additional fibers -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem transverseCartesian_measurePreserving : MeasurePreserving transverseCartesian :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).trans
    (volume_preserving_finTwoArrow ℝ)

theorem centeredStripe_weakStar {p : ℕ → ℝ} (hp : ∀ n, 0 < p n)
    (hplim : Tendsto p atTop (𝓝 0)) (d : ℕ → ℝ) (σ : Bool) :
    Compactness.WeakStarLInfConverges volume
      (fun n x => centeredStripe (p n) (d n) σ x) (fun _ => 0) :=
  PeriodicAveraging.weakStar_zero hp hplim
    (fun n => centeredStripe_periodic (p n) (d n) σ)
    (fun n => centeredStripe_measurable (p n) (d n) σ)
    (fun n => centeredStripe_bound (p n) (d n) σ)
    (fun n => centeredStripe_mean (hp n) (d n) σ)

theorem centeredStripe_transverse_weakStar {p : ℕ → ℝ} (hp : ∀ n, 0 < p n)
    (hplim : Tendsto p atTop (𝓝 0)) (d : ℕ → ℝ) (σ : Bool) :
    Compactness.WeakStarLInfConverges (volume : Measure Transverse)
      (fun n y => centeredStripe (p n) (d n) σ (y 0)) (fun _ => 0) := by
  have hprod : Compactness.WeakStarLInfConverges
      ((volume : Measure ℝ).prod volume)
      (fun n (z : ℝ × ℝ) => centeredStripe (p n) (d n) σ z.1) (fun _ => 0) :=
    Compactness.weakStar_zero_of_fibers
      (fun n => (centeredStripe_measurable (p n) (d n) σ).comp measurable_fst)
      (fun n z => centeredStripe_bound (p n) (d n) σ z.1)
      (fun _ => centeredStripe_weakStar hp hplim d σ)
  exact hprod.comp_measurableEquiv transverseCartesian transverseCartesian_measurePreserving

theorem centeredStripe_fiber_weakStar {W : Type*} [MeasurableSpace W]
    (ν : Measure W) [SFinite ν] {p : ℕ → ℝ} (hp : ∀ n, 0 < p n)
    (hplim : Tendsto p atTop (𝓝 0)) {d : ℕ → W → ℝ} (hd : ∀ n, Measurable (d n)) (σ : Bool) :
    Compactness.WeakStarLInfConverges ((volume : Measure Transverse).prod ν)
      (fun n z => centeredStripe (p n) (d n z.2) σ (z.1 0)) (fun _ => 0) := by
  apply Compactness.weakStar_zero_of_fibers
  · intro n
    have hm : Measurable (fun z : Transverse × W => z.1 0-d n z.2) :=
      (by fun_prop : Measurable (fun z : Transverse × W => z.1 0)).sub ((hd n).comp measurable_snd)
    exact ((measurable_const.indicator (stripeLine_measurable (p n) σ)).comp hm).sub_const (1/4)
  · intro n z
    exact centeredStripe_bound (p n) (d n z.2) σ (z.1 0)
  · intro w
    exact centeredStripe_transverse_weakStar hp hplim (fun n => d n w) σ

end BoltzmannNonuniqueness.JetGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ThermalStripeIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Weak averaging after the Gaussian thermal mixture -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem thermalStripeCentered_bound (p d t : ℝ) (a : Bool) (y : Transverse) :
    |thermalStripeCentered p d t a y| ≤ 1 :=
  JetCoreDensity.masked_thermal_bound (fun w => centeredStripe_bound p (t*d*w.1 0) a (y 0))

theorem thermalStripeCentered_weakStar {p : ℕ → ℝ} (hp : ∀ n, 0 < p n)
    (hplim : Tendsto p atTop (𝓝 0)) (d : ℕ → ℝ) (t : ℝ) (a : Bool) :
    Compactness.WeakStarLInfConverges (volume : Measure Transverse)
      (fun n => thermalStripeCentered (p n) (d n) t a) (fun _ => 0) := by
  let ν := (volume : Measure Transverse).prod (volume : Measure ℝ)
  let J : Transverse × ℝ → ℝ := fun w => JetThermalKernel.J (SheetMeasures.join w)
  let g : ℕ → Transverse × (Transverse × ℝ) → ℝ :=
    fun n z => centeredStripe (p n) (t*d n*z.2.1 0) a (z.1 0)
  have hw := centeredStripe_fiber_weakStar ν hp hplim
    (d := fun n (w : Transverse × ℝ) => t*d n*w.1 0) (by intro n; fun_prop) a
  have hJ : Integrable J ν := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  have hgm (n) : Measurable (g n) :=
    ((measurable_const.indicator (stripeLine_measurable (p n) a)).comp
      (by fun_prop)).sub_const (1/4)
  refine ⟨measurable_const,?_⟩
  intro ψ hψ
  have hi (n) : Integrable (fun z : Transverse × (Transverse × ℝ) =>
      (ψ z.1*J z.2)*g n z) ((volume : Measure Transverse).prod ν) := by
    exact ((hψ.mul_prod hJ).bdd_mul (hgm n).aestronglyMeasurable
      (ae_of_all _ (fun z => centeredStripe_bound (p n) (t*d n*z.2.1 0) a (z.1 0)))).congr
        (ae_of_all _ (fun z => mul_comm _ _))
  have heq (n) : (∫ z, (ψ z.1*J z.2)*g n z ∂(volume : Measure Transverse).prod ν) =
      ∫ y, ψ y*thermalStripeCentered (p n) (d n) t a y := by
    rw [integral_prod _ (hi n)]
    apply integral_congr_ae
    filter_upwards [] with y
    unfold thermalStripeCentered
    rw [← integral_const_mul]
    congr 1
    funext w
    change (ψ y*J w)*g n (y,w) = ψ y*(g n (y,w)*J w)
    ring
  have ht := hw.2 (fun z => ψ z.1*J z.2) (hψ.mul_prod hJ)
  simp only [mul_zero,integral_zero] at ht ⊢
  change Tendsto (fun n => ∫ z, (ψ z.1*J z.2)*g n z
    ∂(volume : Measure Transverse).prod ν) atTop (𝓝 0) at ht
  simpa only [heq] using ht

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # The physical stripe and its centered Gaussian mixture -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

theorem stripe_dilated_indicator {r : ℝ} (hr : 0 < r) (s : ℝ) (a : Bool) (y : Transverse) :
    (stripe s a).indicator (fun _ => (1:ℝ)) (r • y) =
      (stripeLine (r*(s/r)^2) a).indicator (fun _ => (1:ℝ)) (y 0) := by
  classical
  have hi := stripe_dilation hr (s/r) a y
  rw [mul_div_cancel₀ _ hr.ne'] at hi
  rw [stripeAtPeriod_mem_iff] at hi
  by_cases hy : r • y ∈ stripe s a
  · rw [indicator_of_mem hy,indicator_of_mem (hi.mp hy)]
  · rw [indicator_of_notMem hy,indicator_of_notMem (mt hi.mpr hy)]

theorem thermalStripeCentered_eq {r : ℝ} (hr : 0 < r) (s d t : ℝ) (a : Bool)
    (y : Transverse) :
    thermalStripeCentered (r*(s/r)^2) d t a y =
      (∫ w : Transverse × ℝ, (stripe s a).indicator (fun _ => (1:ℝ))
        (r • (y-t • (d • w.1)))*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)-1/4 := by
  let ν := (volume : Measure Transverse).prod (volume : Measure ℝ)
  let χ : Transverse × ℝ → ℝ := fun w =>
    (stripe s a).indicator (fun _ => (1:ℝ)) (r • (y-t • (d • w.1)))
  let J : Transverse × ℝ → ℝ := fun w => JetThermalKernel.J (SheetMeasures.join w)
  have hJ : Integrable J ν := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  have hχm : Measurable χ :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_stripe s a)).comp (by fun_prop)
  have hχ (w) : |χ w| ≤ 1 := by
    classical
    by_cases hw : r • (y-t • (d • w.1)) ∈ stripe s a <;> simp [χ,hw]
  have hi := hJ.bdd_mul hχm.aestronglyMeasurable (ae_of_all _ hχ)
  have heq (w : Transverse × ℝ) :
      centeredStripe (r*(s/r)^2) (t*d*w.1 0) a (y 0) = χ w-1/4 := by
    dsimp only [centeredStripe,χ]
    rw [stripe_dilated_indicator hr]
    congr 2
    change y 0-t*d*w.1 0 = y 0-t*(d*w.1 0)
    ring
  unfold thermalStripeCentered
  simp_rw [heq,sub_mul]
  rw [integral_sub hi (hJ.const_mul (1/4)),integral_const_mul,JetCoreDensity.thermal_integral_one,mul_one]

end BoltzmannNonuniqueness.JetGeometry

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

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Integrability of the actual, free and striped cold averages -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelStripeAverage_measurable (E : HotLimitExtraction S)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) : Measurable (E.coldLabelStripeAverage k a n t) := by
  let r := S.radius (E.indices n)
  let s := JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
  have hm : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (JetGeometry.stripe s a).indicator (fun _ => (1:ℝ))
        (r • (p.1-t • ((d₀*s^10) • p.2.1)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_stripe s a)).comp (by fun_prop)
  exact (hm.mul ((JetThermalKernel.J_smooth.continuous.measurable.comp
    SheetMeasures.join.measurable).comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

theorem HotLimitExtraction.coldLabelStripeAverage_bound (E : HotLimitExtraction S)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) (y : Transverse) :
    |E.coldLabelStripeAverage k a n t y| ≤ 1 := by
  apply JetCoreDensity.masked_thermal_bound
  intro w
  by_cases h : S.radius (E.indices n) •
      (y-t • ((d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10) • w.1)) ∈
      JetGeometry.stripe (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus) a
  · simp only [indicator_of_mem h,abs_one,le_refl]
  · simp only [indicator_of_notMem h,abs_zero,zero_le_one]

theorem HotLimitExtraction.coldLabelStripedProfile_measurable (E : HotLimitExtraction S)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    Measurable (E.coldLabelStripedProfile k a n t ψ) := by
  have hμ : 0 < E.phase*Real.exp (η*(k:ℝ)) :=
    mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  exact (JetCoreDensity.limitingCoefficient_measurable hα hγ hμ ht K (JetPrototype.sign a) hψ).mul
    (((measurable_const.indicator (JetGeometry.measurableSet_scaleShell η
      (E.phase*Real.exp (η*(k:ℝ))))).comp measurable_fst).mul
        ((E.coldLabelStripeAverage_measurable k a n t).comp measurable_fst))

theorem HotLimitExtraction.coldLabelStripedProfile_bound (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 < t)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) (x : JetPrototype.Space) :
    |E.coldLabelStripedProfile k a n t ψ x| ≤ ((K*max 1 (α*γ)⁻¹)/t)*B := by
  have hμ : 0 < E.phase*Real.exp (η*(k:ℝ)) :=
    mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hc := JetCoreDensity.limitingCoefficient_bound hK hα hγ hμ ht hψB (JetPrototype.sign a) x
  have hs := E.coldLabelStripeAverage_bound k a n t x.1
  dsimp only [coldLabelStripedProfile]
  by_cases hx : x.1 ∈ JetGeometry.scaleShell η (E.phase*Real.exp (η*(k:ℝ)))
  · rw [indicator_of_mem hx,one_mul,abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hs).trans hc
  · rw [indicator_of_notMem hx,zero_mul,mul_zero,abs_zero]
    exact (abs_nonneg _).trans hc

theorem HotLimitExtraction.coldLabelStripedProfile_integrable (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 < t)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    Integrable (E.coldLabelStripedProfile k a n t ψ) ρ :=
  Integrable.of_bound (E.coldLabelStripedProfile_measurable hα.le hγ.le k a n ht.le hψ).aestronglyMeasurable
    _ (ae_of_all _ (fun x => E.coldLabelStripedProfile_bound hK hα hγ k a n ht hψB x))

theorem HotLimitExtraction.coldLabelFreeAverage_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (k : ℤ) (a : Bool) (n : ℕ) {t : ℝ} (ht : 0 < t)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    Integrable (E.coldLabelFreeAverage k a n t ψ) ρ := by
  have hs : 0 < JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus := DatumBounds.scale_pos hs₀ _
  apply Integrable.of_bound
    (JetCoreDensity.free_average_measurable _ _ _ _ _ _ _ _ _ hψ.measurable).aestronglyMeasurable
    (((K*max 1 (α*γ)⁻¹)/t)*B)
  exact ae_of_all _ (fun x => JetCoreDensity.dilated_free_average_bound (S.radius_pos hs₀ _) hK hα hγ
    hs (mul_pos hd₀ (pow_pos hs 10)) ht η a x hψ hψB)

theorem HotLimitExtraction.coldLabelAverage_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) (Ω : Set JetPrototype.Space) (hΩ : IsCompact Ω)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Integrable (E.coldLabelAverage k a n t ψ) (JetPrototype.spaceVolume.restrict Ω) := by
  have hi := (E.coldLabelDensity_integrable hs₀ hsmax hη hηmax hK hd₀ hq k a n t Ω hΩ).bdd_mul
    (hψ.comp measurable_snd).aestronglyMeasurable (ae_of_all _ (fun p => hψB p.2))
  exact hi.integral_prod_left

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual cold-label stripes average to one quarter -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelStripe_centered_eq (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) (y : Transverse) :
    E.coldLabelStripeAverage k a n t y-1/4 =
      JetGeometry.thermalStripeCentered
        (S.radius (E.indices n)*
          (JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus/S.radius (E.indices n))^2)
        (d₀*(JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus)^10) t a y :=
  (JetGeometry.thermalStripeCentered_eq (S.radius_pos hs₀ _) _ _ _ _ _).symm

theorem HotLimitExtraction.coldLabelStripe_centered_weakStar (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) (t : ℝ) :
    Compactness.WeakStarLInfConverges (volume : Measure Transverse)
      (fun n y => E.coldLabelStripeAverage k a n t y-1/4) (fun _ => 0) := by
  let r := fun n => S.radius (E.indices n)
  let s := fun n => JetGeometry.jetScale s₀ η (E.coldLabel k a n).annulus
  have hr (n) : 0 < r n := S.radius_pos hs₀ _
  have hs (n) : 0 < s n := DatumBounds.scale_pos hs₀ _
  have hp (n) : 0 < r n*(s n/r n)^2 := mul_pos (hr n) (pow_pos (div_pos (hs n) (hr n)) 2)
  have hplim := JetGeometry.stripe_period_tendsto_zero
    ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop)
    (E.coldLabel_scale_limit hs₀ hη k a)
  have h := JetGeometry.thermalStripeCentered_weakStar hp hplim
    (fun n => d₀*(s n)^10) t a
  have heq : (fun n y => E.coldLabelStripeAverage k a n t y-1/4) =
      (fun n => JetGeometry.thermalStripeCentered (r n*(s n/r n)^2) (d₀*(s n)^10) t a) := by
    funext n y
    exact E.coldLabelStripe_centered_eq hs₀ k a n t y
  rw [heq]
  exact h

theorem HotLimitExtraction.coldLabelStripe_space_centered_weakStar (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (k : ℤ) (a : Bool) (t : ℝ) :
    Compactness.WeakStarLInfConverges JetPrototype.spaceVolume
      (fun n x => E.coldLabelStripeAverage k a n t x.1-1/4) (fun _ => 0) := by
  apply Compactness.weakStar_zero_of_fibers
  · intro n
    exact ((E.coldLabelStripeAverage_measurable k a n t).comp measurable_fst).sub_const (1/4)
  · intro n x
    rw [E.coldLabelStripe_centered_eq hs₀]
    exact JetGeometry.thermalStripeCentered_bound _ _ _ _ _
  · intro _
    exact E.coldLabelStripe_centered_weakStar hs₀ hη k a t

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Every actual cold-label velocity fiber is integrable -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelDensity_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ) :
    Measurable (E.coldLabelDensity k a n t) := by
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  have hp : Measurable (fun p : JetPrototype.Phase =>
      (S.radius (E.indices n)*t,(S.radius (E.indices n) • p.1,p.2))) := by fun_prop
  exact (((ChartKernel.measurable_H q).comp measurable_snd).mul ((hc.1 _).comp hp)).const_mul _

theorem HotLimitExtraction.coldLabelDensity_bounds (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ)
    (p : JetPrototype.Phase) :
    0 ≤ E.coldLabelDensity k a n t p ∧ E.coldLabelDensity k a n t p ≤
      (S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude))*H q p.2 := by
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  have hb := (hc.2.2.1 {E.coldLabel k a n}
    (S.radius (E.indices n)*t,(S.radius (E.indices n) • p.1,p.2))).trans
      ((F.approximation (E.indices n)).solution.value_bounds _).2
  simp only [Finset.sum_singleton] at hb
  have hrH := mul_nonneg (S.radius_pos hs₀ (E.indices n)).le (H_nonneg q p.2)
  refine ⟨mul_nonneg (S.radius_pos hs₀ _).le (mul_nonneg (H_nonneg q p.2) (hc.2.1 _ _)),?_⟩
  calc
    _ = S.radius (E.indices n)*H q p.2*
        (F.approximation (E.indices n)).cold (E.coldLabel k a n)
          (S.radius (E.indices n)*t,(S.radius (E.indices n) • p.1,p.2)) := by
      dsimp [coldLabelDensity]
      ring
    _ ≤ S.radius (E.indices n)*H q p.2*(2*(F.approximation (E.indices n)).amplitude) :=
      mul_le_mul_of_nonneg_left hb hrH
    _ = _ := by ring

theorem HotLimitExtraction.coldLabelDensity_fiber_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ) (t : ℝ)
    (x : JetPrototype.Space) : Integrable (fun v => E.coldLabelDensity k a n t (x,v)) := by
  have hm : Measurable (fun v => E.coldLabelDensity k a n t (x,v)) :=
    (E.coldLabelDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq k a n t).comp
    (measurable_const.prodMk measurable_id)
  apply ((integrable_H hq).const_mul
    (S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude))).mono' hm.aestronglyMeasurable
  filter_upwards [] with v
  have hb := E.coldLabelDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq k a n t (x,v)
  simpa only [Real.norm_of_nonneg hb.1] using hb.2

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The limiting average of an individual cold label -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelLimitProfile_measurable (E : HotLimitExtraction S)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 ≤ t)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    Measurable (E.coldLabelLimitProfile k a t ψ) := by
  have hμ : 0 < E.phase*Real.exp (η*(k:ℝ)) :=
    mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  exact (JetCoreDensity.limitingCoefficient_measurable hα hγ hμ ht K (JetPrototype.sign a) hψ).mul
    (((measurable_const.indicator (JetGeometry.measurableSet_scaleShell η
      (E.phase*Real.exp (η*(k:ℝ))))).comp measurable_fst).mul_const (1/4))

theorem HotLimitExtraction.coldLabelLimitProfile_bound (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 < t)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) (x : JetPrototype.Space) :
    |E.coldLabelLimitProfile k a t ψ x| ≤ ((K*max 1 (α*γ)⁻¹)/t)*B := by
  have hμ : 0 < E.phase*Real.exp (η*(k:ℝ)) :=
    mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hc := JetCoreDensity.limitingCoefficient_bound hK hα hγ hμ ht hψB (JetPrototype.sign a) x
  have hm : |(JetGeometry.scaleShell η (E.phase*Real.exp (η*(k:ℝ)))).indicator
      (fun _ => (1:ℝ)) x.1*(1/4)| ≤ 1 := by
    classical
    by_cases hx : x.1 ∈ JetGeometry.scaleShell η (E.phase*Real.exp (η*(k:ℝ))) <;> norm_num [hx]
  unfold coldLabelLimitProfile
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) hm).trans hc

theorem HotLimitExtraction.coldLabelLimitProfile_integrable (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 < t)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    Integrable (E.coldLabelLimitProfile k a t ψ) ρ :=
  Integrable.of_bound (E.coldLabelLimitProfile_measurable hα.le hγ.le k a ht.le hψ).aestronglyMeasurable
    _ (ae_of_all _ (fun x => E.coldLabelLimitProfile_bound hK hα hγ k a ht hψB x))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Removing the stripes from an individual cold-label profile -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_striped_weak_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (k : ℤ) (a : Bool) {t : ℝ} (ht : 0 < t)
    (Ω : Set JetPrototype.Space) (hΩ : MeasurableSet Ω) (hΩfin : JetPrototype.spaceVolume Ω < ⊤)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges (JetPrototype.spaceVolume.restrict Ω)
      (fun n => E.coldLabelStripedProfile k a n t ψ) (E.coldLabelLimitProfile k a t ψ) := by
  let ρ := JetPrototype.spaceVolume.restrict Ω
  let _ : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr hΩfin.ne
  let μ := E.phase*Real.exp (η*(k:ℝ))
  let c := JetCoreDensity.limitingCoefficient K α γ μ t (JetPrototype.sign a) ψ
  let m : JetPrototype.Space → ℝ := fun x =>
    (JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) x.1
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hcm : Measurable c := JetCoreDensity.limitingCoefficient_measurable
    hα.le hγ.le hμ ht.le K (JetPrototype.sign a) hψ
  have hci : Integrable c ρ := Integrable.of_bound hcm.aestronglyMeasurable _
    (ae_of_all _ (fun x => JetCoreDensity.limitingCoefficient_bound hK hα hγ hμ ht hψB _ x))
  have hmm : Measurable m :=
    (measurable_const.indicator (JetGeometry.measurableSet_scaleShell η μ)).comp measurable_fst
  have hmb (x) : |m x| ≤ 1 := by
    classical
    by_cases hx : x.1 ∈ JetGeometry.scaleShell η μ <;> simp [m,hx]
  have hli := E.coldLabelLimitProfile_integrable hK hα hγ k a ht hψ hψB ρ
  refine ⟨E.coldLabelLimitProfile_measurable hα.le hγ.le k a ht.le hψ,hli,?_⟩
  intro φ hφ hφB
  obtain ⟨D,hD⟩ := hφB
  let χ : JetPrototype.Space → ℝ := fun x => φ x*(m x*c x)
  have hχi : Integrable χ ρ :=
    (hci.bdd_mul hmm.aestronglyMeasurable (ae_of_all _ hmb)).bdd_mul
      hφ.aestronglyMeasurable (ae_of_all _ hD)
  have hzero := ((E.coldLabelStripe_space_centered_weakStar hs₀ hη k a t).restrict hΩ).2 χ hχi
  have hi (n) := (E.coldLabelStripedProfile_integrable hK hα hγ k a n ht hψ hψB ρ).bdd_mul
    hφ.aestronglyMeasurable (ae_of_all _ hD)
  have hl := hli.bdd_mul hφ.aestronglyMeasurable (ae_of_all _ hD)
  have heq (n) : (∫ x, χ x*(E.coldLabelStripeAverage k a n t x.1-1/4) ∂ρ) =
      (∫ x, φ x*E.coldLabelStripedProfile k a n t ψ x ∂ρ)-
        (∫ x, φ x*E.coldLabelLimitProfile k a t ψ x ∂ρ) := by
    rw [← integral_sub (hi n) hl]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [χ,m,c,μ,coldLabelStripedProfile,coldLabelLimitProfile]
    ring
  simp only [mul_zero,integral_zero] at hzero
  change Tendsto (fun n => ∫ x, χ x*(E.coldLabelStripeAverage k a n t x.1-1/4) ∂ρ)
    atTop (𝓝 0) at hzero
  simp_rw [heq] at hzero
  simpa only [zero_add,sub_add_cancel] using
    hzero.add_const (∫ x, φ x*E.coldLabelLimitProfile k a t ψ x ∂ρ)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Joint measurability and positive-time bounds of the atomic label limits -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelLimitProfile_clamped_measurable (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (k : ℤ) (a : Bool)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun z : ℝ × JetPrototype.Space => E.coldLabelLimitProfile k a (max 0 z.1) ψ z.2) := by
  let μ := E.phase*Real.exp (η*(k:ℝ))
  have hμ : 0 < μ := mul_pos (zero_lt_one.trans_le E.phase_mem.1) (Real.exp_pos _)
  have hmA := (AxialBackground.clamped_atom_test_measurable hK hα hγ hμ (JetPrototype.sign a) hψ).comp
    (measurable_fst.prodMk measurable_snd.snd :
      Measurable (fun z : ℝ × JetPrototype.Space => (z.1,z.2.2)))
  have hmS : Measurable (fun z : ℝ × JetPrototype.Space =>
      (JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) z.2.1) :=
    (measurable_const.indicator (JetGeometry.measurableSet_scaleShell η μ)).comp measurable_snd.fst
  have heq : (fun z : ℝ × JetPrototype.Space => E.coldLabelLimitProfile k a (max 0 z.1) ψ z.2) =
      (fun z => (JetGeometry.scaleShell η μ).indicator (fun _ => (1:ℝ)) z.2.1*
        (∫ v, ψ v ∂AxialBackground.atom K α γ μ (max 0 z.1) (JetPrototype.sign a) z.2.2)) := by
    funext z
    rw [AxialBackground.integral_atom hK hα hγ hμ (le_max_left _ _)]
    unfold coldLabelLimitProfile AxialBackground.weight JetCoreDensity.limitingCoefficient
    dsimp only [μ]
    ring
  rw [heq]
  exact hmS.mul hmA

theorem HotLimitExtraction.coldLabelLimitProfile_slab_bound (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (σ : Bool)
    {a t B : ℝ} (ha : 0 < a) (ht : a ≤ t) {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B)
    (x : JetPrototype.Space) :
    |E.coldLabelLimitProfile k σ t ψ x| ≤ ((K*max 1 (α*γ)⁻¹)/a)*B := by
  have hb := E.coldLabelLimitProfile_bound hK hα hγ k σ (ha.trans_le ht) hψB x
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  exact hb.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha ht) hB)

theorem HotLimitExtraction.coldLabelLimitProfile_clamped_integrable (E : HotLimitExtraction S)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (k : ℤ) (σ : Bool)
    {a A B : ℝ} (ha : 0 < a) {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure JetPrototype.Space) [IsFiniteMeasure ρ] :
    Integrable (fun z => E.coldLabelLimitProfile k σ (max 0 z.1) ψ z.2)
      ((volume.restrict (Icc a A)).prod ρ) := by
  apply Integrable.of_bound
    (E.coldLabelLimitProfile_clamped_measurable hK hα.le hγ.le k σ hψ).aestronglyMeasurable
    (((K*max 1 (α*γ)⁻¹)/a)*B)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz
  rw [Real.norm_eq_abs,max_eq_right (ha.le.trans hz.1)]
  exact E.coldLabelLimitProfile_slab_bound hK hα hγ k σ ha hz.1 hψB z.2

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Actual cold averages converge to the shell-weighted stripe averages -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_actual_striped_L1_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (k : ℤ) (a : Bool) (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω₁ : Set Transverse) (hΩ₁ : IsCompact Ω₁) (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Tendsto (fun n => ∫ x, |E.coldLabelAverage k a n t ψ x-E.coldLabelStripedProfile k a n t ψ x|
      ∂JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)) atTop (𝓝 0) := by
  let Ω := Ω₁ ×ˢ Ω₂
  have hΩ : IsCompact Ω := hΩ₁.prod hΩ₂
  let ρ := JetPrototype.spaceVolume.restrict Ω
  let _ : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr hΩ.measure_lt_top.ne
  let _ : IsFiniteMeasure ((volume : Measure ℝ).restrict Ω₂) :=
    isFiniteMeasure_restrict.mpr hΩ₂.measure_lt_top.ne
  have hactual := E.coldLabel_average_free_L1_limit_q80 hs₀ hsmax hη hηmax hK hα.le hαmax hγ.le
    hd₀ hd₀max hsmall hq k a hk ht htU Ω hΩ hψ.measurable hψB
  have hfree := E.coldLabel_free_striped_L1_limit hs₀ hη hK hα hγ hd₀ k a ht hψ hψB
    Ω₁ hΩ₁.measure_lt_top (volume.restrict Ω₂)
  rw [Measure.prod_restrict] at hfree
  have hlim := hactual.add hfree
  simp only [zero_add] at hlim
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => abs_nonneg _)) _ hlim
  intro n
  have hiA := E.coldLabelAverage_integrable hs₀ hsmax hη hηmax hK hd₀.le hq k a n t Ω hΩ
    hψ.measurable hψB
  have hiF := E.coldLabelFreeAverage_integrable hs₀ hK hα hγ hd₀ k a n ht hψ hψB ρ
  have hiS := E.coldLabelStripedProfile_integrable hK hα hγ k a n ht hψ hψB ρ
  have hsum : (∫ x, |E.coldLabelAverage k a n t ψ x-E.coldLabelFreeAverage k a n t ψ x|+
      |E.coldLabelFreeAverage k a n t ψ x-E.coldLabelStripedProfile k a n t ψ x| ∂ρ) =
      (∫ x, |E.coldLabelAverage k a n t ψ x-E.coldLabelFreeAverage k a n t ψ x| ∂ρ)+
      (∫ x, |E.coldLabelFreeAverage k a n t ψ x-E.coldLabelStripedProfile k a n t ψ x| ∂ρ) :=
    integral_add (hiA.sub hiF).abs (hiF.sub hiS).abs
  rw [← hsum]
  apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _))
    ((hiA.sub hiF).abs.add (hiF.sub hiS).abs)
  exact ae_of_all _ (fun x => abs_sub_le _ _ _)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The weak limit of an actual retained cold label -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_weak_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (k : ℤ) (a : Bool) (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {t : ℝ} (ht : 0 < t) (htU : ENNReal.ofReal t < E.horizon)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂))
      (fun n => E.coldLabelAverage k a n t ψ) (E.coldLabelLimitProfile k a t ψ) := by
  let ρ := JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)
  let _ : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr (hΩ₁.prod hΩ₂).measure_lt_top.ne
  have hw := E.coldLabel_striped_weak_limit hs₀ hη hK hα hγ k a ht
    (Ω₁ ×ˢ Ω₂) (hΩ₁.prod hΩ₂).measurableSet (hΩ₁.prod hΩ₂).measure_lt_top hψ hψB
  exact hw.of_integral_abs_sub
    (fun n => E.coldLabelStripedProfile_integrable hK hα hγ k a n ht hψ hψB ρ)
    (fun n => E.coldLabelAverage_integrable hs₀ hsmax hη hηmax hK hd₀.le hq k a n t
      (Ω₁ ×ˢ Ω₂) (hΩ₁.prod hΩ₂) hψ.measurable hψB)
    (E.coldLabel_actual_striped_L1_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hsmall hq k a hk ht htU Ω₁ hΩ₁ Ω₂ hΩ₂ hψ hψB)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Identifying the finite cold limit with the actual atomic background -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.finiteColdLimitProfile_eq_background (E : HotLimitExtraction S)
    (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    {t δ R : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ) (x : JetPrototype.Space)
    (hlo : δ ≤ ‖x.1‖) (hhi : ‖x.1‖ ≤ R) (ψ : Velocity → ℝ) :
    E.finiteColdLimitProfile (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η)
      t ψ x = ∫ v, ψ v ∂E.background t x := by
  convert! (GeometricBackground.integral_finite_window E.phase_mem.1 E.phase_mem.2 hη hδ
    hK hα hγ ht x hlo hhi ψ).symm using 1
  all_goals try with_reducible_and_instances rfl

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapColdBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Joint regularity and uniform bounds for the full cold velocity averages -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem coldAverage_measurable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) : Measurable (S.coldAverage n ψ) := by
  have hm := (hψ.comp measurable_snd).mul
    (S.rescaledColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem coldAverage_global_bound (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) (x : ℝ × JetPrototype.Space) :
    |S.coldAverage n ψ x| ≤
      (B*(S.radius n*(2*(F.approximation n).amplitude)))*(∫ v, H q v) := by
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  have hb := norm_integral_le_of_norm_le
    (f := fun v => ψ v*S.rescaledColdDensity n (x,v))
    ((integrable_H hq).const_mul (B*(S.radius n*(2*(F.approximation n).amplitude)))) ?_
  · simpa only [Real.norm_eq_abs,integral_const_mul,coldAverage] using hb
  · filter_upwards [] with v
    have hd := S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n (x,v)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hd.1]
    exact (mul_le_mul (hψB v) hd.2 hd.1 hB).trans_eq (by ring)

theorem coldAverage_integrable (S : AttainedCapSequence F)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure ρ] :
    Integrable (S.coldAverage n ψ) ρ :=
  Integrable.of_bound (S.coldAverage_measurable hs₀ hsmax hη hηmax hK hd₀ hq n hψ).aestronglyMeasurable
    _ (ae_of_all _ (S.coldAverage_global_bound hs₀ hsmax hη hηmax hK hd₀ hq n hψB))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Joint time-space regularity of actual cold-label velocity averages -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabelDensity_joint_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ) :
    Measurable (fun z : (ℝ × JetPrototype.Space) × Velocity =>
      E.coldLabelDensity k a n z.1.1 (z.1.2,z.2)) := by
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  have hp : Measurable (fun z : (ℝ × JetPrototype.Space) × Velocity =>
      (S.radius (E.indices n)*z.1.1,(S.radius (E.indices n) • z.1.2,z.2))) := by fun_prop
  exact (((ChartKernel.measurable_H q).comp measurable_snd).mul
    ((hc.1 (E.coldLabel k a n)).comp hp)).const_mul _

theorem HotLimitExtraction.coldLabelAverage_joint_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun z : ℝ × JetPrototype.Space => E.coldLabelAverage k a n z.1 ψ z.2) := by
  have hm := (hψ.comp measurable_snd).mul
    (E.coldLabelDensity_joint_measurable hs₀ hsmax hη hηmax hK hd₀ hq k a n)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem HotLimitExtraction.coldLabelAverage_global_bound (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B)
    (t : ℝ) (x : JetPrototype.Space) :
    |E.coldLabelAverage k a n t ψ x| ≤
      (B*(S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude)))*(∫ v, H q v) := by
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  have hb := norm_integral_le_of_norm_le
    (f := fun v => ψ v*E.coldLabelDensity k a n t (x,v))
    ((integrable_H hq).const_mul (B*(S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude)))) ?_
  · simpa only [Real.norm_eq_abs,integral_const_mul,coldLabelAverage] using hb
  · filter_upwards [] with v
    have hd := E.coldLabelDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq k a n t (x,v)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hd.1]
    exact (mul_le_mul (hψB v) hd.2 hd.1 hB).trans_eq (by ring)

theorem HotLimitExtraction.coldLabelAverage_joint_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (k : ℤ) (a : Bool) (n : ℕ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure ρ] :
    Integrable (fun z => E.coldLabelAverage k a n z.1 ψ z.2) ρ :=
  Integrable.of_bound
    (E.coldLabelAverage_joint_measurable hs₀ hsmax hη hηmax hK hd₀ hq k a n hψ).aestronglyMeasurable
    _ (ae_of_all _ (fun z => E.coldLabelAverage_global_bound hs₀ hsmax hη hηmax hK hd₀ hq k a n hψB z.1 z.2))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A finite window of actual cold labels -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.meshCold_sum (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ)
    (hU : U < GeometricMesh.index (s₀/S.radius (E.indices n)) η) (u : ℝ × JetPrototype.Phase) :
    E.meshCold n L U u = ∑ a : Bool, ∑ k ∈ Finset.Icc L U,
      if (E.coldLabel k a n).annulus < F.indices (E.indices n) then
        (F.approximation (E.indices n)).cold (E.coldLabel k a n) u else 0 := by
  classical
  unfold meshCold meshLabels
  rw [Finset.sum_image]
  · exact (Finset.sum_product _ _ _).trans Finset.sum_comm
  · intro p hp q hq he
    have hj := congrArg JetLattice.Label.annulus he
    have ha := congrArg JetLattice.Label.positive he
    have hpU := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).2.trans_lt hU
    have hqU := (Finset.mem_Icc.mp (Finset.mem_product.mp hq).1).2.trans_lt hU
    have hh := congrArg (GeometricMesh.jetMeshIndex s₀ η (S.radius (E.indices n))) hj
    change GeometricMesh.jetMeshIndex s₀ η (S.radius (E.indices n))
        (GeometricMesh.jetIndex s₀ η (fun m => S.radius (E.indices m)) p.1 n) =
      GeometricMesh.jetMeshIndex s₀ η (S.radius (E.indices n))
        (GeometricMesh.jetIndex s₀ η (fun m => S.radius (E.indices m)) q.1 n) at hh
    rw [GeometricMesh.meshIndex_at_jetIndex s₀ η (fun m => S.radius (E.indices m)) n hpU,
      GeometricMesh.meshIndex_at_jetIndex s₀ η (fun m => S.radius (E.indices m)) n hqU] at hh
    exact Prod.ext hh ha

theorem HotLimitExtraction.meshCold_le_total (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2)
    (n : ℕ) (L U : ℤ) (u : ℝ × JetPrototype.Phase) :
    E.meshCold n L U u ≤ (F.approximation (E.indices n)).coldTotal u := by
  classical
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  have hs := ((F.approximation (E.indices n)).coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le).2 u
  apply (Finset.sum_le_sum (s := E.meshLabels n L U) (fun i _ => ?_)).trans
    (hs.1.sum_le_tsum _ (fun i _ => hc.2.1 i u))
  by_cases hi : i.annulus < F.indices (E.indices n)
  · exact (ite_eq_left hi).le
  · rw [ite_eq_right hi]
    exact hc.2.1 i u

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapColdAverages
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual dilated cold density on a finite mesh window -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.meshCold_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ) :
    Measurable (E.meshCold n L U) := by
  classical
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  apply Finset.measurable_sum
  intro i _
  by_cases hi : i.annulus < F.indices (E.indices n)
  · simpa only [hi,ite_true, if_true] using hc.1 i
  · simpa only [hi,ite_false, if_false] using (measurable_const : Measurable (fun _ : ℝ × JetPrototype.Phase => (0:ℝ)))

theorem HotLimitExtraction.meshColdDensity_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ) :
    Measurable (E.meshColdDensity n L U) := by
  have hm := E.meshCold_measurable hs₀ hsmax hη hηmax hK hd₀ hq n L U
  have hp : Measurable (fun z : Published.KineticPhase =>
      (S.radius (E.indices n)*z.1.1,(S.radius (E.indices n) • JetPeriodicDatum.spatialMap z.1.2,z.2))) := by
    unfold JetPeriodicDatum.spatialMap transverse axial
    fun_prop
  exact (((ChartKernel.measurable_H q).comp measurable_snd).const_mul _).mul (hm.comp hp)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A fixed set of retained labels on every finite mesh interval -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.meshColdDensity_sum (E : HotLimitExtraction S) (n : ℕ) (L U : ℤ)
    (hU : U < GeometricMesh.index (s₀/S.radius (E.indices n)) η) (z : Published.KineticPhase) :
    E.meshColdDensity n L U z = ∑ a : Bool, ∑ k ∈ Finset.Icc L U,
      if (E.coldLabel k a n).annulus < F.indices (E.indices n) then
        E.coldLabelDensity k a n z.1.1 (JetPeriodicDatum.spatialMap z.1.2,z.2) else 0 := by
  classical
  unfold meshColdDensity
  rw [E.meshCold_sum n L U hU,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (E.coldLabel k a n).annulus < F.indices (E.indices n)
  · simp only [hk,ite_true, if_true,coldLabelDensity]
    ring
  · simp only [hk,ite_false, if_false,mul_zero]

theorem HotLimitExtraction.eventually_meshColdDensity_fixed (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hη : 0 < η) (L U : ℤ) :
    ∀ᶠ n in atTop, ∀ z : Published.KineticPhase,
      E.meshColdDensity n L U z = ∑ a : Bool, ∑ k ∈ Finset.Icc L U,
        if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then
          E.coldLabelDensity k a n z.1.1 (JetPeriodicDatum.spatialMap z.1.2,z.2) else 0 := by
  classical
  have hret : ∀ᶠ n in atTop, ∀ k ∈ Finset.Icc L U, ∀ a : Bool,
      ((E.coldLabel k a n).annulus < F.indices (E.indices n) ↔
        E.fraction < E.phase*Real.exp (η*(k:ℝ))) := by
    rw [Filter.eventually_all_finset]
    intro k _
    exact Filter.eventually_all.mpr (fun a => E.coldLabel_retained_iff hs₀ hη k a)
  have htop := (GeometricMesh.index_tendsto_atTop hs₀ hη
    (fun n => S.radius_pos hs₀ (E.indices n))
    ((S.radius_tendsto_zero hs₀).comp E.indices_strict.tendsto_atTop)).eventually_gt_atTop U
  filter_upwards [hret,htop] with n hn htop
  intro z
  rw [E.meshColdDensity_sum n L U htop z]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k hk
  simp only [hn k hk a]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Velocity averages of the finite retained mesh -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.eventually_meshColdDensity_average (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (L U : ℤ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    ∀ᶠ n in atTop, ∀ (t : ℝ) (x : Velocity),
      (∫ v, ψ v*E.meshColdDensity n L U ((t,x),v)) =
        E.finiteColdAverage L U n t ψ (JetPeriodicDatum.spatialMap x) := by
  classical
  filter_upwards [E.eventually_meshColdDensity_fixed hs₀ hη L U] with n hn
  intro t x
  let f : Bool → ℤ → Velocity → ℝ := fun a k v =>
    if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then
      ψ v*E.coldLabelDensity k a n t (JetPeriodicDatum.spatialMap x,v) else 0
  have hi (a k) : Integrable (f a k) := by
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))
    · simpa only [f,hk,ite_true, if_true] using
        (E.coldLabelDensity_fiber_integrable hs₀ hsmax hη hηmax hK hd₀ hq k a n t
          (JetPeriodicDatum.spatialMap x)).bdd_mul hψ.aestronglyMeasurable
            (ae_of_all _ hψB)
    · simp only [f,hk,ite_false, if_false]
      exact integrable_const_iff.mpr (Or.inl rfl)
  have heq : (fun v => ψ v*E.meshColdDensity n L U ((t,x),v)) =
      (fun v => ∑ a : Bool, ∑ k ∈ Finset.Icc L U, f a k v) := by
    funext v
    rw [hn ((t,x),v),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)) <;>
      simp only [f,hk,ite_true, if_true,ite_false, if_false,mul_zero]
  rw [heq,integral_finsetSum _ (fun a _ =>
    integrable_finsetSum _ (fun k _ => hi a k))]
  unfold finiteColdAverage
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ (fun k _ => hi a k)]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)) <;>
    simp only [f,hk,ite_true, if_true,ite_false, if_false,integral_zero,coldLabelAverage]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Weak space-time convergence of the actual retained cold labels -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.coldLabel_spacetime_weak_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
    (k : ℤ) (σ : Bool) (hk : E.fraction < E.phase*Real.exp (η*(k:ℝ)))
    {a A : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges
      ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
      (fun n z => E.coldLabelAverage k σ n z.1 ψ z.2)
      (fun z => E.coldLabelLimitProfile k σ (max 0 z.1) ψ z.2) := by
  let ρ := JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)
  let ν := (volume : Measure ℝ).restrict (Icc a A)
  let _ : IsFiniteMeasure ρ := isFiniteMeasure_restrict.mpr (hΩ₁.prod hΩ₂).measure_lt_top.ne
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  apply Published.WeakL1Converges.prod_of_fibers
    (fun n => E.coldLabelAverage_joint_integrable hs₀ hsmax hη hηmax hK hd₀.le hq k σ n
      hψ.measurable hψB (ν.prod ρ))
    (E.coldLabelLimitProfile_clamped_measurable hK hα.le hγ.le k σ hψ.measurable)
    (E.coldLabelLimitProfile_clamped_integrable hK hα hγ k σ ha hψ.measurable hψB ρ)
  · have hb := E.eventually_coldLabelAverage_bound_q80 hs₀ hsmax hη hηmax hK hα
      (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq ha hA hB hψB
    filter_upwards [hb] with n hn
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz
    exact hn z.1 hz k σ z.2
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have htp : 0 < t := ha.trans_le ht.1
    have hw := E.coldLabel_weak_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
      hsmall hq k σ hk htp ((ENNReal.ofReal_le_ofReal ht.2).trans_lt hA)
      Ω₁ hΩ₁ Ω₂ hΩ₂ hψ hψB
    simpa only [max_eq_right htp.le] using hw

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Weak space-time convergence of the finite retained cold mesh -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.finite_cold_spacetime_weak_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (L U : ℤ) {a A : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges
      ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
      (fun n z => E.finiteColdAverage L U n z.1 ψ z.2)
      (fun z => E.finiteColdLimitProfile L U (max 0 z.1) ψ z.2) := by
  classical
  let ρ := (volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂))
  let _ : IsFiniteMeasure (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)) :=
    isFiniteMeasure_restrict.mpr (hΩ₁.prod hΩ₂).measure_lt_top.ne
  let f : Bool → ℤ → ℕ → (ℝ × JetPrototype.Space) → ℝ := fun σ k n z =>
    if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then E.coldLabelAverage k σ n z.1 ψ z.2 else 0
  let g : Bool → ℤ → (ℝ × JetPrototype.Space) → ℝ := fun σ k z =>
    if E.fraction < E.phase*Real.exp (η*(k:ℝ)) then E.coldLabelLimitProfile k σ (max 0 z.1) ψ z.2 else 0
  have hi (σ k n) : Integrable (f σ k n) ρ := by
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))
    · simpa only [f,hk,ite_true, if_true] using E.coldLabelAverage_joint_integrable hs₀ hsmax hη hηmax
        hK hd₀.le hq k σ n hψ.measurable hψB ρ
    · simpa only [f,hk,ite_false, if_false] using (integrable_const (μ := ρ) (0:ℝ))
  have hw (σ k) : Published.WeakL1Converges ρ (f σ k) (g σ k) := by
    by_cases hk : E.fraction < E.phase*Real.exp (η*(k:ℝ))
    · simpa only [f,g,hk,ite_true, if_true] using E.coldLabel_spacetime_weak_limit hs₀ hsmax hη hηmax
        hK hα hαmax hγ hd₀ hd₀max hsmall hq k σ hk ha hA Ω₁ hΩ₁ Ω₂ hΩ₂ hψ hψB
    · simp only [f,g,hk,ite_false, if_false]
      refine ⟨measurable_const,integrable_const 0,?_⟩
      intro φ _ _
      simp only [mul_zero,integral_zero]
      exact tendsto_const_nhds
  have hinner (σ) := Published.WeakL1Converges.finset_sum (Finset.Icc L U)
    (fun k _ => hw σ k) (fun k _ n => hi σ k n)
  exact Published.WeakL1Converges.finset_sum (Finset.univ : Finset Bool)
    (fun σ _ => hinner σ)
    (fun σ _ n => integrable_finsetSum (Finset.Icc L U) (fun k _ => hi σ k n))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The atomic background is the space-time limit of the finite cold mesh -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.finite_cold_spacetime_background_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {a A δ R : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon) (hδ : 0 < δ)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (hlo : ∀ y ∈ Ω₁, δ ≤ ‖y‖) (hhi : ∀ y ∈ Ω₁, ‖y‖ ≤ R)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges
      ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
      (fun n z => E.finiteColdAverage (GeometricMesh.index (δ/Real.exp η) η)
        (GeometricMesh.index R η) n z.1 ψ z.2)
      (fun z => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) := by
  have hw := E.finite_cold_spacetime_weak_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η)
    ha hA Ω₁ hΩ₁ Ω₂ hΩ₂ hψ hψB
  have hm : Measurable (fun z : ℝ × JetPrototype.Space => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) :=
    GeometricBackground.clamped_background_test_measurable (zero_lt_one.trans_le E.phase_mem.1)
      hK hα.le hγ.le η E.fraction hψ.measurable
  apply hw.congr_limit hm
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae
    (ae_restrict_mem (hΩ₁.prod hΩ₂).measurableSet)] with z hz
  exact E.finiteColdLimitProfile_eq_background hη hK hα.le hγ.le (le_max_left 0 z.1) hδ z.2
    (hlo z.2.1 hz.1) (hhi z.2.1 hz.1) ψ

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual finite-mesh velocity averages converge to the background -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness

theorem JetPeriodicDatum.spatialMap_join (x : JetPrototype.Space) :
    JetPeriodicDatum.spatialMap (SheetMeasures.join x) = x := by
  have h := VelocityWeight.split.apply_symm_apply (x.2,x.1)
  apply Prod.ext
  · change VelocityWeight.transverse (VelocityWeight.split.symm (x.2,x.1)) = x.1
    simpa only [VelocityWeight.split_apply] using congrArg Prod.snd h
  · change VelocityWeight.axial (VelocityWeight.split.symm (x.2,x.1)) = x.2
    simpa only [VelocityWeight.split_apply] using congrArg Prod.fst h

namespace JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.eventually_meshColdChartAverage (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (L U : ℤ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    ∀ᶠ n in atTop, ∀ (t : ℝ) (x : JetPrototype.Space),
      E.meshColdChartAverage n L U t ψ x = E.finiteColdAverage L U n t ψ x := by
  filter_upwards [E.eventually_meshColdDensity_average hs₀ hsmax hη hηmax hK hd₀ hq L U hψ hψB]
    with n hn
  intro t x
  simpa only [meshColdChartAverage,JetPeriodicDatum.spatialMap_join] using hn t (SheetMeasures.join x)

theorem HotLimitExtraction.mesh_cold_spacetime_background_limit (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {a A δ R : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon) (hδ : 0 < δ)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (hlo : ∀ y ∈ Ω₁, δ ≤ ‖y‖) (hhi : ∀ y ∈ Ω₁, ‖y‖ ≤ R)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges
      ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
      (fun n z => E.meshColdChartAverage n (GeometricMesh.index (δ/Real.exp η) η)
        (GeometricMesh.index R η) z.1 ψ z.2)
      (fun z => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) := by
  apply (E.finite_cold_spacetime_background_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq ha hA hδ Ω₁ hΩ₁ hlo hhi Ω₂ hΩ₂ hψ hψB).congr_eventually
  filter_upwards [E.eventually_meshColdChartAverage hs₀ hsmax hη hηmax hK hd₀.le hq
    (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index R η) hψ.measurable hψB] with n hn
  exact ae_of_all _ (fun z => (hn z.1 z.2).symm)

end JetCopyDatum.AttainedCapSequence
end BoltzmannNonuniqueness

end

end

section

/-! # Positivity and integrability of finite-mesh averages -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.meshColdDensity_bounds (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ)
    (z : Published.KineticPhase) :
    0 ≤ E.meshColdDensity n L U z ∧ E.meshColdDensity n L U z ≤
      S.rescaledColdDensity (E.indices n) ((z.1.1,JetPeriodicDatum.spatialMap z.1.2),z.2) := by
  have hc := (F.approximation (E.indices n)).cold_properties hs₀ hsmax hη hηmax hK hd₀ hq
    (shrinkingHorizon_pos F.horizonScale_pos _).le
  have hnon : 0 ≤ E.meshCold n L U
      (S.radius (E.indices n)*z.1.1,(S.radius (E.indices n) • JetPeriodicDatum.spatialMap z.1.2,z.2)) := by
    apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact hc.2.1 _ _
    · exact le_rfl
  have hH := mul_nonneg (S.radius_pos hs₀ (E.indices n)).le (H_nonneg q z.2)
  exact ⟨mul_nonneg hH hnon,mul_le_mul_of_nonneg_left
    (E.meshCold_le_total hs₀ hsmax hη hηmax hK hd₀ hq n L U _) hH⟩

theorem HotLimitExtraction.meshColdChartAverage_measurable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) :
    Measurable (fun x : ℝ × JetPrototype.Space => E.meshColdChartAverage n L U x.1 ψ x.2) := by
  have hp : Measurable (fun z : (ℝ × JetPrototype.Space) × Velocity =>
      ((z.1.1,SheetMeasures.join z.1.2),z.2)) :=
    (measurable_fst.fst.prodMk (SheetMeasures.join.measurable.comp measurable_fst.snd)).prodMk measurable_snd
  have hm := (hψ.comp measurable_snd).mul
    ((E.meshColdDensity_measurable hs₀ hsmax hη hηmax hK hd₀ hq n L U).comp hp)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem HotLimitExtraction.meshColdChartAverage_global_bound (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B) (x : ℝ × JetPrototype.Space) :
    |E.meshColdChartAverage n L U x.1 ψ x.2| ≤
      (B*(S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude)))*(∫ v, H q v) := by
  have hB : 0 ≤ B := (abs_nonneg (ψ 0)).trans (hψB 0)
  have hb := norm_integral_le_of_norm_le
    (f := fun v => ψ v*E.meshColdDensity n L U ((x.1,SheetMeasures.join x.2),v))
    ((integrable_H hq).const_mul (B*(S.radius (E.indices n)*(2*(F.approximation (E.indices n)).amplitude)))) ?_
  · simpa only [Real.norm_eq_abs,integral_const_mul,meshColdChartAverage] using hb
  · filter_upwards [] with v
    have hd := E.meshColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq n L U
      ((x.1,SheetMeasures.join x.2),v)
    have ht := S.rescaledColdDensity_bounds hs₀ hsmax hη hηmax hK hd₀ hq (E.indices n)
      ((x.1,JetPeriodicDatum.spatialMap (SheetMeasures.join x.2)),v)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hd.1]
    exact (mul_le_mul (hψB v) (hd.2.trans ht.2) hd.1 hB).trans_eq (by ring)

theorem HotLimitExtraction.meshColdChartAverage_integrable (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (n : ℕ) (L U : ℤ)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Measurable ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (ρ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure ρ] :
    Integrable (fun x => E.meshColdChartAverage n L U x.1 ψ x.2) ρ :=
  Integrable.of_bound
    (E.meshColdChartAverage_measurable hs₀ hsmax hη hηmax hK hd₀ hq n L U hψ).aestronglyMeasurable
    _ (ae_of_all _ (E.meshColdChartAverage_global_bound hs₀ hsmax hη hηmax hK hd₀ hq n L U hψB))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Full cold-average convergence on compact cylinders away from the axis -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem SheetMeasures.norm_join_le_add (x : VelocityWeight.Transverse × ℝ) :
    ‖SheetMeasures.join x‖ ≤ ‖x.1‖+|x.2| := by
  have he := SheetMeasures.norm_join_sq x
  nlinarith [norm_nonneg (SheetMeasures.join x),norm_nonneg x.1,abs_nonneg x.2,sq_abs x.2]

namespace JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.cold_away_axis_weak_limit_q80_oai (E : HotLimitExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) {a A δ R : ℝ} (ha : 0 < a) (hA : ENNReal.ofReal A < E.horizon)
    (hδ : 0 < δ) (hR : 0 ≤ R)
    (Ω₁ : Set VelocityWeight.Transverse) (hΩ₁ : IsCompact Ω₁)
    (hlo : ∀ y ∈ Ω₁, δ ≤ ‖y‖) (hhi : ∀ y ∈ Ω₁, ‖y‖ ≤ R)
    (Ω₂ : Set ℝ) (hΩ₂ : IsCompact Ω₂) (hax : ∀ z ∈ Ω₂, |z| ≤ R)
    {B : ℝ} {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) :
    Published.WeakL1Converges
      ((volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)))
      (fun n => S.coldAverage (E.indices n) ψ)
      (fun z => ∫ v, ψ v ∂E.background (max 0 z.1) z.2) := by
  let ρ := (volume.restrict (Icc a A)).prod (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂))
  let _ : IsFiniteMeasure (JetPrototype.spaceVolume.restrict (Ω₁ ×ˢ Ω₂)) :=
    isFiniteMeasure_restrict.mpr (hΩ₁.prod hΩ₂).measure_lt_top.ne
  have hα1 : α ≤ 1 := hαmax.trans (by norm_num)
  have hw := E.mesh_cold_spacetime_background_limit hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq (R := 2*R) ha hA hδ Ω₁ hΩ₁ hlo (fun y hy => (hhi y hy).trans (by linarith))
    Ω₂ hΩ₂ hψ hψB
  apply hw.of_integral_abs_sub
    (fun n => E.meshColdChartAverage_integrable hs₀ hsmax hη hηmax hK hd₀.le hq n
      (GeometricMesh.index (δ/Real.exp η) η) (GeometricMesh.index (2*R) η) hψ.measurable hψB ρ)
    (fun n => S.coldAverage_integrable hs₀ hsmax hη hηmax hK hd₀.le hq (E.indices n) hψ.measurable hψB ρ)
  apply E.cold_mesh_average_L1_limit_q80 hs₀ hsmax hη hηmax hK hα.le hα1 hγ.le
    hd₀ hd₀max hsmall hq ha hA hδ hψ.measurable hψB ρ
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (hΩ₁.prod hΩ₂).measurableSet)] with z ht hx
  exact ⟨ht,hlo _ hx.1,(SheetMeasures.norm_join_le_add z.2).trans (by
    have hy := hhi _ hx.1
    have hz := hax _ hx.2
    linarith)⟩

end JetCopyDatum.AttainedCapSequence
end BoltzmannNonuniqueness

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_away_axis_weak_limit_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.cold_away_axis_weak_limit_q80_oai
