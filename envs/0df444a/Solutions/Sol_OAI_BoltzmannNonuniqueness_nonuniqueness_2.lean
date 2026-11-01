-- Prove2me | solution 2 for OAI.BoltzmannNonuniqueness.nonuniqueness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:37:34.902467+00:00
-- url     : https://prove2.me/submissions/708774a7-e7c2-438b-9e4c-a7134280c477

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_Published_glps1988Proposition3_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_nonuniqueness_without_compactness_inputs_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_periodicExistenceInput_q80

section
-- module Solutions.OAIQ080_BZ.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_NormalReflectionGeometry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.stateKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_pow_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact reflected relative direction in the hard-sphere angular map -/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem normalReflection_measurable (e : Sphere) : Measurable (normalReflection e) := by
  unfold normalReflection normalReflectionVector
  fun_prop

theorem normalReflection_neg_normal (e n : Sphere) :
    normalReflectionVector e.1 (-n.1) = normalReflectionVector e.1 n.1 := by
  unfold normalReflectionVector
  simp only [inner_neg_right,mul_neg,neg_smul,smul_neg,neg_neg]

theorem normalReflection_relative_scatter (v w n : Velocity) :
    (1/2:ℝ) • (v+w)+(1/2:ℝ) • normalReflectionVector (v-w) n = scatterLeft v w n := by
  unfold normalReflectionVector scatterLeft normalComponent
  module

theorem normalReflectionVector_smul (c : ℝ) (g n : Velocity) :
    normalReflectionVector (c • g) n = c • normalReflectionVector g n := by
  unfold normalReflectionVector
  rw [real_inner_smul_left]
  module

theorem normalReflection_child (e : Sphere) (r : ℝ) (hr : 0 ≤ r)
    (v w : Velocity) (hg : v-w = r • e.1) (n : Sphere) :
    ReferenceGeometry.child v w (normalReflection e n).1 = scatterLeft v w n.1 := by
  have hn : ‖v-w‖ = r := by rw [hg,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,
    mem_sphere_zero_iff_norm.mp e.property,mul_one]
  rw [ReferenceGeometry.child,hn]
  change (1/2:ℝ) • (v+w)+(r/2) • normalReflectionVector e.1 n.1 = _
  rw [← normalReflection_relative_scatter v w n.1,hg,normalReflectionVector_smul]
  module

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SphereIsometryMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Orthogonal changes of coordinates preserve the actual sphere area measure -/

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace BoltzmannNonuniqueness

theorem sphereIsometry_cone (R : Velocity ≃ₗᵢ[ℝ] Velocity) (S : Set Sphere) :
    (Ioo (0:ℝ) 1) • ((↑) '' ((sphereIsometry R) ⁻¹' S)) =
      R ⁻¹' ((Ioo (0:ℝ) 1) • ((↑) '' S)) := by
  ext x
  constructor
  · rintro ⟨r,hr,y,⟨n,hn,hny⟩,hxy⟩
    subst y
    change R x ∈ (Ioo (0:ℝ) 1) • ((↑) '' S)
    refine ⟨r,hr,R n.1,⟨sphereIsometry R n,hn,rfl⟩,?_⟩
    change r • R n.1 = R x
    change r • n.1 = x at hxy
    rw [← R.map_smul,hxy]
  · rintro ⟨r,hr,y,⟨n,hn,hny⟩,hxy⟩
    subst y
    refine ⟨r,hr,R.symm n.1,⟨(sphereIsometry R).symm n,?_,rfl⟩,?_⟩
    · change sphereIsometry R ((sphereIsometry R).symm n) ∈ S
      simpa only [MeasurableEquiv.apply_symm_apply] using hn
    · apply R.injective
      rw [R.map_smul,R.apply_symm_apply]
      exact hxy

theorem sphereIsometry_measurePreserving (R : Velocity ≃ₗᵢ[ℝ] Velocity) :
    MeasurePreserving (sphereIsometry R) sphereArea sphereArea := by
  refine ⟨(sphereIsometry R).measurable,?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (sphereIsometry R).measurable hS,sphereArea,
    Measure.toSphere_apply' _ ((sphereIsometry R).measurable hS),Measure.toSphere_apply' _ hS,
    sphereIsometry_cone]
  congr 1
  change volume (R.toHomeomorph ⁻¹' _) = volume _
  rw [← R.toHomeomorph.measurableEmbedding.map_apply]
  change (volume.map R) _ = volume _
  rw [R.measurePreserving.map_eq]

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityFourierMultiplier
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Nonnegative polar integrals for the physical three-dimensional velocity space -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem lintegral_velocity_polar {F : Velocity → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x, F x) = ∫⁻ n : Sphere, ∫⁻ r : Ioi (0:ℝ), F ((r:ℝ) • n.1)
      ∂Measure.volumeIoiPow 2 ∂sphereArea := by
  let H := homeomorphUnitSphereProd Velocity
  have hp := (volume : Measure Velocity).measurePreserving_homeomorphUnitSphereProd
  have hFm : Measurable (fun p : Sphere × Ioi (0:ℝ) => F ((p.2:ℝ) • p.1.1)) := by
    apply hF.comp
    fun_prop
  calc
    (∫⁻ x, F x) = ∫⁻ x : ({0}ᶜ : Set Velocity), F x ∂((volume : Measure Velocity).comap (↑)) := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl,restrict_compl_singleton]
    _ = ∫⁻ p : Sphere × Ioi (0:ℝ), F ((p.2:ℝ) • p.1.1)
        ∂sphereArea.prod (Measure.volumeIoiPow 2) := by
      have hh := hp.lintegral_comp_emb H.measurableEmbedding
        (fun p => F (H.symm p))
      simpa only [H,sphereArea,Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe,finrank_euclideanSpace,
        Fintype.card_fin,Nat.reduceSub] using hh
    _ = _ := lintegral_prod _ hFm.aemeasurable

theorem radial_cubic_unit_integral :
    (∫⁻ r : Ioi (0:ℝ), if (r:ℝ) < 1 then ENNReal.ofReal ((r:ℝ)^3) else 0
      ∂Measure.volumeIoiPow 2) = (6:ℝ≥0∞)⁻¹ := by
  have hm : Measurable (fun r : Ioi (0:ℝ) => ENNReal.ofReal ((r:ℝ)^3)) := by fun_prop
  have hd : (Measure.volumeIoiPow 2).withDensity (fun r : Ioi (0:ℝ) => ENNReal.ofReal ((r:ℝ)^3)) =
      Measure.volumeIoiPow 5 := by
    unfold Measure.volumeIoiPow
    rw [← withDensity_mul _ (by fun_prop) hm]
    congr 1
    funext r
    change ENNReal.ofReal ((r:ℝ)^2)*ENNReal.ofReal ((r:ℝ)^3) = _
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hs : MeasurableSet {r : Ioi (0:ℝ) | (r:ℝ) < 1} := measurableSet_lt (by fun_prop) measurable_const
  change (∫⁻ r, ({r : Ioi (0:ℝ) | (r:ℝ) < 1}.indicator
    (fun r => ENNReal.ofReal ((r:ℝ)^3))) r ∂Measure.volumeIoiPow 2) = _
  rw [lintegral_indicator hs,← withDensity_apply _ hs,hd]
  change Measure.volumeIoiPow 5 (Iio (⟨1,by norm_num⟩ : Ioi (0:ℝ))) = _
  rw [Measure.volumeIoiPow_apply_Iio]
  norm_num only [Nat.reduceAdd,one_pow]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 6)]
  norm_num

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_TransverseAverage
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem inner_line (e : Transverse) (D s : ℝ) (he : ‖e‖ = 1) :
    inner ℝ e (line e D s) = D := by
  simp only [line, inner_add_right, inner_smul_right, inner_quarterTurn,
    real_inner_self_eq_norm_sq, he]
  ring

theorem inner_quarterTurn_line (e : Transverse) (D s : ℝ) (he : ‖e‖ = 1) :
    inner ℝ (quarterTurn e) (line e D s) = s := by
  have hp : inner ℝ (quarterTurn e) e = 0 := by
    rw [real_inner_comm, inner_quarterTurn]
  simp only [line, inner_add_right, inner_smul_right, hp,
    real_inner_self_eq_norm_sq, norm_quarterTurn, he]
  ring

/-- The normal and tangential coordinates recover every transverse vector. -/
theorem line_reconstruct (e u : Transverse) (he : ‖e‖ = 1) :
    line e (inner ℝ e u) (inner ℝ (quarterTurn e) u) = u := by
  have hnorm : e 0 ^ 2 + e 1 ^ 2 = 1 := by
    have hsq : ‖e‖ ^ (2 : ℕ) = 1 := by rw [he]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] at hsq
    exact hsq
  apply (WithLp.ext_iff 2).mpr
  funext i
  fin_cases i
  · simp [line, quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination u 0 * hnorm
  · simp [line, quarterTurn, PiLp.inner_apply, Fin.sum_univ_two]
    linear_combination u 1 * hnorm

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

theorem norm_direction {v : Transverse} (hv : v ≠ 0) : ‖direction v‖ = 1 :=
  norm_smul_inv_norm hv

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

theorem join_transverse_axial (v : Velocity) : join (transverse v) (axial v) = v := by
  apply split.injective
  simp only [join, split.apply_symm_apply, split_apply]

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

/-- Every velocity on the plane is recovered by its axial and tangent coordinates. -/
theorem chart_recovers (v p ξ : Velocity) (hn : normal v p ≠ 0)
    (hplane : inner ℝ (v - p) (ξ - v) = 0) :
    chart v p (axial ξ - axial v)
      (inner ℝ (quarterTurn (direction (normal v p))) (transverse ξ)) = ξ := by
  have hnn : ‖normal v p‖ ≠ 0 := norm_ne_zero_iff.mpr hn
  have hscale : ‖normal v p‖ • direction (normal v p) = normal v p := by
    rw [direction, smul_smul, mul_inv_cancel₀ hnn, one_smul]
  have he : ‖normal v p‖ *
      (inner ℝ (direction (normal v p)) (transverse ξ) - offset v p) +
      axial (v - p) * (axial ξ - axial v) = 0 := by
    simp only [inner_split, transverse_sub, axial_sub] at hplane
    change inner ℝ (normal v p) (transverse ξ - transverse v) +
      axial (v - p) * (axial ξ - axial v) = 0 at hplane
    rw [← hscale, real_inner_smul_left, inner_sub_right] at hplane
    exact hplane
  have hD : offset v p - slope v p * (axial ξ - axial v) =
      inner ℝ (direction (normal v p)) (transverse ξ) := by
    unfold slope
    field_simp
    nlinarith only [he]
  unfold chart
  rw [hD, line_reconstruct _ _ (norm_direction hn), add_sub_cancel]
  exact join_transverse_axial ξ

end BoltzmannNonuniqueness.PlaneChart

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RedundantPlaneIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A nonsingular three-dimensional coordinate map for a collision plane

The third coordinate is the coefficient of the normal, rather than distance
along the unit normal. This normalization cancels the length of the normal in
the redundant-parameter density. The transverse normal must be nonzero, just
as in the graph chart used by the actual gain kernel.
-/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal

namespace BoltzmannNonuniqueness.RedundantPlane

theorem normSq_pos {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) : 0 < normSq n := by
  unfold normSq
  nlinarith [sq_nonneg (n 2),sq_pos_of_pos hr]

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Integrating the redundant coordinate in the collision plane -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal

namespace BoltzmannNonuniqueness.RedundantPlane

theorem splitThree_apply (q : V) : splitThree q = (q 0,(q 1,q 2)) := by
  rfl

theorem splitThree_measurePreserving : MeasurePreserving splitThree := by
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurePreserving.id volume).prod (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)))

end BoltzmannNonuniqueness.RedundantPlane

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CarlemanNormalCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Normal and tangent coordinates for the Carleman change of variables -/
noncomputable section
open Matrix MeasureTheory
open scoped Matrix ENNReal
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem frame_apply (n q : V) (r : ℝ) :
    frame n r q = ![-q 0*n 0-q 1*n 2*n 0/r^2-q 2*n 1/r,
      -q 0*n 1-q 1*n 2*n 1/r^2+q 2*n 0/r,-q 0*n 2+q 1] := by
  ext i
  fin_cases i <;> simp [frame,frameMatrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem frameMatrix_det {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) :
    (frameMatrix n r).det = RedundantPlane.normSq n/r := by
  simp [frameMatrix,Matrix.det_fin_three,RedundantPlane.normSq]
  field_simp [hr.ne']
  linear_combination -(n 2)^2 * hrsq

theorem frame_dot {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) (q : V) :
    n ⬝ᵥ frame n r q = -q 0*RedundantPlane.normSq n := by
  rw [frame_apply]
  simp [RedundantPlane.normSq,Matrix.vecHead,Matrix.vecTail]
  field_simp [hr.ne']
  linear_combination (q 1*n 2) * hrsq

theorem frame_map_volume {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) :
    Measure.map (frame n r) volume = ENNReal.ofReal (r/RedundantPlane.normSq n) • volume := by
  have hN := RedundantPlane.normSq_pos hr hrsq
  have hd := frameMatrix_det hr hrsq
  have hm := Real.map_matrix_volume_pi_eq_smul_volume_pi
    (hd.trans_ne (ne_of_gt (div_pos hN hr)))
  simpa only [frame,hd,inv_div,abs_of_pos (div_pos hr hN)] using hm

theorem unit_frame_map_volume {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) (hn : RedundantPlane.normSq n = 1) :
    Measure.map (frame n r) volume = ENNReal.ofReal r • volume := by
  simpa only [hn,div_one] using frame_map_volume hr hrsq

end BoltzmannNonuniqueness.CarlemanCoordinates

end

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_NormalGainMeasureActions
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Rotation covariance of the weighted normal-reflection law -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem normalReflectionVector_isometry (R : Velocity ≃ₗᵢ[ℝ] Velocity) (g n : Velocity) :
    R (normalReflectionVector g n) = normalReflectionVector (R g) (R n) := by
  unfold normalReflectionVector
  rw [R.map_sub,R.map_smul,R.inner_map_map]

theorem normalReflection_isometry (R : Velocity ≃ₗᵢ[ℝ] Velocity) (e n : Sphere) :
    sphereIsometry R (normalReflection e n) =
      normalReflection (sphereIsometry R e) (sphereIsometry R n) := by
  apply Subtype.ext
  exact normalReflectionVector_isometry R e.1 n.1

theorem normalReflectionLaw_lintegral (e : Sphere) {f : Sphere → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ n, f n ∂normalReflectionLaw e) =
      ∫⁻ n : Sphere, ENNReal.ofReal |inner ℝ e.1 n.1| * f (normalReflection e n) ∂sphereArea := by
  rw [normalReflectionLaw,lintegral_map hf (normalReflection_measurable e),
    lintegral_withDensity_eq_lintegral_mul _ (g := fun n => f (normalReflection e n)) (by fun_prop)
      (hf.comp (normalReflection_measurable e))]
  rfl

theorem normalReflectionLaw_isometry (R : Velocity ≃ₗᵢ[ℝ] Velocity) (e : Sphere) :
    (normalReflectionLaw e).map (sphereIsometry R) = normalReflectionLaw (sphereIsometry R e) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (sphereIsometry R).measurable,
    normalReflectionLaw_lintegral e (f := fun n => f (sphereIsometry R n)) (hf.comp (sphereIsometry R).measurable),
    normalReflectionLaw_lintegral (sphereIsometry R e) hf]
  let g : Sphere → ℝ≥0∞ := fun n => ENNReal.ofReal |inner ℝ (sphereIsometry R e).1 n.1| *
    f (normalReflection (sphereIsometry R e) n)
  have hg : Measurable g := by
    exact (show Measurable (fun n : Sphere => ENNReal.ofReal |inner ℝ (sphereIsometry R e).1 n.1|) by
      fun_prop).mul (hf.comp (normalReflection_measurable _))
  calc
    _ = ∫⁻ n, g (sphereIsometry R n) ∂sphereArea := by
      apply lintegral_congr
      intro n
      dsimp only [g]
      rw [← normalReflection_isometry]
      congr 2
      change |inner ℝ e.1 n.1| = |inner ℝ (R e.1) (R n.1)|
      rw [R.inner_map_map]
    _ = ∫⁻ n, g n ∂sphereArea.map (sphereIsometry R) :=
      (lintegral_map hg (sphereIsometry R).measurable).symm
    _ = _ := by rw [(sphereIsometry_measurePreserving R).map_eq]

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RadialReflectionChangeVariables
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A polynomial radial extension of the normal-angle reflection map

On the positive hemisphere this quadratic map is injective. Its radial coordinate
is squared, allowing the angular change of variables to be proved in ambient space.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem radialReflection_continuous (e : Sphere) : Continuous (radialReflection e) := by
  unfold radialReflection
  fun_prop

theorem radialReflection_inner (e : Sphere) (x : Velocity) :
    inner ℝ e.1 (radialReflection e x) = ‖x‖^2-2*(inner ℝ e.1 x)^2 := by
  unfold radialReflection
  rw [inner_sub_right,real_inner_smul_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.mp e.property]
  ring

theorem radialReflection_norm (e : Sphere) (x : Velocity) :
    ‖radialReflection e x‖ = ‖x‖^2 := by
  have hs : ‖radialReflection e x‖^2 = (‖x‖^2)^2 := by
    unfold radialReflection
    rw [norm_sub_sq_real,real_inner_smul_left,real_inner_smul_right,norm_smul,norm_smul]
    simp only [Real.norm_eq_abs,mul_pow,sq_abs,mem_sphere_zero_iff_norm.mp e.property]
    ring
  nlinarith [norm_nonneg (radialReflection e x),sq_nonneg ‖x‖]

theorem radialReflection_sphere (e n : Sphere) (r : ℝ) :
    radialReflection e (r • n.1) = r^2 • (normalReflection e n).1 := by
  unfold radialReflection normalReflection normalReflectionVector
  rw [norm_smul,real_inner_smul_right]
  simp only [Real.norm_eq_abs,sq_abs,mem_sphere_zero_iff_norm.mp n.property,mul_one]
  module

theorem radialReflection_injOn (e : Sphere) :
    InjOn (radialReflection e) {x | 0 < inner ℝ e.1 x} := by
  intro x hx y hy hxy
  have hn : ‖x‖^2 = ‖y‖^2 := by
    simpa only [radialReflection_norm] using congrArg norm hxy
  have hi : inner ℝ e.1 x = inner ℝ e.1 y := by
    have h := congrArg (inner ℝ e.1) hxy
    rw [radialReflection_inner,radialReflection_inner,hn] at h
    have hx' : 0 < inner ℝ e.1 x := hx
    have hy' : 0 < inner ℝ e.1 y := hy
    nlinarith
  have hc : (2*inner ℝ e.1 x) • x = (2*inner ℝ e.1 x) • y := by
    unfold radialReflection at hxy
    rw [hn,hi] at hxy
    rw [hi]
    exact sub_right_injective hxy
  exact (smul_right_injective _ (ne_of_gt (mul_pos (by norm_num) hx))) hc

end BoltzmannNonuniqueness

end

end

section

/-! # Image of the positive half-space under the radial reflection map -/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem radialReflection_image (e : Sphere) :
    radialReflection e '' {x | 0 < inner ℝ e.1 x} =
      {y | inner ℝ e.1 y < ‖y‖} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change inner ℝ e.1 (radialReflection e x) < ‖radialReflection e x‖
    rw [radialReflection_inner,radialReflection_norm]
    have hx' : 0 < inner ℝ e.1 x := hx
    nlinarith [sq_pos_of_pos hx']
  · intro hy
    have ha : 0 < ‖y‖-inner ℝ e.1 y := sub_pos.mpr hy
    let a : ℝ := ‖y‖-inner ℝ e.1 y
    let d : ℝ := Real.sqrt (2*a)
    let z : Velocity := ‖y‖ • e.1-y
    have hd : 0 < d := Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
    have hd2 : d^2 = 2*a := Real.sq_sqrt (by positivity)
    have hi : inner ℝ e.1 z = a := by
      dsimp [z,a]
      rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
        mem_sphere_zero_iff_norm.mp e.property]
      ring
    have hz : ‖z‖^2 = 2*‖y‖*a := by
      dsimp [z,a]
      rw [norm_sub_sq_real,norm_smul,real_inner_smul_left]
      simp only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg y),
        mem_sphere_zero_iff_norm.mp e.property]
      ring
    have hc : (2*(d⁻¹*a))*d⁻¹ = 1 := by
      field_simp
      nlinarith [hd2]
    have hn : ‖d⁻¹ • z‖^2 = ‖y‖ := by
      rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hz]
      field_simp
      nlinarith [hd2]
    refine ⟨d⁻¹ • z,?_,?_⟩
    · change 0 < inner ℝ e.1 (d⁻¹ • z)
      rw [real_inner_smul_right,hi]
      exact mul_pos (inv_pos.mpr hd) ha
    · rw [radialReflection,hn,real_inner_smul_right,hi,smul_smul,hc,one_smul]
      dsimp [z]
      module

end BoltzmannNonuniqueness

end

end

section

/-! # Derivative of the ambient polynomial reflection map -/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem radialReflection_hasFDerivAt (e : Sphere) (x : Velocity) :
    HasFDerivAt (radialReflection e) (radialReflectionDerivative e x) x := by
  convert! ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.smul_const e.1).sub
    (((innerSL ℝ e.1).hasFDerivAt.const_mul 2).smul (hasFDerivAt_id x)) using 1
  all_goals try with_reducible_and_instances rfl
  ext h
  simp [radialReflectionDerivative,two_smul]

theorem radialReflectionDerivative_north (x h : Velocity) :
    radialReflectionDerivative northSphere x h =
      (2*inner ℝ x h) • (EuclideanSpace.single 0 1) -
        (2*h 0) • x - (2*x 0) • h := by
  simp only [radialReflectionDerivative,sub_apply,
    add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,innerSL_apply_apply,
    ContinuousLinearMap.id_apply,northSphere,EuclideanSpace.inner_single_left,map_one,one_mul]
  module

theorem radialReflectionDerivative_det_north (x : Velocity) :
    (radialReflectionDerivative northSphere x).det = -8*x 0*‖x‖^2 := by
  change (radialReflectionDerivative northSphere x).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  rw [Matrix.det_fin_three]
  simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_repr,
    ContinuousLinearMap.coe_coe]
  simp only [radialReflectionDerivative_north,
    EuclideanSpace.inner_single_right,EuclideanSpace.single,PiLp.single_apply,
    PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  norm_num
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_succ,Fin.isValue,Fin.reduceSucc]
  ring

end BoltzmannNonuniqueness

end

end

section

/-! # Ambient change of variables for the normal-angle reflection -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem radialReflection_image_ae (e : Sphere) :
    radialReflection e '' {x | 0 < inner ℝ e.1 x} =ᵐ[volume] (univ : Set Velocity) := by
  rw [radialReflection_image,ae_eq_univ]
  have he : e.1 ≠ 0 := by
    intro h
    have := mem_sphere_zero_iff_norm.mp e.property
    rw [h,norm_zero] at this
    norm_num at this
  have hn : (ℝ ∙ e.1 : Submodule ℝ Velocity) ≠ ⊤ := by
    intro h
    have hd := finrank_span_singleton (K := ℝ) he
    rw [h,finrank_top] at hd
    norm_num [finrank_euclideanSpace] at hd
  apply measure_mono_null (t := (ℝ ∙ e.1 : Submodule ℝ Velocity)) _
    (Measure.addHaar_submodule volume _ hn)
  intro y hy
  have hle : ‖y‖ ≤ inner ℝ e.1 y := le_of_not_gt hy
  have hinner : inner ℝ e.1 y ≤ ‖y‖ := by
    simpa only [mem_sphere_zero_iff_norm.mp e.property,one_mul] using real_inner_le_norm e.1 y
  have hi : inner ℝ e.1 y = ‖y‖ := le_antisymm hinner hle
  have hz : y-‖y‖ • e.1 = 0 := by
    apply norm_eq_zero.mp
    have hs : ‖y-‖y‖ • e.1‖^2 = 0 := by
      rw [norm_sub_sq_real,real_inner_smul_right,real_inner_comm,hi,norm_smul]
      simp only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg y),
        mem_sphere_zero_iff_norm.mp e.property,mul_one]
      ring
    nlinarith [norm_nonneg (y-‖y‖ • e.1)]
  rw [sub_eq_zero] at hz
  rw [hz]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem lintegral_radialReflection_north (g : Velocity → ℝ≥0∞) :
    (∫⁻ y, g y) = ∫⁻ x in {x : Velocity | 0 < x 0},
      ENNReal.ofReal (8*x 0*‖x‖^2) * g (radialReflection northSphere x) := by
  have hi : {x : Velocity | 0 < inner ℝ northSphere.1 x} = {x : Velocity | 0 < x 0} := by
    ext x
    simp [northSphere,EuclideanSpace.inner_single_left]
  have hs : MeasurableSet {x : Velocity | 0 < x 0} := measurableSet_lt measurable_const (by fun_prop)
  have hc := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x _ => (radialReflection_hasFDerivAt northSphere x).hasFDerivWithinAt)
    (hi ▸ radialReflection_injOn northSphere) g
  rw [← hi] at hc
  rw [Measure.restrict_congr_set (radialReflection_image_ae northSphere),Measure.restrict_univ] at hc
  rw [hi] at hc
  rw [hc]
  apply setLIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [radialReflectionDerivative_det_north]
  congr 2
  rw [show -8*x 0*‖x‖^2 = -(8*x 0*‖x‖^2) by ring,abs_neg,abs_of_nonneg]
  exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hx)) (sq_nonneg _)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_SphereDirectionAbsolute
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A measurable direction map with an arbitrary value at zero -/

noncomputable section
open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem sphereDirection_measurable (e : Sphere) : Measurable (sphereDirection e) := by
  apply Measurable.subtype_mk
  change Measurable (fun x => (sphereDirection e x).1)
  have he : (fun x => (sphereDirection e x).1) =
      fun x : Velocity => if x = 0 then e.1 else ‖x‖⁻¹ • x := by
    funext x
    simp only [sphereDirection,NormedSpace.normalize]
    split <;> rfl
  rw [he]
  exact measurable_const.ite (measurableSet_singleton 0) (measurable_norm.inv.smul measurable_id)

theorem sphereDirection_smul (e n : Sphere) {r : ℝ} (hr : 0 < r) :
    sphereDirection e (r • n.1) = n := by
  have hn : n.1 ≠ 0 := by
    intro h
    have := mem_sphere_zero_iff_norm.mp n.property
    rw [h,norm_zero] at this
    norm_num at this
  have h : r • n.1 ≠ 0 := smul_ne_zero hr.ne' hn
  apply Subtype.ext
  simp only [sphereDirection,dite_eq_right h,NormedSpace.normalize,norm_smul,
    Real.norm_eq_abs,abs_of_pos hr,mem_sphere_zero_iff_norm.mp n.property,mul_one,smul_smul,
    inv_mul_cancel₀ hr.ne',one_smul]

theorem sphereDirection_radialReflection (e n : Sphere) {r : ℝ} (hr : 0 < r) :
    sphereDirection e (radialReflection e (r • n.1)) = normalReflection e n := by
  rw [radialReflection_sphere]
  exact sphereDirection_smul e _ (sq_pos_of_pos hr)

end BoltzmannNonuniqueness

end

end

section

/-! # Lifting sphere tests to the unit velocity ball -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem sphereBallLift_measurable (e : Sphere) {f : Sphere → ℝ≥0∞} (hf : Measurable f) :
    Measurable (sphereBallLift e f) := by
  exact (hf.comp (sphereDirection_measurable e)).ite
    (measurableSet_lt measurable_norm measurable_const) measurable_const

theorem sphereBallLift_radial (e n : Sphere) (f : Sphere → ℝ≥0∞)
    (r : Ioi (0:ℝ)) :
    sphereBallLift e f ((r:ℝ) • n.1) = if (r:ℝ) < 1 then f n else 0 := by
  rw [sphereBallLift,sphereDirection_smul e n r.property,norm_smul,
    Real.norm_eq_abs,abs_of_pos r.property,mem_sphere_zero_iff_norm.mp n.property,mul_one]

theorem sphereBallLift_integral (e : Sphere) {f : Sphere → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, sphereBallLift e f x) = (3:ℝ≥0∞)⁻¹ * ∫⁻ n, f n ∂sphereArea := by
  rw [lintegral_velocity_polar (sphereBallLift_measurable e hf)]
  simp_rw [sphereBallLift_radial]
  have hi (n : Sphere) :
      (∫⁻ r : Ioi (0:ℝ), if (r:ℝ) < 1 then f n else 0 ∂Measure.volumeIoiPow 2) =
        (3:ℝ≥0∞)⁻¹*f n := by
    change (∫⁻ r, (Iio (⟨1,by norm_num⟩ : Ioi (0:ℝ))).indicator (fun _ => f n) r
      ∂Measure.volumeIoiPow 2) = _
    rw [lintegral_indicator measurableSet_Iio,setLIntegral_const,Measure.volumeIoiPow_apply_Iio]
    norm_num only [Nat.reduceAdd,one_pow]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 3)]
    norm_num [mul_comm]
  simp_rw [hi]
  exact lintegral_const_mul _ hf

theorem radial_cubic_factor {A : Sphere → ℝ≥0∞} (hA : Measurable A) :
    (∫⁻ n : Sphere, ∫⁻ r : Ioi (0:ℝ),
      (if (r:ℝ) < 1 then ENNReal.ofReal ((r:ℝ)^3) else 0)*A n
        ∂Measure.volumeIoiPow 2 ∂sphereArea) = (6:ℝ≥0∞)⁻¹*∫⁻ n, A n ∂sphereArea := by
  have hm : Measurable (fun r : Ioi (0:ℝ) =>
      if (r:ℝ) < 1 then ENNReal.ofReal ((r:ℝ)^3) else 0) := by
    exact Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
      (by fun_prop) measurable_const
  simp_rw [lintegral_mul_const _ hm,radial_cubic_unit_integral]
  exact lintegral_const_mul _ hA

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveSourceFormula
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! # The angular change of variables on one normal hemisphere -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem positiveReflectionTest_measurable (e : Sphere) {f : Sphere → ℝ≥0∞} (hf : Measurable f) :
    Measurable (positiveReflectionTest e f) := by
  apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
  · exact (show Measurable (fun n : Sphere => ENNReal.ofReal (inner ℝ e.1 n.1)) by fun_prop).mul
      (hf.comp (normalReflection_measurable e))
  · exact measurable_const

theorem sphereBallLift_radialReflection (e n : Sphere) (f : Sphere → ℝ≥0∞)
    (r : Ioi (0:ℝ)) :
    sphereBallLift e f (radialReflection e ((r:ℝ) • n.1)) =
      if (r:ℝ) < 1 then f (normalReflection e n) else 0 := by
  rw [sphereBallLift,sphereDirection_radialReflection e n r.property,
    radialReflection_norm,norm_smul,Real.norm_eq_abs,abs_of_pos r.property,
    mem_sphere_zero_iff_norm.mp n.property,mul_one]
  simp only [sq_lt_one_iff₀ (le_of_lt (show (0:ℝ) < r from r.property))]

theorem north_reflection_radial_integrand (f : Sphere → ℝ≥0∞) (n : Sphere)
    (r : Ioi (0:ℝ)) :
    (if 0 < ((r:ℝ) • n.1) 0 then
      ENNReal.ofReal (8*((r:ℝ) • n.1) 0*‖(r:ℝ) • n.1‖^2)*
        sphereBallLift northSphere f (radialReflection northSphere ((r:ℝ) • n.1)) else 0) =
      (if (r:ℝ) < 1 then ENNReal.ofReal ((r:ℝ)^3) else 0)*
        (8*positiveReflectionTest northSphere f n) := by
  have hrp : (0:ℝ) < r := r.property
  rw [sphereBallLift_radialReflection,norm_smul,Real.norm_eq_abs,abs_of_pos r.property,
    mem_sphere_zero_iff_norm.mp n.property,mul_one]
  simp only [PiLp.smul_apply,smul_eq_mul,positiveReflectionTest,northSphere,
    EuclideanSpace.inner_single_left,map_one,one_mul]
  have hp : 0 < (r:ℝ)*n.1 0 ↔ 0 < n.1 0 := mul_pos_iff_of_pos_left r.property
  simp only [hp]
  by_cases hn : 0 < n.1 0
  · rw [ite_eq_left hn,ite_eq_left hn]
    have hc : ENNReal.ofReal (8*((r:ℝ)*n.1 0)*(r:ℝ)^2) =
        ENNReal.ofReal ((r:ℝ)^3)*(8*ENNReal.ofReal (n.1 0)) := by
      rw [← ENNReal.ofReal_ofNat 8,← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 8),
        ← ENNReal.ofReal_mul (pow_nonneg hrp.le 3)]
      congr 1
      ring
    rw [hc]
    by_cases hr : (r:ℝ) < 1 <;> simp only [hr,ite_true, if_true,ite_false, if_false,mul_zero,zero_mul,mul_assoc]
  · simp [hn]

theorem positive_hemisphere_reflection (f : Sphere → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ n, f n ∂sphereArea) = 4*∫⁻ n, positiveReflectionTest northSphere f n ∂sphereArea := by
  have hA := positiveReflectionTest_measurable northSphere hf
  have hM : Measurable (fun x : Velocity => if 0 < x 0 then
      ENNReal.ofReal (8*x 0*‖x‖^2)*sphereBallLift northSphere f (radialReflection northSphere x)
        else 0) := by
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
    · exact (show Measurable (fun x : Velocity => ENNReal.ofReal (8*x 0*‖x‖^2)) by fun_prop).mul ((sphereBallLift_measurable northSphere hf).comp
        (radialReflection_continuous northSphere).measurable)
    · exact measurable_const
  have h := lintegral_radialReflection_north (sphereBallLift northSphere f)
  rw [sphereBallLift_integral northSphere hf] at h
  rw [← lintegral_indicator (measurableSet_lt measurable_const (by fun_prop))] at h
  change (3:ℝ≥0∞)⁻¹*(∫⁻ n, f n ∂sphereArea) =
    ∫⁻ x : Velocity, (if 0 < x 0 then _ else 0) at h
  rw [lintegral_velocity_polar hM] at h
  simp_rw [north_reflection_radial_integrand] at h
  rw [radial_cubic_factor (A := fun n => 8*positiveReflectionTest northSphere f n) (measurable_const.mul hA),lintegral_const_mul _ hA] at h
  have hh := congrArg (fun z : ℝ≥0∞ => 3*z) h
  have hthree : (3:ℝ≥0∞)*3⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have hscale : (3:ℝ≥0∞)*6⁻¹*8 = 4 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  simpa only [← mul_assoc,hthree,hscale,one_mul] using hh

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_NormalOutgoingSymmetry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.stateKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_pow_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.incomingChart_zero _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.normalChart_zero _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual normal-angle law is half the uniform sphere area measure -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem normalReflection_neg (e n : Sphere) : normalReflection e (-n) = normalReflection e n := by
  apply Subtype.ext
  exact normalReflection_neg_normal e n

theorem normalReflection_split (e n : Sphere) (f : Sphere → ℝ≥0∞) :
    ENNReal.ofReal |inner ℝ e.1 n.1| * f (normalReflection e n) =
      positiveReflectionTest e f n+positiveReflectionTest e f (-n) := by
  simp only [positiveReflectionTest,show (-n).1 = -n.1 from rfl,inner_neg_right,normalReflection_neg]
  by_cases h : 0 < inner ℝ e.1 n.1
  · simp [h,not_lt.mpr (neg_nonpos.mpr h.le),abs_of_pos h]
  · have hh : inner ℝ e.1 n.1 ≤ 0 := le_of_not_gt h
    by_cases hn : inner ℝ e.1 n.1 < 0
    · simp [h,neg_pos.mpr hn,abs_of_neg hn]
    · have hz : inner ℝ e.1 n.1 = 0 := le_antisymm hh (le_of_not_gt hn)
      simp [hz]

theorem normalReflectionLaw_north : normalReflectionLaw northSphere = (2:ℝ≥0∞)⁻¹ • sphereArea := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [normalReflectionLaw_lintegral _ hf,lintegral_smul_measure]
  simp_rw [normalReflection_split]
  rw [lintegral_add_left (positiveReflectionTest_measurable northSphere hf)]
  have hn : (∫⁻ n, positiveReflectionTest northSphere f (-n) ∂sphereArea) =
      ∫⁻ n, positiveReflectionTest northSphere f n ∂sphereArea := by
    have hm := positiveReflectionTest_measurable northSphere hf
    rw [← lintegral_map hm measurable_neg,sphereArea_antipodal.map_eq]
  rw [hn]
  have h := positive_hemisphere_reflection f hf
  rw [h]
  rw [← two_mul,smul_eq_mul,← mul_assoc]
  congr 1
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num

theorem normalReflectionLaw_uniform (e : Sphere) :
    normalReflectionLaw e = (2:ℝ≥0∞)⁻¹ • sphereArea := by
  let R : Velocity ≃ₗᵢ[ℝ] Velocity := (ℝ ∙ (northSphere.1-e.1))ᗮ.reflection
  have he : R northSphere.1 = e.1 := by
    apply Submodule.reflection_sub
    rw [mem_sphere_zero_iff_norm.mp northSphere.property,mem_sphere_zero_iff_norm.mp e.property]
  have he' : sphereIsometry R northSphere = e := Subtype.ext he
  rw [← he',← normalReflectionLaw_isometry,normalReflectionLaw_north,Measure.map_smul,
    (sphereIsometry_measurePreserving R).map_eq]

end BoltzmannNonuniqueness

end

end

section

/-! # Exact normal-angle and outgoing-sphere integrals for a fixed collision pair -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness

theorem normal_left_integral_of_direction (e : Sphere) {r : ℝ} (hr : 0 ≤ r)
    (v w : Velocity) (hg : v-w = r • e.1) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*f (scatterLeft v w n)
      ∂sphereArea) = (ENNReal.ofReal r*(2:ℝ≥0∞)⁻¹)*
        ∫⁻ n : Sphere, f (child v w n.1) ∂sphereArea := by
  have hc : Measurable (fun n : Sphere => f (child v w n.1)) := by
    apply hf.comp
    unfold child
    fun_prop
  have h := congrArg (fun μ : Measure Sphere => ∫⁻ n, f (child v w n.1) ∂μ)
    (normalReflectionLaw_uniform e)
  rw [normalReflectionLaw_lintegral e hc,lintegral_smul_measure] at h
  simp_rw [normalReflection_child e r hr v w hg] at h
  rw [smul_eq_mul] at h
  have hsc : Measurable (fun n : Sphere => scatterLeft v w n.1) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hm : Measurable (fun n : Sphere => ENNReal.ofReal |inner ℝ e.1 n.1| * f (scatterLeft v w n.1)) :=
    (show Measurable (fun n : Sphere => ENNReal.ofReal |inner ℝ e.1 n.1|) by fun_prop).mul
      (hf.comp hsc)
  calc
    _ = ∫⁻ n : Sphere, ENNReal.ofReal r*
        (ENNReal.ofReal |inner ℝ e.1 n.1| * f (scatterLeft v w n)) ∂sphereArea := by
      apply lintegral_congr
      intro n
      unfold collisionKernel normalComponent
      rw [hg,real_inner_smul_left,abs_mul,abs_of_nonneg hr,ENNReal.ofReal_mul hr]
      exact mul_assoc _ _ _
    _ = _ := by
      rw [lintegral_const_mul _ hm,h,mul_assoc]

theorem normal_left_integral (v w : Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*f (scatterLeft v w n)
      ∂sphereArea) = (ENNReal.ofReal ‖v-w‖*(2:ℝ≥0∞)⁻¹)*
        ∫⁻ n : Sphere, f (child v w n.1) ∂sphereArea := by
  by_cases h : v-w = 0
  · simp [collisionKernel,normalComponent,h]
  · let e := sphereDirection northSphere (v-w)
    apply normal_left_integral_of_direction e (norm_nonneg _) v w _ hf
    change v-w = ‖v-w‖ • (sphereDirection northSphere (v-w)).1
    rw [sphereDirection,dite_eq_right h,NormedSpace.norm_smul_normalize]

theorem outgoing_lintegral (v w : Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ u, f u ∂outgoing (v,w)) = (ENNReal.ofReal (4*Real.pi))⁻¹*
      ∫⁻ n : Sphere, f (child v w n.1) ∂sphereArea := by
  rw [outgoing_apply,lintegral_map hf (by unfold child; fun_prop),sphereProbability,
    lintegral_smul_measure,smul_eq_mul]

theorem normal_left_integral_outgoing (v w : Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*f (scatterLeft v w n)
      ∂sphereArea) = ENNReal.ofReal (2*Real.pi*‖v-w‖)*∫⁻ u, f u ∂outgoing (v,w) := by
  rw [normal_left_integral v w hf,outgoing_lintegral v w hf,← mul_assoc]
  congr 1
  have hp : 0 < 4*Real.pi := by positivity
  rw [← ENNReal.ofReal_inv_of_pos hp,← ENNReal.ofReal_mul (by positivity)]
  have hreal : 2*Real.pi*‖v-w‖*(4*Real.pi)⁻¹ = ‖v-w‖/2 := by field_simp <;> ring
  rw [hreal,ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
  norm_num [div_eq_mul_inv]

end BoltzmannNonuniqueness

end

end

section

/-! # Both normal-angle collision children have the same outgoing law -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness

theorem scatterRight_eq_left_swap (v w n : Velocity) :
    scatterRight v w n = scatterLeft w v n := by
  unfold scatterRight scatterLeft normalComponent
  rw [show w-v = -(v-w) by abel,inner_neg_left]
  module

theorem collisionKernel_swap (v w : Velocity) (n : Sphere) :
    collisionKernel v w n = collisionKernel w v n := by
  unfold collisionKernel normalComponent
  rw [show w-v = -(v-w) by abel,inner_neg_left,abs_neg]

theorem child_swap (v w n : Velocity) : child v w n = child w v n := by
  unfold child
  rw [norm_sub_rev w v,add_comm w v]

theorem outgoing_swap (v w : Velocity) : outgoing (v,w) = outgoing (w,v) := by
  rw [outgoing_apply,outgoing_apply]
  congr 1
  funext n
  exact child_swap v w n.1

theorem normal_right_integral_outgoing (v w : Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*f (scatterRight v w n)
      ∂sphereArea) = ENNReal.ofReal (2*Real.pi*‖v-w‖)*∫⁻ u, f u ∂outgoing (v,w) := by
  simp_rw [scatterRight_eq_left_swap,collisionKernel_swap v w]
  rw [normal_left_integral_outgoing w v hf,norm_sub_rev,outgoing_swap w v]

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CarlemanIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The normal-and-plane Jacobian in physical velocity coordinates -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem physicalFrame_measurable (n : Velocity) : Measurable (physicalFrame n) :=
  (MeasurableEquiv.toLp 2 V).measurable.comp
    (frame (WithLp.ofLp n) ‖transverse n‖).continuous_of_finiteDimensional.measurable

theorem transverse_norm_sq (n : Velocity) :
    ‖transverse n‖^2 = n 0^2+n 1^2 := by
  simp [transverse,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]

theorem normal_normSq (n : Velocity) : RedundantPlane.normSq (WithLp.ofLp n) = ‖n‖^2 := by
  simp [RedundantPlane.normSq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]

theorem physicalFrame_map_volume {n : Velocity} (hn : ‖n‖ = 1)
    (ht : transverse n ≠ 0) :
    Measure.map (physicalFrame n) (volume : Measure V) = ENNReal.ofReal ‖transverse n‖ • volume := by
  have hN : RedundantPlane.normSq (WithLp.ofLp n) = 1 := by rw [normal_normSq,hn,one_pow]
  have hF := unit_frame_map_volume (norm_pos_iff.mpr ht) (transverse_norm_sq n) hN
  have hm := (frame (WithLp.ofLp n) ‖transverse n‖).continuous_of_finiteDimensional.measurable
  rw [physicalFrame,← Measure.map_map (MeasurableEquiv.toLp 2 V).measurable hm,hF,
    Measure.map_smul]
  · congr 1
    exact (PiLp.volume_preserving_toLp (Fin 3)).map_eq

theorem lintegral_physicalFrame {n : Velocity} (hn : ‖n‖ = 1)
    (ht : transverse n ≠ 0) {F : Velocity → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ w : Velocity, F w) = ENNReal.ofReal (‖transverse n‖⁻¹) *
      ∫⁻ q : V, F (physicalFrame n q) := by
  have h := lintegral_map (μ := (volume : Measure V)) hF (physicalFrame_measurable n)
  rw [physicalFrame_map_volume hn ht,lintegral_smul_measure,smul_eq_mul] at h
  have hr := norm_pos_iff.mpr ht
  rw [ENNReal.ofReal_inv_of_pos hr]
  rw [← h,← mul_assoc,ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hr).ne'
    ENNReal.ofReal_ne_top,one_mul]

theorem normalComponent_physicalFrame {n : Velocity} (hn : ‖n‖ = 1)
    (ht : transverse n ≠ 0) (v : Velocity) (q : V) :
    normalComponent v (v+physicalFrame n q) n = q 0 := by
  have h := frame_dot (norm_pos_iff.mpr ht) (transverse_norm_sq n) q
  rw [normal_normSq,hn,one_pow,mul_one] at h
  change inner ℝ (v-(v+physicalFrame n q)) n = q 0
  rw [show v-(v+physicalFrame n q) = -physicalFrame n q by abel,inner_neg_left,real_inner_comm]
  have he : inner ℝ n (physicalFrame n q) =
      WithLp.ofLp n ⬝ᵥ frame (WithLp.ofLp n) ‖transverse n‖ q := by
    simp [physicalFrame,PiLp.inner_apply,RCLike.inner_apply,dotProduct,mul_comm]
  rw [he,h,neg_neg]

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Matching the tangent columns with the manuscript's collision-plane chart -/
noncomputable section
open MeasureTheory Matrix
open scoped Matrix RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseLine BoltzmannNonuniqueness.TransverseAverage
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem axial_planeFrame (n : Velocity) (z s : ℝ) : axial (planeFrame n z s) = z := by
  simp [planeFrame,physicalFrame,frame_apply,axial]

theorem transverse_planeFrame (n : Velocity) (z s : ℝ) :
    transverse (planeFrame n z s) =
      line (direction (transverse n)) (-n 2/‖transverse n‖*z) s := by
  apply (WithLp.ext_iff 2).mpr
  funext i
  fin_cases i <;>
    simp [planeFrame,physicalFrame,frame_apply,transverse,line,quarterTurn,direction] <;> ring

theorem planeFrame_eq_origin_chart (n : Velocity) (z s : ℝ) :
    planeFrame n z s = chart 0 (-n) z s := by
  apply split.injective
  rw [split_apply,split_apply]
  apply Prod.ext
  · rw [axial_planeFrame,axial_chart]
    simp [axial]
  · rw [transverse_planeFrame,transverse_chart]
    have hn : normal 0 (-n) = transverse n := by
      simp [normal]
    rw [hn]
    simp [offset,PlaneChart.slope,normal,axial,show transverse (0 : Velocity) = 0 from rfl]
    congr 1
    ring

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The positive radial normal recovers the exact translated collision chart -/
noncomputable section
open scoped RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseLine BoltzmannNonuniqueness.TransverseAverage
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem planeFrame_orthogonal {n : Velocity} (ht : transverse n ≠ 0) (z s : ℝ) :
    inner ℝ n (planeFrame n z s) = 0 := by
  have hn : normal 0 (-n) ≠ 0 := by simpa [normal,transverse_sub] using ht
  have h := chart_on_plane 0 (-n) z s hn
  simpa only [zero_sub,neg_neg,sub_zero,← planeFrame_eq_origin_chart] using h

theorem normal_scaled (v n : Velocity) (a : ℝ) : normal v (v-a • n) = a • transverse n := by
  unfold normal
  rw [show v-(v-a • n) = a • n by module]
  rfl

theorem direction_pos_scaled {a : ℝ} (ha : 0 < a) (u : Transverse) :
    direction (a • u) = direction u := by
  simp [direction,norm_smul,Real.norm_eq_abs,abs_of_pos ha,smul_smul,ha.ne']

theorem positive_chart_frame (v : Velocity) {n : Velocity} (ht : transverse n ≠ 0)
    {a : ℝ} (ha : 0 < a) (z s : ℝ) :
    chart v (v-a • n) z (s+RedundantPlane.tangentOffset v (v-a • n)) =
      v+planeFrame n z s := by
  have hn : normal v (v-a • n) ≠ 0 := by
    rw [normal_scaled]
    exact smul_ne_zero ha.ne' ht
  have hd : direction (normal v (v-a • n)) = direction (transverse n) := by
    rw [normal_scaled,direction_pos_scaled ha]
  have hp : inner ℝ (v-(v-a • n)) (v+planeFrame n z s-v) = 0 := by
    rw [show v-(v-a • n) = a • n by module,add_sub_cancel_left,real_inner_smul_left,
      planeFrame_orthogonal ht,mul_zero]
  have hc := chart_recovers v (v-a • n) (v+planeFrame n z s) hn hp
  have hz : axial (v+planeFrame n z s)-axial v = z := by
    change axial v+axial (planeFrame n z s)-axial v = z
    rw [axial_planeFrame]
    ring
  have hs : inner ℝ (quarterTurn (direction (normal v (v-a • n))))
      (transverse (v+planeFrame n z s)) = s+RedundantPlane.tangentOffset v (v-a • n) := by
    change inner ℝ (quarterTurn (direction (normal v (v-a • n))))
      (transverse v+transverse (planeFrame n z s)) = _
    rw [inner_add_right,transverse_planeFrame,hd,
      inner_quarterTurn_line _ _ _ (norm_direction ht)]
    rw [RedundantPlane.tangentOffset,hd,add_comm]
  rwa [hz,hs] at hc

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Removing the symmetric average from the nonnegative gain -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness

theorem scatter_complement_left (v w n : Velocity) :
    v+w-scatterLeft v w n = scatterRight v w n := by
  unfold scatterLeft scatterRight
  module

theorem scatter_complement_right (v w n : Velocity) :
    v+w-scatterRight v w n = scatterLeft v w n := by
  unfold scatterLeft scatterRight
  module

theorem normal_cross_integral_symm (v w : Velocity) {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*
      f (scatterLeft v w n)*g (scatterRight v w n) ∂sphereArea) =
    ∫⁻ n : Sphere, ENNReal.ofReal (collisionKernel v w n)*
      g (scatterLeft v w n)*f (scatterRight v w n) ∂sphereArea := by
  let H : Velocity → ℝ≥0∞ := fun u => f u*g (v+w-u)
  have hH : Measurable H := hf.mul (hg.comp (by fun_prop))
  have h := (normal_left_integral_outgoing v w hH).trans
    (normal_right_integral_outgoing v w hH).symm
  simpa only [H,scatter_complement_left,scatter_complement_right,mul_assoc,
    mul_left_comm,mul_comm] using h

theorem rawGainIntegrand_measurable {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    Measurable (rawGainIntegrand f g v) := by
  have hleft : Measurable (fun p : Velocity × Sphere => scatterLeft v p.1 p.2) := by
    unfold scatterLeft normalComponent
    fun_prop
  have hright : Measurable (fun p : Velocity × Sphere => scatterRight v p.1 p.2) := by
    unfold scatterRight normalComponent
    fun_prop
  have hker : Measurable (fun p : Velocity × Sphere => ENNReal.ofReal (collisionKernel v p.1 p.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact (hker.mul (hf.comp hleft)).mul (hg.comp hright)

theorem rawGain_eq_lintegral {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    rawNonnegativeGain f g v = ∫⁻ p, rawGainIntegrand f g v p ∂gainPairMeasure := by
  exact (lintegral_prod _ (rawGainIntegrand_measurable hf hg v).aemeasurable).symm

theorem rawNonnegativeGain_symm {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    rawNonnegativeGain f g v = rawNonnegativeGain g f v := by
  apply lintegral_congr
  intro w
  exact normal_cross_integral_symm v w hf hg

theorem nonnegativeGain_eq_raw {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    nonnegativeGain f g v = rawNonnegativeGain f g v := by
  have hfg := rawGainIntegrand_measurable hf hg v
  have hgf := rawGainIntegrand_measurable hg hf v
  have he : nonnegativeGain f g v =
      ∫⁻ p, (2 : ℝ≥0∞)⁻¹*(rawGainIntegrand f g v p+rawGainIntegrand g f v p)
        ∂gainPairMeasure := by
    apply lintegral_congr
    intro p
    unfold rawGainIntegrand
    rw [div_eq_mul_inv,mul_add,mul_add]
    ac_rfl
  rw [he]
  change (∫⁻ p, (2 : ℝ≥0∞)⁻¹*((rawGainIntegrand f g v+rawGainIntegrand g f v) p)
    ∂gainPairMeasure) = _
  rw [lintegral_const_mul _ (hfg.add hgf)]
  change (2 : ℝ≥0∞)⁻¹ * (∫⁻ p, rawGainIntegrand f g v p+rawGainIntegrand g f v p
    ∂gainPairMeasure) = _
  rw [lintegral_add_left hfg,
    ← rawGain_eq_lintegral hf hg v,← rawGain_eq_lintegral hg hf v,
    ← rawNonnegativeGain_symm hf hg v,← two_mul,← mul_assoc]
  rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), one_mul]

end BoltzmannNonuniqueness

end

end

section

/-! # Measurable collision-plane averages and their orientation invariance -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal Matrix
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem physicalFrame_joint_measurable :
    Measurable (fun x : Velocity × V => physicalFrame x.1 x.2) := by
  apply (MeasurableEquiv.toLp 2 V).measurable.comp
  simp_rw [frame_apply]
  apply Measurable.of_eval
  intro i
  fin_cases i <;> fun_prop

attribute [local irreducible] physicalFrame frame

theorem planeFrame_joint_measurable :
    Measurable (fun x : Velocity × (ℝ × ℝ) => planeFrame x.1 x.2.1 x.2.2) := by
  unfold planeFrame
  have hm : Measurable (fun x : Velocity × (ℝ × ℝ) => (x.1, (![0,x.2.1,x.2.2] : V))) := by
    apply measurable_fst.prodMk
    apply Measurable.of_eval
    intro i
    fin_cases i <;> fun_prop
  exact physicalFrame_joint_measurable.comp hm

attribute [local irreducible] planeFrame

theorem planeAverage_measurable {g : Velocity → ℝ≥0∞} (hg : Measurable g)
    (v : Velocity) : Measurable (planeAverage g v) := by
  have hm : Measurable (fun x : (Velocity × ℝ) × ℝ =>
      g (v+planeFrame x.1.1 x.1.2 x.2)) := by
    apply hg.comp
    apply measurable_const.add
    exact planeFrame_joint_measurable.comp
      ((measurable_fst.fst).prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact hm.lintegral_prod_right'.lintegral_prod_right'

theorem planeFrame_neg (n : Velocity) (z s : ℝ) :
    planeFrame (-n) z s = planeFrame n z (-s) := by
  have ht : transverse (-n) = -transverse n := rfl
  ext i
  fin_cases i <;> simp [planeFrame,physicalFrame,frame_apply,ht]

theorem planeAverage_neg {g : Velocity → ℝ≥0∞} (hg : Measurable g)
    (v n : Velocity) : planeAverage g v (-n) = planeAverage g v n := by
  apply lintegral_congr
  intro z
  simp_rw [planeFrame_neg]
  have hm : Measurable (fun s => g (v+planeFrame n z s)) := by
    apply hg.comp
    apply measurable_const.add
    exact planeFrame_joint_measurable.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have h := lintegral_map (μ := (volume : Measure ℝ)) hm measurable_neg
  rw [Measure.map_neg_eq_self] at h
  exact h.symm

theorem planeAverage_eq_chart (g : Velocity → ℝ≥0∞) (v : Velocity)
    {n : Velocity} (ht : transverse n ≠ 0) {a : ℝ} (ha : 0 < a) :
    planeAverage g v n = ∫⁻ z : ℝ, ∫⁻ s : ℝ, g (PlaneChart.chart v (v-a • n) z s) := by
  apply lintegral_congr
  intro z
  calc
    _ = ∫⁻ s : ℝ, g (PlaneChart.chart v (v-a • n) z
        (s+RedundantPlane.tangentOffset v (v-a • n))) := by
      apply lintegral_congr
      intro s
      rw [positive_chart_frame v ht ha]
    _ = _ := lintegral_add_right_eq_self
      (fun s : ℝ => g (PlaneChart.chart v (v-a • n) z s)) _

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Splitting normal displacement from the two collision-plane parameters -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal Matrix RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem physicalFrame_decomposition (n : Velocity) (q : V) :
    physicalFrame n q = (-q 0) • n + physicalFrame n ![0,q 1,q 2] := by
  ext i
  fin_cases i <;> simp [physicalFrame,frame_apply] <;> ring

theorem scatterLeft_frame {n : Velocity} (hn : ‖n‖ = 1) (ht : transverse n ≠ 0)
    (v : Velocity) (q : V) :
    scatterLeft v (v+physicalFrame n q) n = v-q 0 • n := by
  unfold scatterLeft
  rw [normalComponent_physicalFrame hn ht]

theorem scatterRight_frame {n : Velocity} (hn : ‖n‖ = 1) (ht : transverse n ≠ 0)
    (v : Velocity) (q : V) :
    scatterRight v (v+physicalFrame n q) n = v+physicalFrame n ![0,q 1,q 2] := by
  unfold scatterRight
  rw [normalComponent_physicalFrame hn ht,physicalFrame_decomposition]
  module

theorem lintegral_shifted_frame {n : Velocity} (hn : ‖n‖ = 1) (ht : transverse n ≠ 0)
    (v : Velocity) {F : Velocity → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ w : Velocity, F w) = ENNReal.ofReal (‖transverse n‖⁻¹) *
      ∫⁻ a : ℝ, ∫⁻ z : ℝ, ∫⁻ s : ℝ, F (v+physicalFrame n ![a,z,s]) := by
  have hm : Measurable (fun w : Velocity => F (v+w)) := hF.comp (by fun_prop)
  have h := lintegral_physicalFrame hn ht hm
  rw [lintegral_add_left_eq_self] at h
  rw [h]
  congr 1
  let G : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun x => F (v+physicalFrame n ![x.1,x.2.1,x.2.2])
  have hg : Measurable G := by
    apply hF.comp
    apply measurable_const.add
    apply (physicalFrame_measurable n).comp
    apply Measurable.of_eval
    intro i
    fin_cases i <;> fun_prop
  have he : (fun q : V => F (v+physicalFrame n q)) = G ∘ RedundantPlane.splitThree := by
    funext q
    dsimp [G,RedundantPlane.splitThree_apply,Function.comp_def]
    congr 2
  rw [he]
  change (∫⁻ q : V, G (RedundantPlane.splitThree q)) = _
  rw [RedundantPlane.splitThree_measurePreserving.lintegral_comp hg]
  rw [MeasureTheory.Measure.volume_eq_prod,lintegral_prod _ hg.aemeasurable]
  apply lintegral_congr
  intro a
  rw [MeasureTheory.Measure.volume_eq_prod]
  exact lintegral_prod _ ((hg.comp measurable_prodMk_left).aemeasurable)

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The exceptional axial normal directions have zero sphere area -/
noncomputable section
open MeasureTheory Set
open scoped Pointwise ENNReal
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem sphere_ae_transverse_ne_zero :
    ∀ᵐ n : Sphere ∂sphereArea, transverse n.1 ≠ 0 := by
  have hm : MeasurableSet {n : Sphere | transverse n.1 = 0} := by
    apply measurableSet_eq_fun _ measurable_const
    unfold transverse
    fun_prop
  have hzero : (volume : Measure Velocity) {x | transverse x = 0} = 0 := by
    simpa only [not_not] using ae_iff.mp SheetApplication.ae_transverse_ne_zero
  have hcone : (volume : Measure Velocity)
      (Ioo (0 : ℝ) 1 • ((↑) '' {n : Sphere | transverse n.1 = 0})) = 0 := by
    apply measure_mono_null _ hzero
    rintro x ⟨r,-,y,⟨n,hn,rfl⟩,rfl⟩
    change transverse (r • n.1) = 0
    have he : transverse (r • n.1) = r • transverse n.1 := rfl
    rw [he,hn,smul_zero]
  rw [ae_iff]
  simp only [not_not]
  change (volume : Measure Velocity).toSphere {n : Sphere | transverse n.1 = 0} = 0
  rw [Measure.toSphere_apply' _ hm,hcone,mul_zero]

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Splitting an even nonnegative integral at zero -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CarlemanCoordinates

theorem lintegral_even_halfline {F : ℝ → ℝ≥0∞} (hF : Measurable F)
    (heven : ∀ a, F (-a) = F a) :
    (∫⁻ a : ℝ, F a) = 2 * ∫⁻ a in Ioi (0 : ℝ), F a := by
  have hp := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
  have he : Neg.neg ⁻¹' Ioi (0 : ℝ) = Iio (0 : ℝ) := by ext a; simp
  rw [he] at hp
  have hi := hp.lintegral_comp hF
  simp only [heven] at hi
  have hu : Iio (0 : ℝ) ∪ Ioi 0 = ({0} : Set ℝ)ᶜ := by
    ext a
    simp only [mem_union,mem_Iio,mem_Ioi,mem_compl_iff,mem_singleton_iff]
    constructor
    · rintro (h | h)
      · exact h.ne
      · exact h.ne'
    · exact lt_or_gt_of_ne
  have hd : Disjoint (Iio (0 : ℝ)) (Ioi 0) := by
    apply disjoint_left.mpr
    intro a ha hb
    change a < 0 at ha
    change 0 < a at hb
    linarith
  have h := lintegral_union (μ := (volume : Measure ℝ)) (f := F) measurableSet_Ioi hd
  rw [hu,restrict_compl_singleton] at h
  rw [h,hi,two_mul]

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The gain integral after splitting the incoming velocity along a fixed normal -/
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal Matrix
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] planeFrame physicalFrame planeAverage

theorem planePoint_measurable (v n : Velocity) :
    Measurable (fun p : ℝ × ℝ => v+planeFrame n p.1 p.2) := by
  apply measurable_const.add
  exact planeFrame_joint_measurable.comp (measurable_const.prodMk measurable_id)

theorem lintegral_plane_const_mul (c : ℝ≥0∞) {g : Velocity → ℝ≥0∞}
    (hg : Measurable g) (v n : Velocity) :
    (∫⁻ z : ℝ, ∫⁻ s : ℝ, c*g (v+planeFrame n z s)) = c*planeAverage g v n := by
  unfold planeAverage
  have hm := hg.comp (planePoint_measurable v n)
  calc
    _ = ∫⁻ z : ℝ, c * ∫⁻ s : ℝ, g (v+planeFrame n z s) := by
      apply lintegral_congr
      intro z
      exact lintegral_const_mul c (hm.comp measurable_prodMk_left)
    _ = _ := lintegral_const_mul c hm.lintegral_prod_right'

theorem normal_gain_integral {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity)
    {n : Velocity} (hn : ‖n‖ = 1) (ht : transverse n ≠ 0) :
    (∫⁻ w : Velocity, ENNReal.ofReal (collisionKernel v w n)*
      f (scatterLeft v w n)*g (scatterRight v w n)) =
    ENNReal.ofReal (‖transverse n‖⁻¹) *
      ∫⁻ a : ℝ, ENNReal.ofReal |a| * f (v-a • n)*planeAverage g v n := by
  have hm : Measurable (fun w : Velocity => ENNReal.ofReal (collisionKernel v w n)*
      f (scatterLeft v w n)*g (scatterRight v w n)) := by
    have hl : Measurable (fun w : Velocity => scatterLeft v w n) := by
      unfold scatterLeft normalComponent
      fun_prop
    have hr : Measurable (fun w : Velocity => scatterRight v w n) := by
      unfold scatterRight normalComponent
      fun_prop
    have hk : Measurable (fun w : Velocity => ENNReal.ofReal (collisionKernel v w n)) := by
      unfold collisionKernel normalComponent
      fun_prop
    exact (hk.mul (hf.comp hl)).mul (hg.comp hr)
  rw [lintegral_shifted_frame hn ht v hm]
  congr 1
  apply lintegral_congr
  intro a
  simp_rw [collisionKernel,normalComponent_physicalFrame hn ht,
    scatterLeft_frame hn ht,scatterRight_frame hn ht]
  change (∫⁻ z : ℝ, ∫⁻ s : ℝ, (ENNReal.ofReal |a| * f (v-a • n))*
    g (v+physicalFrame n ![0,z,s])) = _
  simpa only [planeFrame] using lintegral_plane_const_mul (ENNReal.ofReal |a| * f (v-a • n)) hg v n

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # A measurable radial integrand, even after integration over the sphere -/
noncomputable section
open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] planeAverage planeFrame physicalFrame

theorem radialIntegrand_measurable {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    Measurable (Function.uncurry (radialIntegrand f g v)) := by
  have hr : Measurable (fun x : ℝ × Sphere => ENNReal.ofReal (‖transverse x.2.1‖⁻¹)) := by
    unfold transverse
    fun_prop
  have ha : Measurable (fun x : ℝ × Sphere => ENNReal.ofReal |x.1|) := by fun_prop
  have hp : Measurable (fun x : ℝ × Sphere => f (v-x.1 • x.2.1)) := hf.comp (by fun_prop)
  have hq : Measurable (fun x : ℝ × Sphere => planeAverage g v x.2.1) :=
    (planeAverage_measurable hg v).comp (measurable_subtype_coe.comp measurable_snd)
  exact hr.mul ((ha.mul hp).mul hq)

theorem radialIntegrand_neg {f g : Velocity → ℝ≥0∞}
    (hg : Measurable g) (v : Velocity) (a : ℝ) (n : Sphere) :
    radialIntegrand f g v (-a) n = radialIntegrand f g v a (-n) := by
  have ht : transverse (-n.1) = -transverse n.1 := rfl
  simp [radialIntegrand,ht,planeAverage_neg hg,neg_smul,smul_neg]

attribute [local irreducible] radialIntegrand

theorem angularRadial_even {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) (a : ℝ) :
    (∫⁻ n : Sphere, radialIntegrand f g v (-a) n ∂sphereArea) =
      ∫⁻ n : Sphere, radialIntegrand f g v a n ∂sphereArea := by
  simp_rw [radialIntegrand_neg hg]
  exact sphereArea_antipodal.lintegral_comp
    ((radialIntegrand_measurable hf hg v).comp measurable_prodMk_left)

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The measurable Carleman profile and its radial weight -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] chart physicalFrame planeFrame

theorem chartProfile_measurable {g : Velocity → ℝ≥0∞}
    (hg : Measurable g) (v : Velocity) : Measurable (chartProfile g v) := by
  have hm : Measurable (fun x : (Velocity × ℝ) × ℝ => g (chart v x.1.1 x.1.2 x.2)) :=
    hg.comp ((ChartKernel.measurable_point v).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hn : Measurable (fun p : Velocity => ENNReal.ofReal (‖normal v p‖⁻¹)) := by
    unfold normal
    exact ((ChartKernel.measurable_transverse.comp (measurable_const.sub measurable_id)).norm.inv).ennreal_ofReal
  exact hn.mul hm.lintegral_prod_right'.lintegral_prod_right'

theorem chartGain_eq_density_integral {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    chartGain (volume.withDensity f) g v = 2 * ∫⁻ p : Velocity, f p*chartProfile g v p := by
  change 2 * (∫⁻ p : Velocity, chartProfile g v p ∂volume.withDensity f) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hf (chartProfile_measurable hg v)]
  rfl

theorem radial_chart_weight {v n : Velocity} (ht : transverse n ≠ 0)
    {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal (a^2) * ENNReal.ofReal (‖normal v (v-a • n)‖⁻¹) =
      ENNReal.ofReal (‖transverse n‖⁻¹) * ENNReal.ofReal a := by
  rw [normal_scaled,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
  rw [← ENNReal.ofReal_mul (sq_nonneg a),← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _))]
  congr 1
  field_simp [ha.ne', (norm_pos_iff.mpr ht).ne']

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # Polar coordinates identify the chart profile with the positive normal integral -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] PlaneChart.chart physicalFrame planeFrame planeAverage

theorem lintegral_positive_radial_weight {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    (∫⁻ a : Ioi (0 : ℝ), H a ∂Measure.volumeIoiPow 2) =
      ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (a^2)*H a := by
  unfold Measure.volumeIoiPow
  calc
    _ = ∫⁻ a : Ioi (0 : ℝ), ENNReal.ofReal ((a : ℝ)^2)*H a
        ∂volume.comap Subtype.val := by
      simpa only [Pi.mul_apply,Function.comp_apply] using
        lintegral_withDensity_eq_lintegral_mul (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ))
          (show Measurable (fun a : Ioi (0 : ℝ) => ENNReal.ofReal ((a : ℝ)^2)) by fun_prop)
          (hH.comp measurable_subtype_coe)
    _ = _ := lintegral_subtype_comap measurableSet_Ioi
      (fun a : ℝ => ENNReal.ofReal (a^2)*H a)

theorem radial_chart_integrand {f g : Velocity → ℝ≥0∞} (v : Velocity)
    {n : Sphere} (ht : transverse n.1 ≠ 0) {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal (a^2)*(f (v-a • n.1)*chartProfile g v (v-a • n.1)) =
      radialIntegrand f g v a n := by
  rw [chartProfile,← planeAverage_eq_chart g v ht ha]
  calc
    _ = (ENNReal.ofReal (a^2)*ENNReal.ofReal (‖PlaneChart.normal v (v-a • n.1)‖⁻¹))*
        (f (v-a • n.1)*planeAverage g v n.1) := by ac_rfl
    _ = _ := by
      rw [radial_chart_weight ht ha]
      simp only [radialIntegrand,abs_of_pos ha]
      ac_rfl

theorem chart_integral_eq_positive_radial {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    (∫⁻ p : Velocity, f p*chartProfile g v p) =
      ∫⁻ n : Sphere, ∫⁻ a in Ioi (0 : ℝ), radialIntegrand f g v a n ∂volume ∂sphereArea := by
  let H : Velocity → ℝ≥0∞ := fun p => f p*chartProfile g v p
  have hH : Measurable H := hf.mul (chartProfile_measurable hg v)
  have hT : Measurable (fun y : Velocity => H (v-y)) := hH.comp (by fun_prop)
  calc
    _ = ∫⁻ y : Velocity, H (v-y) := by
      calc
        _ = ∫⁻ y : Velocity, H (v+y) := (lintegral_add_left_eq_self H v).symm
        _ = _ := (lintegral_neg_eq_self (fun y : Velocity => H (v+y))).symm
    _ = ∫⁻ n : Sphere, ∫⁻ a : Ioi (0 : ℝ), H (v-(a:ℝ) • n.1)
        ∂Measure.volumeIoiPow 2 ∂sphereArea := lintegral_velocity_polar hT
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [sphere_ae_transverse_ne_zero] with n hn
      calc
        _ = ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (a^2)*H (v-a • n.1) :=
          lintegral_positive_radial_weight (H := fun a : ℝ => H (v-a • n.1))
            (hH.comp (by fun_prop))
        _ = _ := by
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro a ha
          exact radial_chart_integrand v hn ha

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The full gain as twice a positive radial integral -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.CarlemanCoordinates

attribute [local irreducible] planeAverage planeFrame physicalFrame radialIntegrand

theorem rawGain_eq_signed_radial {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    rawNonnegativeGain f g v =
      ∫⁻ a : ℝ, ∫⁻ n : Sphere, radialIntegrand f g v a n ∂sphereArea := by
  have hraw := rawGainIntegrand_measurable hf hg v
  have hrad := radialIntegrand_measurable hf hg v
  calc
    _ = ∫⁻ n : Sphere, ∫⁻ w : Velocity, ENNReal.ofReal (collisionKernel v w n)*
        f (scatterLeft v w n)*g (scatterRight v w n) ∂volume ∂sphereArea :=
      lintegral_lintegral_swap hraw.aemeasurable
    _ = ∫⁻ n : Sphere, ∫⁻ a : ℝ, radialIntegrand f g v a n ∂volume ∂sphereArea := by
      apply lintegral_congr_ae
      filter_upwards [sphere_ae_transverse_ne_zero] with n hn
      have hunit : ‖n.1‖ = 1 := mem_sphere_zero_iff_norm.mp n.property
      rw [normal_gain_integral hf hg v hunit hn]
      simpa only [radialIntegrand,Pi.mul_apply,Function.comp_apply] using (lintegral_const_mul _
        (((show Measurable (fun a : ℝ => ENNReal.ofReal |a|) by fun_prop).mul
          (hf.comp (by fun_prop))).mul_const _)).symm
    _ = _ := (lintegral_lintegral_swap hrad.aemeasurable).symm

theorem rawGain_eq_positive_radial {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    rawNonnegativeGain f g v =
      2 * ∫⁻ a in Ioi (0 : ℝ), ∫⁻ n : Sphere, radialIntegrand f g v a n ∂sphereArea := by
  rw [rawGain_eq_signed_radial hf hg v]
  exact lintegral_even_halfline (radialIntegrand_measurable hf hg v).lintegral_prod_right'
    (angularRadial_even hf hg v)

end BoltzmannNonuniqueness.CarlemanCoordinates

end

end

section

/-! # The nonnegative hard-sphere Carleman identity

This proves the precise density identity used from Gamba--Panferov--Villani,
ARMA 194 (2009), Appendix C, Lemma 16 and its hard-sphere specialization.
Only nonnegative measurable densities are used; no identity for atomic
incoming measures is asserted.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness
open CarlemanCoordinates

theorem nonnegativeGain_eq_chartGain {f g : Velocity → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (v : Velocity) :
    nonnegativeGain f g v = chartGain (volume.withDensity f) g v := by
  rw [nonnegativeGain_eq_raw hf hg v,rawGain_eq_positive_radial hf hg v,
    chartGain_eq_density_integral hf hg v,chart_integral_eq_positive_radial hf hg v]
  congr 1
  exact lintegral_lintegral_swap (radialIntegrand_measurable hf hg v).aemeasurable

namespace Published

theorem gpv2009CarlemanInput : GPV2009CarlemanInput := by
  intro f g hf hg
  exact Filter.Eventually.of_forall (nonnegativeGain_eq_chartGain hf hg)

end Published
end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PeriodicExistenceReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Nonuniqueness from averaging and periodic existence -/
namespace BoltzmannNonuniqueness

theorem nonuniqueness_without_carleman_input
    (hGLPS : Published.GLPS1988Proposition3)
    (hperiodic : PeriodicExistenceInput) : NonuniquenessStatement :=
  nonuniqueness_without_compactness_inputs_q80 Published.gpv2009CarlemanInput hGLPS hperiodic

end BoltzmannNonuniqueness


end

section

/-! # Nonuniqueness assuming periodic global existence -/
namespace BoltzmannNonuniqueness

theorem nonuniqueness_without_averaging_input
    (hperiodic : PeriodicExistenceInput) : NonuniquenessStatement :=
  nonuniqueness_without_carleman_input Published.glps1988Proposition3_q80 hperiodic

end BoltzmannNonuniqueness


end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_UnconditionalMainProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Global nonuniqueness via periodic continuation -/
namespace BoltzmannNonuniqueness

theorem nonuniqueness_proved : NonuniquenessStatement :=
  nonuniqueness_without_averaging_input periodicExistenceInput_q80

end BoltzmannNonuniqueness

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nonuniqueness for the periodic hard-sphere Boltzmann equation

The exact main statement includes two distinct global renormalized solutions of one
bounded-velocity initial datum, with local mass conservation, total momentum conservation, energy and
entropy-dissipation inequalities, and strong early L1 continuity with integrable collisions.
-/
namespace BoltzmannNonuniqueness

theorem nonuniqueness_oai :
    ∃ f₀ : Density, BoundedVelocitySupport f₀ ∧
      ∃ (F G : Evolution) (T : ℝ), AdmissibleGlobal f₀ F ∧ AdmissibleGlobal f₀ G ∧
        StrongEarly T F ∧ StrongEarly T G ∧
        ∃ t ∈ Set.Icc 0 T, ¬(F t =ᵐ[MeasureTheory.volume] G t) :=
  nonuniqueness_proved

end BoltzmannNonuniqueness

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.nonuniqueness_oai := @OAI.BoltzmannNonuniqueness.nonuniqueness_oai
