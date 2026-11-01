-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.GeometricBackground.geometric_common_block_growth_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:06:56.547011+00:00
-- url     : https://prove2.me/submissions/eab388be-e688-4aa1-ada2-cfacef76f2dd

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_ReferenceGeometry_uniform_damped_finite_block_growth_q80

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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceCollisionGeometry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.stateKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_pow_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.incomingChart_zero _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.normalChart_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Stability of the finite collision paths used in the branching block -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem child_lipschitz (v w v' w' n : V) (hn : ‖n‖ = 1) :
    ‖child v w n-child v' w' n‖ ≤ ‖v-v'‖+‖w-w'‖ := by
  have he : child v w n-child v' w' n =
      (1/2:ℝ) • ((v-v')+(w-w'))+((‖v-w‖-‖v'-w'‖)/2) • n := by
    unfold child
    module
  rw [he]
  have hsum := norm_add_le ((1/2:ℝ) • ((v-v')+(w-w')))
    (((‖v-w‖-‖v'-w'‖)/2) • n)
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hn,mul_one,
    abs_of_pos (by norm_num : (0:ℝ) < 1/2),abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)] at hsum
  have hdiff : ‖(v-w)-(v'-w')‖ ≤ ‖v-v'‖+‖w-w'‖ := by
    calc
      _ = ‖(v-v')-(w-w')‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hrad := (abs_norm_sub_norm_le (v-w) (v'-w')).trans hdiff
  have hc := norm_add_le (v-v') (w-w')
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The two-beam reference jump law and its sign probabilities -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem minusProbability_eq (e v : V) (he : ‖e‖ = 1) :
    1-plusProbability e v = ‖v+e‖/(‖v-e‖+‖v+e‖) := by
  have hd : 0 < ‖v-e‖+‖v+e‖ := lt_of_lt_of_le (by norm_num) (two_beam_distance_lower v e he)
  unfold plusProbability
  field_simp
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Normalization of the reference histories retained in the velocity ball -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem retainedJump_univ (e v : V) (hp : retention e v ≠ 0) :
    retainedJump e v univ = 1 := by
  rw [retainedJump_apply,Measure.smul_apply,Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hp (retention_ne_top e v)

/-- Each collision rate times its conditional jump law recovers the retained branching rate. -/
theorem retainedJump_rate_identity (e v : V) (c : ℝ≥0∞) (hp : retention e v ≠ 0) :
    (c*retention e v) • retainedJump e v = c • (referenceJump e v).restrict referenceRegion := by
  rw [retainedJump_apply,smul_smul,mul_assoc,
    ENNReal.mul_inv_cancel hp (retention_ne_top e v),mul_one]

theorem retainedRate_measure_identity (e v : V)
    (hp : retention e v ≠ 0) :
    ENNReal.ofReal (retainedRate e v) • retainedJump e v =
      ENNReal.ofReal (2*frequency v e) • (referenceJump e v).restrict referenceRegion := by
  have hν : 0 ≤ frequency v e := by unfold frequency; positivity
  have hnonneg : 0 ≤ 2*frequency v e := by positivity
  have hr : retainedRate e v = (2*frequency v e)*(retention e v).toReal := by
    unfold retainedRate
    ring
  rw [hr,ENNReal.ofReal_mul hnonneg,ENNReal.ofReal_toReal (retention_ne_top e v)]
  exact retainedJump_rate_identity e v _ hp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # No retention loss for the small velocities used by the minorization paths -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem referenceJump_measure (e v : V) : referenceJump e v =
    ENNReal.ofReal (plusProbability e v) • outgoing (v,e)+
      ENNReal.ofReal (1-plusProbability e v) • outgoing (v,-e) := by
  have hp : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (plusProbability e v))) :=
    ((plusProbability_measurable e).comp measurable_fst).ennreal_ofReal
  have hm : Measurable (Function.uncurry (fun v (_ : V) => ENNReal.ofReal (1-plusProbability e v))) :=
    (measurable_const.sub ((plusProbability_measurable e).comp measurable_fst)).ennreal_ofReal
  simp only [referenceJump,add_apply,Kernel.withDensity_apply _ hp,Kernel.withDensity_apply _ hm,
    withDensity_const]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_NormalGainMeasureActions
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual normal-angle gain kernel for measurable cold partner measures -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem normalChild_measurable (left : Bool) : Measurable (normalChild (X := X) left) := by
  cases left <;> unfold normalChild scatterLeft scatterRight normalComponent <;> dsimp <;> fun_prop

theorem normalRate_measurable : Measurable (normalRate (X := X)) := by
  unfold normalRate collisionKernel normalComponent
  fun_prop

instance normalChildKernel_sFinite (K : Kernel X Velocity) [IsSFiniteKernel K] (left : Bool) :
    IsSFiniteKernel (normalChildKernel K left) := by
  have : IsSFiniteKernel (Kernel.withDensity (Kernel.id ×ₖ normalParameters K)
      (fun _ z => normalRate z)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  unfold normalChildKernel
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply normalChild_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem normalChildKernel_lintegral (K : Kernel X Velocity) [IsSFiniteKernel K]
    (left : Bool) (z : X × Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ v, f v ∂normalChildKernel K left z) =
      ∫⁻ w, ∫⁻ ω, ENNReal.ofReal (collisionKernel w z.2 ω)*
        f (normalChild left (z,w,ω)) ∂sphereArea ∂K z.1 := by
  have hd : Measurable (Function.uncurry (fun (_ : X × Velocity)
      (q : (X × Velocity) × (Velocity × Sphere)) => normalRate q)) :=
    normalRate_measurable.comp measurable_snd
  have hc : Measurable (fun q => f (normalChild (X := X) left q)) :=
    hf.comp (normalChild_measurable (X := X) left)
  have hi : Measurable (fun q : (X × Velocity) × (Velocity × Sphere) => normalRate q*f (normalChild left q)) :=
    normalRate_measurable.mul hc
  rw [normalChildKernel,Kernel.lintegral_map _ (normalChild_measurable left) z hf,
    Kernel.lintegral_withDensity _ hd z hc,Kernel.lintegral_id_prod hi]
  have hip : Measurable (fun q : Velocity × Sphere =>
      ENNReal.ofReal (collisionKernel q.1 z.2 q.2)*f (normalChild left (z,q))) := by
    simpa only [normalRate,Function.comp_def,id_eq] using
      hi.comp (measurable_const.prodMk measurable_id)
  rw [normalParameters,Kernel.prod_apply,Kernel.comap_apply,Kernel.const_apply]
  exact lintegral_prod _ hip.aemeasurable

instance normalGainKernel_sFinite (K : Kernel X Velocity) [IsSFiniteKernel K] :
    IsSFiniteKernel (normalGainKernel K) := by unfold normalGainKernel; infer_instance

theorem normalGainKernel_lintegral (K : Kernel X Velocity) [IsSFiniteKernel K]
    (z : X × Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ v, f v ∂normalGainKernel K z) =
      (∫⁻ w, ∫⁻ ω, ENNReal.ofReal (collisionKernel w z.2 ω)*f (scatterLeft w z.2 ω)
        ∂sphereArea ∂K z.1)+
      (∫⁻ w, ∫⁻ ω, ENNReal.ofReal (collisionKernel w z.2 ω)*f (scatterRight w z.2 ω)
        ∂sphereArea ∂K z.1) := by
  rw [normalGainKernel,add_apply,lintegral_add_measure,
    normalChildKernel_lintegral K true z hf,normalChildKernel_lintegral K false z hf]
  rfl

end BoltzmannNonuniqueness

end

end

section

/-! # The physical gain kernel, retaining the collision's spacetime location -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem normalPhaseGainKernel_lintegral (K : Kernel X Velocity) [IsSFiniteKernel K]
    (z : X × Velocity) {f : X × Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂normalPhaseGainKernel K z) =
      (∫⁻ w, ∫⁻ ω, ENNReal.ofReal (collisionKernel w z.2 ω)*f (z.1,scatterLeft w z.2 ω)
        ∂sphereArea ∂K z.1)+
      (∫⁻ w, ∫⁻ ω, ENNReal.ofReal (collisionKernel w z.2 ω)*f (z.1,scatterRight w z.2 ω)
        ∂sphereArea ∂K z.1) := by
  have hp : Measurable (fun p : (X × Velocity) × Velocity => (p.1.1,p.2)) := by fun_prop
  have hc : Measurable (fun p : (X × Velocity) × Velocity => f (p.1.1,p.2)) := hf.comp hp
  rw [normalPhaseGainKernel,Kernel.lintegral_map _ hp z hf,
    Kernel.lintegral_id_prod hc]
  simpa only [Function.comp_def] using normalGainKernel_lintegral K z
    (hf.comp (show Measurable (fun v : Velocity => (z.1,v)) from
      measurable_const.prodMk measurable_id))

end BoltzmannNonuniqueness

end

end

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

section

/-! # The normal-angle gain is linear in an arbitrary incoming partner measure -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem normalPhaseGainKernel_lintegral_gain
    (K : Kernel X Velocity) [IsSFiniteKernel K] (z : X × Velocity)
    {f : X × Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂normalPhaseGainKernel K z) =
      ∫⁻ v, f (z.1,v) ∂normalGainKernel K z := by
  rw [normalPhaseGainKernel_lintegral K z hf,
    normalGainKernel_lintegral K z (f := fun v => f (z.1,v)) (hf.comp (measurable_const.prodMk measurable_id))]

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

section

/-! # Testing the positive gain-and-retention kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem positiveSourceKernel_lintegral (K : Kernel X X) [IsSFiniteKernel K]
    {b r : X → ℝ} (hb : Measurable b) (hr : Measurable r) (x : X)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂positiveSourceKernel K b r x) =
      (∫⁻ y, ENNReal.ofReal (b y)*f y ∂K x)+ENNReal.ofReal (b x*r x)*f x := by
  rw [positiveSourceKernel,add_apply,lintegral_add_measure,
    Kernel.lintegral_withDensity (f := fun (_ : X) y => ENNReal.ofReal (b y)) K
      (hb.ennreal_ofReal.comp measurable_snd) x hf,
    Kernel.lintegral_withDensity (f := fun (_ : X) y => ENNReal.ofReal (b y*r y)) Kernel.id
      ((hb.mul hr).ennreal_ofReal.comp measurable_snd) x hf,
    Kernel.id_apply,lintegral_dirac' x (f := fun y => ENNReal.ofReal (b y*r y)*f y)
      ((hb.mul hr).ennreal_ofReal.mul hf)]

theorem positiveSourceKernel_one_lintegral (K : Kernel X X) [IsSFiniteKernel K]
    {r : X → ℝ} (hr : Measurable r) (x : X) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂positiveSourceKernel K (fun _ => 1) r x) =
      (∫⁻ y, f y ∂K x)+ENNReal.ofReal (r x)*f x := by
  rw [positiveSourceKernel_lintegral K measurable_const hr x hf]
  simp only [ENNReal.ofReal_one,one_mul]

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AeKernelHistoryOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Almost-everywhere kernel comparison suffices below an occupation measure -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.KernelHistoryOrder

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem measure_comp_mono_ae {K L : Kernel X Y} {μ ν : Measure X}
    (hK : ∀ᵐ x ∂μ, K x ≤ L x) (hμ : μ ≤ ν) : K ∘ₘ μ ≤ L ∘ₘ ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA K.aemeasurable,Measure.bind_apply hA L.aemeasurable]
  apply (lintegral_mono_ae ?_).trans (lintegral_mono' hμ le_rfl)
  filter_upwards [hK] with x hx
  exact hx A

end BoltzmannNonuniqueness.KernelHistoryOrder

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceMinorization
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The retained reference law as a Markov kernel on its bounded state space -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem stateKernel_apply (v : RetainedState) :
    stateKernel v = (retainedJump beamAxis v.1).comap (Subtype.val : RetainedState → V) := rfl

theorem stateKernel_map (v : RetainedState) :
    (stateKernel v).map (Subtype.val : RetainedState → V) = retainedJump beamAxis v.1 := by
  rw [stateKernel_apply,map_comap_subtype_coe referenceRegion_measurable]
  have hn := retention_ne_zero_coarse beamAxis v.1 axis_norms.2.2 (retainedState_norm v)
  have : IsProbabilityMeasure (retainedJump beamAxis v.1) :=
    ⟨retainedJump_univ _ _ hn⟩
  exact Measure.restrict_eq_self_of_ae_mem
    ((mem_ae_iff_prob_eq_one referenceRegion_measurable).mpr (retainedJump_region _ _ hn))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The positive collision kernel after adding a constant attenuation clock -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem stateFrequency_measurable : Measurable stateFrequency := by
  unfold stateFrequency frequency
  fun_prop

theorem branchingKernel_apply (v : RetainedState) : branchingKernel v =
    ENNReal.ofReal (stateRate v) • stateKernel v +
      ENNReal.ofReal (48*Real.pi-stateFrequency v) • Measure.dirac v := by
  have hr : Measurable (Function.uncurry (fun v (_ : RetainedState) => ENNReal.ofReal (stateRate v))) :=
    (stateRate_measurable.comp measurable_fst).ennreal_ofReal
  have hs : Measurable (Function.uncurry (fun v (_ : RetainedState) =>
      ENNReal.ofReal (48*Real.pi-stateFrequency v))) :=
    (measurable_const.sub (stateFrequency_measurable.comp measurable_fst)).ennreal_ofReal
  rw [branchingKernel,add_apply,Kernel.withDensity_apply _ hr,Kernel.withDensity_apply _ hs,
    withDensity_const,withDensity_const,Kernel.id_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_KernelInvariantOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite history comparison only needs kernel order on the reachable region -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem kernel_pow_le_on_invariant (K L : Kernel X X) (A : Set X)
    (hinv : ∀ x ∈ A, ∀ᵐ y ∂K x, y ∈ A) (hle : ∀ x ∈ A, K x ≤ L x)
    (n : ℕ) : ∀ x ∈ A, (K^n) x ≤ (L^n) x := by
  induction n with
  | zero => intro x hx; exact le_rfl
  | succ n ih =>
    intro x hx
    rw [show K^(n+1) = (K^n) ∘ₖ K by simpa only [pow_one] using Kernel.pow_add K n 1,
      show L^(n+1) = (L^n) ∘ₖ L by simpa only [pow_one] using Kernel.pow_add L n 1]
    have h : ∀ᵐ y ∂K x, (K^n) y ≤ (L^n) y := by
      filter_upwards [hinv x hx] with y hy
      exact ih y hy
    exact KernelHistoryOrder.measure_comp_mono_ae h (hle x hx)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceFlightLaws
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Lebesgue waiting-time choices for finite collision histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem waitingDensity_measurable : Measurable (Function.uncurry waitingDensity) := by
  let D : Set (TimeFlightState × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ q.1.1}
  have hD : MeasurableSet D := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst.fst)
  exact (measurable_const.indicator hD : Measurable (D.indicator (fun _ => (1 : ℝ≥0∞))))

theorem waitingTime_apply (p : TimeFlightState) : waitingTime p = volume.restrict (Ioc 0 p.1) := by
  rw [waitingTime,Kernel.withDensity_apply _ waitingDensity_measurable,Kernel.const_apply]
  exact withDensity_indicator_one measurableSet_Ioc

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceBranchingHistories
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Damped finite collision histories for the positive reference gain -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem eventDensity_measurable (rate : ℝ≥0) : Measurable (Function.uncurry (eventDensity rate)) := by
  unfold eventDensity clockSurvival
  fun_prop

theorem rawEventStep_lintegral (K : Kernel RetainedState RetainedState) [IsSFiniteKernel K]
    (p : TimeFlightState) {F : TimeFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂rawEventStep K p) =
      ∫⁻ s in Ioc 0 p.1, ∫⁻ u, F (advanceState p s u) ∂K p.2.2 := by
  have ha (q : TimeFlightState × ℝ) : (∫⁻ p, F p ∂eventAfterWait K q) =
      ∫⁻ u, F (advanceState q.1 q.2 u) ∂K q.1.2.2 := by
    rw [eventAfterWait,Kernel.lintegral_map _ advanceState_measurable q hF]
    simpa only [Function.comp_def,Kernel.comap_apply] using!
      Kernel.lintegral_id_prod (hF.comp advanceState_measurable)
        (K.comap (fun q : TimeFlightState × ℝ => q.1.2.2) (by fun_prop)) q
  rw [rawEventStep,Kernel.lintegral_comp _ _ _ hF,
    Kernel.lintegral_id_prod (hF.lintegral_kernel (κ := eventAfterWait K))]
  simp_rw [ha]
  rw [waitingTime_apply]

theorem eventStep_lintegral (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] (p : TimeFlightState) {F : TimeFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂eventStep rate K p) =
      ∫⁻ s in Ioc 0 p.1, clockSurvival rate s * ∫⁻ u, F (advanceState p s u) ∂K p.2.2 := by
  rw [eventStep,Kernel.lintegral_withDensity _ (eventDensity_measurable rate) _ hF,
    rawEventStep_lintegral K p]
  · apply lintegral_congr
    intro s
    have he (u : RetainedState) : eventDensity rate p (advanceState p s u) =
        clockSurvival rate s := by simp only [eventDensity,advanceState,sub_sub_cancel]
    simp_rw [he]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · exact ((eventDensity_measurable rate).comp (measurable_const.prodMk measurable_id)).mul hF

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Factorial bounds and time support of positive collision histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem clockSurvival_le_one (rate : ℝ≥0) {s : ℝ} (hs : 0 ≤ s) :
    clockSurvival rate s ≤ 1 := by
  simpa only [clockSurvival,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr rate.coe_nonneg) hs))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive finite-history exhaustion for a bounded reference subsolution -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem eventHistory_measurable (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D) (n : ℕ) :
    Measurable (eventHistory rate K D n) := hD.lintegral_kernel

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exponentially growing reference flight is dominated by actual positive histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightSeed_measurable (rate : ℝ≥0) {f : FlightState → ℝ≥0∞}
    (hf : Measurable f) : Measurable (flightSeed rate f) := by
  apply Measurable.mul
  · unfold clockSurvival
    fun_prop
  · exact hf.comp finishFlight_measurable

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Unnormalized beam intensities behind the positive reference histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem referenceJump_intensity (e v : V) (he : ‖e‖ = 1) :
    ENNReal.ofReal (2*frequency v e) • referenceJump e v =
      ENNReal.ofReal (4*Real.pi*‖v-e‖) • outgoing (v,e) +
      ENNReal.ofReal (4*Real.pi*‖v+e‖) • outgoing (v,-e) := by
  have hd : ‖v-e‖+‖v+e‖ ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (two_beam_distance_lower v e he))
  rw [referenceJump_measure,smul_add,smul_smul,smul_smul,
    ← ENNReal.ofReal_mul (by unfold frequency; positivity),
    ← ENNReal.ofReal_mul (by unfold frequency; positivity),minusProbability_eq e v he]
  have hp : 2*frequency v e*plusProbability e v = 4*Real.pi*‖v-e‖ := by
    unfold frequency plusProbability
    field_simp
    ring
  have hm : 2*frequency v e*(‖v+e‖/(‖v-e‖+‖v+e‖)) = 4*Real.pi*‖v+e‖ := by
    unfold frequency
    field_simp
    ring
  rw [hp,hm]

theorem branchingKernel_projection (v : RetainedState) :
    (branchingKernel v).map (Subtype.val : RetainedState → V) =
      ENNReal.ofReal (2*frequency v.1 beamAxis) •
        (referenceJump beamAxis v.1).restrict referenceRegion +
      ENNReal.ofReal (48*Real.pi-stateFrequency v) • Measure.dirac v.1 := by
  rw [branchingKernel_apply,Measure.map_add _ _ measurable_subtype_coe,
    Measure.map_smul,Measure.map_smul,
    stateKernel_map,Measure.map_dirac' measurable_subtype_coe]
  · congr 1
    exact retainedRate_measure_identity beamAxis v.1
      (retention_ne_zero_coarse beamAxis v.1 axis_norms.2.2 (retainedState_norm v))
  all_goals exact measurable_subtype_coe.aemeasurable

theorem branchingKernel_beam_projection (v : RetainedState) :
    (branchingKernel v).map (Subtype.val : RetainedState → V) =
      (ENNReal.ofReal (4*Real.pi*‖v.1-beamAxis‖) • outgoing (v.1,beamAxis) +
        ENNReal.ofReal (4*Real.pi*‖v.1+beamAxis‖) • outgoing (v.1,-beamAxis)).restrict referenceRegion +
      ENNReal.ofReal (48*Real.pi-stateFrequency v) • Measure.dirac v.1 := by
  rw [branchingKernel_projection]
  congr 1
  rw [← Measure.restrict_smul,referenceJump_intensity beamAxis v.1 axis_norms.2.2]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Pointwise collision-rate stability for merely measurable partner fields -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem relative_speed_lipschitz (v w u z : V) :
    |‖v-w‖-‖u-z‖| ≤ ‖v-u‖+‖w-z‖ := by
  apply (abs_norm_sub_norm_le (v-w) (u-z)).trans
  calc
    ‖(v-w)-(u-z)‖ = ‖(v-u)-(w-z)‖ := by congr 1; abel
    _ ≤ _ := norm_sub_le _ _

theorem weighted_speed_error {v w u z : V} {b ε δ R : ℝ}
    (hb : 0 ≤ b) (hb2 : b ≤ 2) (hberr : |b-1| ≤ ε)
    (herr : ‖v-u‖+‖w-z‖ ≤ δ) (hR : ‖u-z‖ ≤ R) :
    |b*‖v-w‖-‖u-z‖| ≤ 2*δ+ε*R := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hberr
  have hδ : 0 ≤ δ := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans herr
  calc
    |b*‖v-w‖-‖u-z‖| = |b*(‖v-w‖-‖u-z‖)+(b-1)*‖u-z‖| := by congr 1; ring
    _ ≤ |b| * |‖v-w‖-‖u-z‖|+|b-1| * ‖u-z‖ := by
      simpa only [abs_mul,abs_norm] using abs_add_le (b*(‖v-w‖-‖u-z‖)) ((b-1)*‖u-z‖)
    _ ≤ 2*δ+ε*R := by
      apply add_le_add
      · rw [abs_of_nonneg hb]
        exact mul_le_mul hb2 ((relative_speed_lipschitz v w u z).trans herr)
          (abs_nonneg _) (by norm_num)
      · exact mul_le_mul hberr hR (norm_nonneg _) hε

theorem beam_gain_rate_error {v w u z : V} {b ε δ R : ℝ}
    (hb : 0 ≤ b) (hb2 : b ≤ 2) (hberr : |b-1| ≤ ε)
    (herr : ‖v-u‖+‖w-z‖ ≤ δ) (hR : ‖u-z‖ ≤ R) :
    |4*Real.pi*b*‖v-w‖-4*Real.pi*‖u-z‖| ≤ 4*Real.pi*(2*δ+ε*R) := by
  rw [show 4*Real.pi*b*‖v-w‖-4*Real.pi*‖u-z‖ =
    (4*Real.pi)*(b*‖v-w‖-‖u-z‖) by ring,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 4*Real.pi)]
  exact mul_le_mul_of_nonneg_left (weighted_speed_error hb hb2 hberr herr hR) (by positivity)

theorem medium_frequency_error {v u w_plus w_minus e : V} {b_plus b_minus ε δ R : ℝ}
    (hb_plus : 0 ≤ b_plus) (hb_minus : 0 ≤ b_minus) (hb_plus2 : b_plus ≤ 2) (hb_minus2 : b_minus ≤ 2)
    (he_plus : |b_plus-1| ≤ ε) (he_minus : |b_minus-1| ≤ ε)
    (hv_plus : ‖v-u‖+‖w_plus-e‖ ≤ δ) (hv_minus : ‖v-u‖+‖w_minus-(-e)‖ ≤ δ)
    (hR_plus : ‖u-e‖ ≤ R) (hR_minus : ‖u-(-e)‖ ≤ R) :
    |mediumFrequency v w_plus w_minus b_plus b_minus-frequency u e| ≤ 4*Real.pi*(2*δ+ε*R) := by
  have h_plus := weighted_speed_error hb_plus hb_plus2 he_plus hv_plus hR_plus
  have h_minus := weighted_speed_error hb_minus hb_minus2 he_minus hv_minus hR_minus
  have hn : u-(-e) = u+e := sub_neg_eq_add _ _
  rw [hn] at h_minus
  have heq : mediumFrequency v w_plus w_minus b_plus b_minus-frequency u e =
      (2*Real.pi)*((b_plus*‖v-w_plus‖-‖u-e‖)+(b_minus*‖v-w_minus‖-‖u+e‖)) := by
    unfold mediumFrequency frequency
    ring
  rw [heq,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
  have hsum := (abs_add_le (b_plus*‖v-w_plus‖-‖u-e‖) (b_minus*‖v-w_minus‖-‖u+e‖)).trans (add_le_add h_plus h_minus)
  calc
    _ ≤ (2*Real.pi)*((2*δ+ε*R)+(2*δ+ε*R)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Coupled positive histories with two beam marks and self-retention marks -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem marked_child_error (m : HistoryMark) {v u wp wm zp zm n : V} {δ ε : ℝ}
    (hn : ‖n‖ = 1) (hv : ‖v-u‖ ≤ δ) (hp : ‖wp-zp‖ ≤ ε) (hm : ‖wm-zm‖ ≤ ε) :
    ‖markedChild m v wp wm n-markedChild m u zp zm n‖ ≤ δ+ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hp
  unfold markedChild
  split
  · exact hv.trans (le_add_of_nonneg_right hε)
  · split
    · exact (child_lipschitz v wp u zp n hn).trans (add_le_add hv hp)
    · exact (child_lipschitz v wm u zm n hn).trans (add_le_add hv hm)

theorem marked_rate_error (m : HistoryMark) {v u wp wm e : V} {bp bm ε δ R : ℝ}
    (hp : 0 ≤ bp) (hm : 0 ≤ bm) (hp2 : bp ≤ 2) (hm2 : bm ≤ 2)
    (hep : |bp-1| ≤ ε) (hem : |bm-1| ≤ ε)
    (hvp : ‖v-u‖+‖wp-e‖ ≤ δ) (hvm : ‖v-u‖+‖wm-(-e)‖ ≤ δ)
    (hRp : ‖u-e‖ ≤ R) (hRm : ‖u-(-e)‖ ≤ R) :
    |markedRate m v wp wm bp bm-markedRate m u e (-e) 1 1| ≤
      4*Real.pi*(2*δ+ε*R) := by
  unfold markedRate
  split
  · have hf := medium_frequency_error hp hm hp2 hm2 hep hem hvp hvm hRp hRm
    have heq : mediumFrequency u e (-e) 1 1 = frequency u e := by
      simp only [mediumFrequency,frequency,one_mul,sub_neg_eq_add]
    rw [heq,show 48*Real.pi-mediumFrequency v wp wm bp bm-(48*Real.pi-frequency u e) =
      -(mediumFrequency v wp wm bp bm-frequency u e) by ring,abs_neg]
    exact hf
  · split
    · simpa only [mul_one] using beam_gain_rate_error hp hp2 hep hvp hRp
    · simpa only [mul_one] using beam_gain_rate_error hm hm2 hem hvm hRm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceHistoryMoments
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurable extension of retained-state observables to the physical velocity space -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem stateProjection_measurable : Measurable stateProjection :=
  (Classical.choose_spec state_projection_exists).1

theorem stateProjection_apply (v : RetainedState) : stateProjection v.1 = v :=
  (Classical.choose_spec state_projection_exists).2 v

theorem stateProjection_coe {v : V} (hv : v ∈ referenceRegion) :
    (stateProjection v : V) = v := by
  have h := congrArg (Subtype.val : RetainedState → V) (stateProjection_apply ⟨v,hv⟩)
  exact h

theorem branchingKernel_lintegral_physical (v : RetainedState)
    {F : RetainedState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ u, F u ∂branchingKernel v) =
      ENNReal.ofReal (4*Real.pi*‖v.1-beamAxis‖)*
        (∫⁻ n, referenceRegion.indicator (fun w => F (stateProjection w))
          (child v.1 beamAxis n.1) ∂sphereProbability) +
      ENNReal.ofReal (4*Real.pi*‖v.1+beamAxis‖)*
        (∫⁻ n, referenceRegion.indicator (fun w => F (stateProjection w))
          (child v.1 (-beamAxis) n.1) ∂sphereProbability) +
      ENNReal.ofReal (48*Real.pi-stateFrequency v)*F v := by
  let G : V → ℝ≥0∞ := fun w => F (stateProjection w)
  have hG : Measurable G := hF.comp stateProjection_measurable
  have he : (∫⁻ w, G w ∂(branchingKernel v).map (Subtype.val : RetainedState → V)) =
      ∫⁻ u, F u ∂branchingKernel v := by
    rw [lintegral_map hG measurable_subtype_coe]
    apply lintegral_congr
    intro u
    exact congrArg F (stateProjection_apply u)
  rw [← he,branchingKernel_beam_projection,lintegral_add_measure,
    ← lintegral_indicator referenceRegion_measurable,
    lintegral_add_measure,lintegral_smul_measure,lintegral_smul_measure,lintegral_smul_measure,
    lintegral_dirac]
  rw [outgoing_apply,outgoing_apply,
    lintegral_map (hG.indicator referenceRegion_measurable) (by unfold child; fun_prop),
    lintegral_map (hG.indicator referenceRegion_measurable) (by unfold child; fun_prop)]
  simp only [smul_eq_mul,G,stateProjection_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A common positive bound for the nearby physical beam-history weights -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem medium_frequency_bounds {v wp wm : V} {bp bm : ℝ}
    (hv : ‖v‖ ≤ 6) (hwp : ‖wp‖ ≤ 2) (hwm : ‖wm‖ ≤ 2)
    (hbp : 0 ≤ bp) (hbm : 0 ≤ bm) (hbp1 : bp ≤ 5/4) (hbm1 : bm ≤ 5/4) :
    0 ≤ mediumFrequency v wp wm bp bm ∧ mediumFrequency v wp wm bp bm ≤ 40*Real.pi := by
  have hp : ‖v-wp‖ ≤ 8 := (norm_sub_le v wp).trans (by linarith)
  have hm : ‖v-wm‖ ≤ 8 := (norm_sub_le v wm).trans (by linarith)
  have hp' : bp*‖v-wp‖ ≤ 10 := by
    calc
      _ ≤ (5/4:ℝ)*8 := mul_le_mul hbp1 hp (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hm' : bm*‖v-wm‖ ≤ 10 := by
    calc
      _ ≤ (5/4:ℝ)*8 := mul_le_mul hbm1 hm (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  constructor
  · unfold mediumFrequency
    positivity
  · unfold mediumFrequency
    have h := mul_le_mul_of_nonneg_left (add_le_add hp' hm') (by positivity : 0 ≤ 2*Real.pi)
    nlinarith

theorem marked_rate_bounds (m : HistoryMark) {v wp wm : V} {bp bm : ℝ}
    (hv : ‖v‖ ≤ 6) (hwp : ‖wp‖ ≤ 2) (hwm : ‖wm‖ ≤ 2)
    (hbp : 0 ≤ bp) (hbm : 0 ≤ bm) (hbp1 : bp ≤ 5/4) (hbm1 : bm ≤ 5/4) :
    0 ≤ markedRate m v wp wm bp bm ∧ markedRate m v wp wm bp bm ≤ 48*Real.pi := by
  have hf := medium_frequency_bounds hv hwp hwm hbp hbm hbp1 hbm1
  unfold markedRate
  split
  · constructor <;> linarith [Real.pi_pos]
  · split
    · have hn := norm_sub_le v wp
      have hp : bp*‖v-wp‖ ≤ 10 := by
        have h := mul_le_mul hbp1 (show ‖v-wp‖ ≤ 8 by linarith) (norm_nonneg (v-wp)) (by norm_num)
        norm_num at h
        exact h
      constructor
      · positivity
      · have h := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*Real.pi)
        nlinarith [Real.pi_pos]
    · have hn := norm_sub_le v wm
      have hp : bm*‖v-wm‖ ≤ 10 := by
        have h := mul_le_mul hbm1 (show ‖v-wm‖ ≤ 8 by linarith) (norm_nonneg (v-wm)) (by norm_num)
        norm_num at h
        exact h
      constructor
      · positivity
      · have h := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*Real.pi)
        nlinarith [Real.pi_pos]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Explicit mark-and-angle formula for one positive reference event -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem reference_frequency_eq (v : V) :
    mediumFrequency v beamAxis (-beamAxis) 1 1 = frequency v beamAxis := by
  simp only [mediumFrequency,frequency,one_mul,sub_neg_eq_add]

theorem markedReference_integral (v : RetainedState) {F : RetainedState → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ u, F u ∂branchingKernel v) =
      ∑ m : HistoryMark, ∫⁻ n, markedReferenceWeight v m n*F (markedReferenceState v m n)
        ∂sphereProbability := by
  have hmul (w : V) : referenceRegion.indicator 1 w * F (stateProjection w) =
      referenceRegion.indicator (fun u => F (stateProjection u)) w := by
    by_cases hw : w ∈ referenceRegion <;> simp [hw]
  have hzero : (∫⁻ n, markedReferenceWeight v 0 n * F (markedReferenceState v 0 n)
      ∂sphereProbability) = ENNReal.ofReal (48*Real.pi-stateFrequency v)*F v := by
    have he (n : Sphere) : markedReferenceWeight v 0 n * F (markedReferenceState v 0 n) =
        ENNReal.ofReal (48*Real.pi-stateFrequency v)*F v := by
      simp [markedReferenceWeight,markedReferenceState,markedChild,markedRate,
        reference_frequency_eq,stateFrequency,v.2,stateProjection_apply]
    simp_rw [he]
    rw [lintegral_const,measure_univ,mul_one]
  have hone : (∫⁻ n, markedReferenceWeight v 1 n * F (markedReferenceState v 1 n)
      ∂sphereProbability) = ENNReal.ofReal (4*Real.pi*‖v.1-beamAxis‖) *
        ∫⁻ n, referenceRegion.indicator (fun u => F (stateProjection u))
          (child v.1 beamAxis n.1) ∂sphereProbability := by
    simp only [markedReferenceWeight,markedReferenceState,markedChild,markedRate,
      Fin.isValue,one_ne_zero,↓reduceIte,mul_one,mul_assoc,hmul]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have htwo : (∫⁻ n, markedReferenceWeight v 2 n * F (markedReferenceState v 2 n)
      ∂sphereProbability) = ENNReal.ofReal (4*Real.pi*‖v.1+beamAxis‖) *
        ∫⁻ n, referenceRegion.indicator (fun u => F (stateProjection u))
          (child v.1 (-beamAxis) n.1) ∂sphereProbability := by
    simp only [markedReferenceWeight,markedReferenceState,markedChild,markedRate,
      Fin.isValue,show (2 : HistoryMark) ≠ 0 by decide,show (2 : HistoryMark) ≠ 1 by decide,
      ↓reduceIte,mul_one,sub_neg_eq_add,mul_assoc,hmul]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [Fin.sum_univ_three,hzero,hone,htwo,branchingKernel_lintegral_physical v hF]
  ac_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Mark-and-angle expansion of every finite positive reference history -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem markedChild_measurable (m : HistoryMark) :
    Measurable (fun p : RetainedState × Sphere =>
      markedChild m p.1.1 beamAxis (-beamAxis) p.2.1) := by
  unfold markedChild
  split
  · fun_prop
  · split <;> unfold child <;> fun_prop

theorem markedRate_measurable (m : HistoryMark) :
    Measurable (fun v : RetainedState => markedRate m v.1 beamAxis (-beamAxis) 1 1) := by
  unfold markedRate
  split
  · unfold mediumFrequency
    fun_prop
  · split <;> fun_prop

theorem markedReferenceWeight_measurable (m : HistoryMark) :
    Measurable (fun p : RetainedState × Sphere => markedReferenceWeight p.1 m p.2) := by
  unfold markedReferenceWeight
  exact ((markedRate_measurable m).comp measurable_fst).ennreal_ofReal.mul
    ((measurable_const.indicator referenceRegion_measurable).comp (markedChild_measurable m))

theorem markedReferenceState_measurable (m : HistoryMark) :
    Measurable (fun p : RetainedState × Sphere => markedReferenceState p.1 m p.2) :=
  stateProjection_measurable.comp (markedChild_measurable m)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite time-and-angle parameter measures for the selected positive histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem eventParameterMeasure_mass (T : ℝ) :
    eventParameterMeasure T univ = ENNReal.ofReal T := by
  rw [eventParameterMeasure,Measure.prod_apply MeasurableSet.univ]
  simp only [Set.preimage_univ,measure_univ,lintegral_const,one_mul,
    Measure.restrict_apply_univ,Real.volume_Ioc,sub_zero]

theorem referenceParameterState_measurable (m : HistoryMark) :
    Measurable (fun q : TimeFlightState × EventParameter => referenceParameterState q.1 m q.2) := by
  unfold referenceParameterState advanceState
  have hi : Measurable (fun q : TimeFlightState × EventParameter => (q.1.2.2,q.2.2)) := by
    fun_prop
  have hu : Measurable (fun q : TimeFlightState × EventParameter =>
      markedReferenceState q.1.2.2 m q.2.2) := by
    simpa only [Function.comp_def] using (markedReferenceState_measurable m).comp hi
  have ht : Measurable (fun q : TimeFlightState × EventParameter => q.1.1-q.2.1) := by
    fun_prop
  have hx : Measurable (fun q : TimeFlightState × EventParameter => (freeFlight q.2.1 q.1.2).1) := by
    unfold freeFlight
    fun_prop
  exact ht.prodMk (hx.prodMk hu)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A fixed finite parameter measure including the three event marks -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem markedParameterState_measurable :
    Measurable (fun q : TimeFlightState × MarkedEventParameter => markedParameterState q.1 q.2) := by
  have hm : Measurable (fun q : HistoryMark × (TimeFlightState × EventParameter) =>
      referenceParameterState q.2.1 q.1 q.2.2) :=
    measurable_from_prod_countable_right (fun m => referenceParameterState_measurable m)
  exact hm.comp (measurable_snd.fst.prodMk (measurable_fst.prodMk measurable_snd.snd))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Fixed finite products of time, mark and angle parameters -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

attribute [instance] parameterWordMeasurable

theorem parameterWordState_measurable (n : ℕ) :
    Measurable (fun q : TimeFlightState × ParameterWord n => parameterWordState n q.1 q.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    have hh : Measurable (fun q : TimeFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by fun_prop
    have ht : Measurable (fun q : TimeFlightState × ParameterWord (n+1) => q.2.2) := by fun_prop
    have hs : Measurable (fun q : TimeFlightState × ParameterWord (n+1) =>
        (markedParameterState q.1 q.2.1,q.2.2)) :=
      (markedParameterState_measurable.comp hh).prodMk ht
    exact ih.comp hs

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact finite-history integrals over a fixed product parameter space -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem markedParameterState_time (p : TimeFlightState) (a : MarkedEventParameter)
    (ha : a.2.1 ∈ Ioc 0 p.1) : (markedParameterState p a).1 ∈ Icc 0 p.1 :=
  ⟨sub_nonneg.mpr ha.2,sub_le_self _ ha.1.le⟩

theorem eventHistory_zero (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] (D : TimeFlightState → ℝ≥0∞) (p : TimeFlightState) :
    eventHistory rate K D 0 p = D p := by
  have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
  rw [eventHistory,pow_zero,hi,Kernel.id_apply,lintegral_dirac]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact volume of the fixed finite history parameter domains -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem markedEventMeasure_mass (T : ℝ) : markedEventMeasure T univ = 3*ENNReal.ofReal T := by
  rw [markedEventMeasure,Measure.prod_apply MeasurableSet.univ]
  simp only [preimage_univ,eventParameterMeasure_mass,lintegral_const]
  rw [Measure.count_univ]
  norm_num [mul_comm]

theorem parameterWordMeasure_mass (T : ℝ) (n : ℕ) :
    parameterWordMeasure T n univ = (3*ENNReal.ofReal T)^n := by
  induction n with
  | zero =>
    change (Measure.dirac PUnit.unit) univ = _
    rw [Measure.dirac_apply_of_mem (mem_univ _),pow_zero]
  | succ n ih =>
    rw [parameterWordMeasure,Measure.prod_apply MeasurableSet.univ]
    simp only [preimage_univ,ih,lintegral_const]
    rw [markedEventMeasure_mass,pow_succ]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceGrowthBlocks
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Displacement geometry for the three intervals of a branching block -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem blockTarget_measurable (x : V) (A κ d : ℝ) : MeasurableSet (blockTarget x A κ d) := by
  unfold blockTarget
  measurability

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The reference collision kernel at a larger constant damping -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem branchingAt_apply (C : ℝ≥0) (v : RetainedState) :
    branchingAt C v = branchingKernel v +
      ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) • Measure.dirac v := by
  rw [branchingAt,add_apply,Kernel.withDensity_apply _ (by fun_prop),withDensity_const,Kernel.id_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Strict endpoint margins survive finite-path perturbations -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem block_target_perturb {x : V} {A κ d : ℝ} {r : FlightState} {w : V × V}
    (hr : r ∈ blockTarget x A κ d)
    (hx : ‖w.1-r.1‖ ≤ d*κ*A/4) (hv : ‖w.2-(r.2 : V)‖ ≤ 1) :
    w ∈ physicalBlockTarget x A κ d := by
  constructor
  · have hh := norm_sub_le_norm_sub_add_norm_sub w.1 r.1 (x+(κ*A) • firstAxis)
    have hgood := hr.1
    linarith
  · have hh := norm_add_le (w.2-(r.2 : V)) (r.2 : V)
    rw [sub_add_cancel] at hh
    have hgood := hr.2
    linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PerturbedFiniteBlock
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive marked histories in a measurable two-beam medium -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumPoint_measurable (endTime : ℝ) :
    Measurable (fun q : PhysicalFlightState × ℝ => mediumPoint endTime q.1 q.2) := by
  unfold mediumPoint
  fun_prop

theorem mediumParameterState_measurable (b : BeamCoefficients) (endTime : ℝ) :
    Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      mediumParameterState b endTime q.1 q.2) := by
  have hfixed (m : HistoryMark) : Measurable (fun q : PhysicalFlightState × EventParameter =>
      mediumParameterState b endTime q.1 (m,q.2)) := by
    have hx : Measurable (fun q : PhysicalFlightState × EventParameter =>
        mediumPoint endTime q.1 q.2.1) :=
      (mediumPoint_measurable endTime).comp
        (show Measurable (fun q : PhysicalFlightState × EventParameter => (q.1,q.2.1)) by fun_prop)
    have hplus : Measurable (fun q : PhysicalFlightState × EventParameter =>
        b.plusPartner (mediumPoint endTime q.1 q.2.1)) := by
      simpa only [Function.comp_def] using b.plusPartner_measurable.comp hx
    have hminus : Measurable (fun q : PhysicalFlightState × EventParameter =>
        b.minusPartner (mediumPoint endTime q.1 q.2.1)) := by
      simpa only [Function.comp_def] using b.minusPartner_measurable.comp hx
    have hv : Measurable (fun q : PhysicalFlightState × EventParameter => q.1.2.2) := by fun_prop
    have hn : Measurable (fun q : PhysicalFlightState × EventParameter => q.2.2) := by fun_prop
    have hu : Measurable (fun q : PhysicalFlightState × EventParameter =>
        markedChild m q.1.2.2 (b.plusPartner (mediumPoint endTime q.1 q.2.1))
          (b.minusPartner (mediumPoint endTime q.1 q.2.1)) q.2.2.1) := by
      unfold markedChild
      split
      · exact hv
      · split
        · simpa only [Function.comp_def] using child_measurable.comp ((hv.prodMk hplus).prodMk hn)
        · simpa only [Function.comp_def] using child_measurable.comp ((hv.prodMk hminus).prodMk hn)
    exact (show Measurable (fun q : PhysicalFlightState × EventParameter => q.1.1-q.2.1) by fun_prop).prodMk
      (hx.snd.prodMk hu)
  have hm : Measurable (fun q : HistoryMark × (PhysicalFlightState × EventParameter) =>
      mediumParameterState b endTime q.2.1 (q.1,q.2.2)) :=
    measurable_from_prod_countable_right hfixed
  simpa only [Function.comp_def] using hm.comp
    (show Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      (q.2.1,(q.1,q.2.2))) by fun_prop)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite parameter words in a measurable two-beam medium -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumWordState_measurable (b : BeamCoefficients) (endTime : ℝ) (n : ℕ) :
    Measurable (fun q : PhysicalFlightState × ParameterWord n => mediumWordState b endTime n q.1 q.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    have hh : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by fun_prop
    have ht : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => q.2.2) := by fun_prop
    have hs : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) =>
        (mediumParameterState b endTime q.1 q.2.1,q.2.2)) :=
      ((mediumParameterState_measurable b endTime).comp hh).prodMk ht
    exact ih.comp hs

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Geometric stability of finite marked words along the actual medium path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem markedParameterState_velocity (p : TimeFlightState) (a : MarkedEventParameter)
    (ha : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∈ referenceRegion) :
    (markedParameterState p a).2.2.1 =
      markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 :=
  stateProjection_coe ha

theorem medium_parameter_velocity_error (b : BeamCoefficients) (endTime : ℝ)
    {p : TimeFlightState} {q : PhysicalFlightState} {a : MarkedEventParameter} {δ ε : ℝ}
    (ha : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∈ referenceRegion)
    (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (hp : ‖b.plusPartner (mediumPoint endTime q a.2.1)-beamAxis‖ ≤ ε)
    (hm : ‖b.minusPartner (mediumPoint endTime q a.2.1)-(-beamAxis)‖ ≤ ε) :
    ‖(mediumParameterState b endTime q a).2.2-(markedParameterState p a).2.2.1‖ ≤ δ+ε := by
  rw [markedParameterState_velocity p a ha]
  exact marked_child_error a.1 (mem_sphere_zero_iff_norm.mp a.2.2.2) hv hp hm

theorem medium_parameter_position_error (b : BeamCoefficients) (endTime : ℝ)
    {p : TimeFlightState} {q : PhysicalFlightState} {a : MarkedEventParameter} {X δ : ℝ}
    (hs : 0 ≤ a.2.1) (hx : ‖q.2.1-p.2.1‖ ≤ X) (hv : ‖q.2.2-p.2.2.1‖ ≤ δ) :
    ‖(mediumParameterState b endTime q a).2.1-(markedParameterState p a).2.1‖ ≤ X+a.2.1*δ := by
  change ‖(q.2.1+a.2.1 • q.2.2)-(p.2.1+a.2.1 • p.2.2.1)‖ ≤ _
  rw [show (q.2.1+a.2.1 • q.2.2)-(p.2.1+a.2.1 • p.2.2.1) =
    (q.2.1-p.2.1)+a.2.1 • (q.2.2-p.2.2.1) by module]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
  exact add_le_add hx (mul_le_mul_of_nonneg_left hv hs)

theorem parameterWordState_time (n : ℕ) (p : TimeFlightState) (a : ParameterWord n)
    (hp : 0 ≤ p.1) (ha : GoodReferenceWord n p a) :
    (parameterWordState n p a).1 ∈ Icc 0 p.1 := by
  induction n generalizing p with
  | zero => exact ⟨hp,le_rfl⟩
  | succ n ih =>
    have hs := markedParameterState_time p a.1 ha.1
    exact ⟨(ih _ a.2 hs.1 ha.2.2).1,(ih _ a.2 hs.1 ha.2.2).2.trans hs.2⟩

theorem medium_word_geometry (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) {p : TimeFlightState} {q : PhysicalFlightState} (a : ParameterWord n)
    {X δ ε : ℝ} (hε : 0 ≤ ε) (hp : 0 ≤ p.1) (ht : q.1 = p.1)
    (hx : ‖q.2.1-p.2.1‖ ≤ X) (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (ha : GoodReferenceWord n p a) (hb : WordNearby b endTime ε n q a) :
    (mediumWordState b endTime n q a).1 = (parameterWordState n p a).1 ∧
    ‖(mediumWordState b endTime n q a).2.1-(parameterWordState n p a).2.1‖ ≤
      X+p.1*(δ+(n:ℝ)*ε) ∧
    ‖(mediumWordState b endTime n q a).2.2-(parameterWordState n p a).2.2.1‖ ≤ δ+(n:ℝ)*ε := by
  induction n generalizing p q X δ with
  | zero =>
    have hδ : 0 ≤ δ := (norm_nonneg _).trans hv
    exact ⟨ht,by simpa only [mediumWordState,parameterWordState,Nat.cast_zero,zero_mul,add_zero]
      using hx.trans (le_add_of_nonneg_right (mul_nonneg hp hδ)),by simpa [mediumWordState,parameterWordState] using hv⟩
  | succ n ih =>
    have hs := markedParameterState_time p a.1 ha.1
    have ht' : (mediumParameterState b endTime q a.1).1 = (markedParameterState p a.1).1 := by
      change q.1-a.1.2.1 = p.1-a.1.2.1
      rw [ht]
    have hx' := medium_parameter_position_error b endTime ha.1.1.le hx hv
    have hv' := medium_parameter_velocity_error b endTime ha.2.1 hv hb.1 hb.2.1
    have H := ih a.2 hs.1 ht' hx' hv' ha.2.2 hb.2.2.2.2
    refine ⟨H.1,H.2.1.trans ?_,?_⟩
    · change X+a.1.2.1*δ+(p.1-a.1.2.1)*(δ+ε+(n:ℝ)*ε) ≤ _
      have hprod : 0 ≤ a.1.2.1*((n:ℝ)+1)*ε :=
        mul_nonneg (mul_nonneg ha.1.1.le (by positivity)) hε
      push_cast
      nlinarith
    · simpa only [mediumWordState,parameterWordState,Nat.cast_add,Nat.cast_one] using
        H.2.2.trans_eq (by ring)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform one-event bounds for nearby measurable beam coefficients -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem nearby_marked_rate_bounds (m : HistoryMark) {v : V} (u : RetainedState)
    {wp wm : V} {bp bm ε D : ℝ}
    (_hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hD : D ≤ 1)
    (hv : ‖v-u.1‖ ≤ D) (hp : ‖wp-beamAxis‖ ≤ ε) (hm : ‖wm-(-beamAxis)‖ ≤ ε)
    (hbp : |bp-1| ≤ ε) (hbm : |bm-1| ≤ ε) :
    (0 ≤ markedRate m v wp wm bp bm ∧ markedRate m v wp wm bp bm ≤ 48*Real.pi) ∧
    (0 ≤ markedRate m u.1 beamAxis (-beamAxis) 1 1 ∧
      markedRate m u.1 beamAxis (-beamAxis) 1 1 ≤ 48*Real.pi) ∧
    |markedRate m v wp wm bp bm-markedRate m u.1 beamAxis (-beamAxis) 1 1| ≤
      4*Real.pi*(2*D+8*ε) := by
  have hu := retainedState_norm u
  have hv6 : ‖v‖ ≤ 6 := by
    have hh := norm_add_le (v-u.1) u.1
    rw [sub_add_cancel] at hh
    linarith
  have hwp : ‖wp‖ ≤ 2 := by
    have hh := norm_add_le (wp-beamAxis) beamAxis
    rw [sub_add_cancel,axis_norms.2.2] at hh
    linarith
  have hwm : ‖wm‖ ≤ 2 := by
    have hh := norm_add_le (wm-(-beamAxis)) (-beamAxis)
    rw [sub_add_cancel,norm_neg,axis_norms.2.2] at hh
    linarith
  have hbpp := abs_le.mp hbp
  have hbmm := abs_le.mp hbm
  have hp0 : 0 ≤ bp := by linarith
  have hm0 : 0 ≤ bm := by linarith
  have hp1 : bp ≤ 5/4 := by linarith
  have hm1 : bm ≤ 5/4 := by linarith
  refine ⟨marked_rate_bounds m hv6 hwp hwm hp0 hm0 hp1 hm1,
    marked_rate_bounds m (by linarith) (by rw [axis_norms.2.2]; norm_num)
      (by rw [norm_neg,axis_norms.2.2]; norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),?_⟩
  have hup : ‖u.1-beamAxis‖ ≤ 6 := (norm_sub_le _ _).trans (by rw [axis_norms.2.2]; linarith)
  have hum : ‖u.1-(-beamAxis)‖ ≤ 6 := (norm_sub_le _ _).trans (by rw [norm_neg,axis_norms.2.2]; linarith)
  have H := marked_rate_error m hp0 hm0 (by linarith) (by linarith) hbp hbm
    (add_le_add hv hp) (add_le_add hv hm) hup hum
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite positive-history weights remain close under beam perturbations -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem wordWeightError_ne_top {M : ℝ≥0∞} (hM : M ≠ ⊤) (n : ℕ) :
    wordWeightError M n ≠ ⊤ := by
  induction n with
  | zero => exact ENNReal.zero_ne_top
  | succ n ih =>
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top hM,ENNReal.mul_ne_top hM ih⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Local coefficient control suffices along every retained finite word -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem wordNearby_of_excursion (b : BeamCoefficients) (endTime A : ℝ) (x₀ : V)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hnear : ∀ y : ℝ × V, y.1 ∈ Icc (endTime-A) endTime → ‖y.2-x₀‖ ≤ 6*A → BeamNear b ε y)
    (n : ℕ) {p : TimeFlightState} {q : PhysicalFlightState} (a : ParameterWord n)
    {δ : ℝ} (hbudget : δ+(n:ℝ)*ε ≤ 1) (hp : p.1 ∈ Icc 0 A) (ht : q.1 = p.1)
    (hx : ‖q.2.1-x₀‖ ≤ 6*(A-p.1)) (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (ha : GoodReferenceWord n p a) : WordNearby b endTime ε n q a := by
  induction n generalizing p q δ with
  | zero => trivial
  | succ n ih =>
    have hs : a.1.2.1 ∈ Ioc 0 p.1 := ha.1
    have hδ : δ ≤ 1 := by nlinarith
    have hv6 : ‖q.2.2‖ ≤ 6 := by
      have hh := norm_add_le (q.2.2-p.2.2.1) p.2.2.1
      rw [sub_add_cancel] at hh
      linarith [retainedState_norm p.2.2]
    have hytime : (mediumPoint endTime q a.1.2.1).1 ∈ Icc (endTime-A) endTime := by
      change endTime-q.1+a.1.2.1 ∈ Icc (endTime-A) endTime
      rw [ht]
      constructor <;> linarith [hp.1,hp.2,hs.1,hs.2]
    have hypos : ‖(mediumPoint endTime q a.1.2.1).2-x₀‖ ≤ 6*(A-(p.1-a.1.2.1)) := by
      change ‖q.2.1+a.1.2.1 • q.2.2-x₀‖ ≤ _
      rw [show q.2.1+a.1.2.1 • q.2.2-x₀ = (q.2.1-x₀)+a.1.2.1 • q.2.2 by module]
      have hnorm := norm_add_le (q.2.1-x₀) (a.1.2.1 • q.2.2)
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1.le] at hnorm
      have hmul := mul_le_mul_of_nonneg_left hv6 hs.1.le
      linarith
    have hybound : ‖(mediumPoint endTime q a.1.2.1).2-x₀‖ ≤ 6*A := hypos.trans (by linarith [hs.2])
    have hb := hnear (mediumPoint endTime q a.1.2.1) hytime hybound
    refine ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,?_⟩
    apply ih a.2 (p := markedParameterState p a.1) (δ := δ+ε)
    · push_cast at hbudget ⊢
      linarith
    · change p.1-a.1.2.1 ∈ Icc 0 A
      constructor <;> linarith [hp.2,hs.1,hs.2]
    · change q.1-a.1.2.1 = p.1-a.1.2.1
      rw [ht]
    · exact hypos
    · exact medium_parameter_velocity_error b endTime ha.2.1 hv hb.1 hb.2.1
    · exact ha.2.2

theorem wordNearby_from_start (b : BeamCoefficients) (endTime A : ℝ) (z : FlightState)
    {ε : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hnear : ∀ y : ℝ × V, y.1 ∈ Icc (endTime-A) endTime → ‖y.2-z.1‖ ≤ 6*A → BeamNear b ε y)
    (n : ℕ) (hn : (n:ℝ)*ε ≤ 1) (a : ParameterWord n) (ha : GoodReferenceWord n (A,z) a) :
    WordNearby b endTime ε n (embedFlightState (A,z)) a := by
  apply wordNearby_of_excursion b endTime A z.1 hε hnear n (p := (A,z)) a (δ := 0)
  · simpa using hn
  · exact ⟨hA,le_rfl⟩
  · rfl
  · simp [embedFlightState]
  · simp [embedFlightState]
  · exact ha

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Endpoint margins for the same finite marked parameters in the nearby medium -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finishMediumFlight_error {p : TimeFlightState} {q : PhysicalFlightState} {X δ : ℝ}
    (hp : 0 ≤ p.1) (ht : q.1 = p.1)
    (hx : ‖q.2.1-p.2.1‖ ≤ X) (hv : ‖q.2.2-p.2.2.1‖ ≤ δ) :
    ‖(finishMediumFlight q).1-(finishFlight p).1‖ ≤ X+p.1*δ := by
  change ‖(q.2.1+q.1 • q.2.2)-(p.2.1+p.1 • p.2.2.1)‖ ≤ _
  rw [ht,show (q.2.1+p.1 • q.2.2)-(p.2.1+p.1 • p.2.2.1) =
    (q.2.1-p.2.1)+p.1 • (q.2.2-p.2.2.1) by module]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hp]
  exact add_le_add hx (mul_le_mul_of_nonneg_left hv hp)

theorem medium_word_endpoint_error (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (a : ParameterWord n) {ε : ℝ}
    (hε : 0 ≤ ε) (hp : 0 ≤ p.1) (ha : GoodReferenceWord n p a)
    (hb : WordNearby b endTime ε n (embedFlightState p) a) :
    ‖(finishMediumFlight (mediumWordState b endTime n (embedFlightState p) a)).1-
      (finishFlight (parameterWordState n p a)).1‖ ≤ 2*p.1*((n:ℝ)*ε) ∧
    ‖(finishMediumFlight (mediumWordState b endTime n (embedFlightState p) a)).2-
      (finishFlight (parameterWordState n p a)).2.1‖ ≤ (n:ℝ)*ε := by
  have H := medium_word_geometry b endTime n a (X := 0) (δ := 0) hε hp rfl
    (by simp [embedFlightState]) (by simp [embedFlightState]) ha hb
  simp only [zero_add] at H
  have ht := parameterWordState_time n p a hp ha
  refine ⟨?_,H.2.2⟩
  have hh := finishMediumFlight_error ht.1 H.1 H.2.1 H.2.2
  refine hh.trans ?_
  calc
    p.1*((n:ℝ)*ε)+(parameterWordState n p a).1*((n:ℝ)*ε)
        ≤ p.1*((n:ℝ)*ε)+p.1*((n:ℝ)*ε) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right ht.2 (by positivity))
    _ = _ := by ring

theorem medium_word_target (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (a : ParameterWord n) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hp : 0 ≤ p.1) (hv : (n:ℝ)*ε ≤ 1)
    (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (ha : GoodReferenceWord n p a) (hb : WordNearby b endTime ε n (embedFlightState p) a)
    (hmem : finishFlight (parameterWordState n p a) ∈ blockTarget p.2.1 p.1 κ d) :
    finishMediumFlight (mediumWordState b endTime n (embedFlightState p) a) ∈
      physicalBlockTarget p.2.1 p.1 κ d := by
  have H := medium_word_endpoint_error b endTime n p a hε hp ha hb
  exact block_target_perturb hmem (H.1.trans hx) (H.2.trans hv)

end BoltzmannNonuniqueness.ReferenceGeometry

end

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

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Disjoint annuli in the limiting geometric mesh -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.GeometricMesh

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

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BackgroundCappedLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Relative weights of the actual compressed cold beams -/

noncomputable section

open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialBackground

theorem compressed_scalar_error {R a s : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    |R*s/(1+a*s)-1| ≤ |R-1|+R*(1-s+a) := by
  have hd : 0 < 1+a*s := by positivity
  have hq0 : 0 ≤ s/(1+a*s) := div_nonneg hs hd.le
  have hq1 : s/(1+a*s) ≤ 1 := (div_le_one hd).mpr (by nlinarith)
  have hsq : s^2 ≤ 1 := by nlinarith
  have hsq' := mul_le_mul_of_nonneg_left hsq ha
  have hq : s-s/(1+a*s) ≤ a := by
    have he : (s-a)*(1+a*s) ≤ s := by nlinarith [mul_nonneg (sq_nonneg a) hs]
    have hh := (le_div_iff₀ hd).mpr he
    linarith
  have he : R*s/(1+a*s)-1 = (R-1)+R*(s/(1+a*s)-1) := by ring
  rw [he]
  calc
    _ ≤ |R-1|+|R*(s/(1+a*s)-1)| := abs_add_le _ _
    _ = |R-1|+R*(1-s/(1+a*s)) := by
      rw [abs_mul,abs_of_nonneg hR,abs_of_nonpos (sub_nonpos.mpr hq1)]
      ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by linarith) hR)

theorem weight_eq_relative {r α γ μ t : ℝ} (hr : 0 < r) (hμ : 0 < μ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (K σ z : ℝ) :
    weight K α γ μ t σ z = (K/(4*r))*relativeWeight r α γ μ t σ z := by
  have hS := (S_pos (γ*AxialFlow.foot σ α γ μ t z/μ)).le
  have hprod : 0 ≤ t*α*γ*S (γ*AxialFlow.foot σ α γ μ t z/μ) := by positivity
  have hd : μ+t*α*γ*S (γ*AxialFlow.foot σ α γ μ t z/μ) ≠ 0 := by linarith
  have hd' : 1+(t*α*γ/μ)*S (γ*AxialFlow.foot σ α γ μ t z/μ) ≠ 0 := by positivity
  unfold weight JetCoreDensity.compressed relativeWeight
  field_simp

theorem relativeWeight_error {r α γ μ t : ℝ} (hr : 0 ≤ r) (hμ : 0 < μ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (σ z : ℝ) :
    |relativeWeight r α γ μ t σ z-1| ≤ |r/μ-1|+
      (r/μ)*(1-S (γ*AxialFlow.foot σ α γ μ t z/μ)+t*α*γ/μ) :=
  compressed_scalar_error (div_nonneg hr hμ.le) (by positivity)
    (S_pos _).le (S_le_one _)

theorem foot_abs_bound {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t)
    (σ γ μ z : ℝ) : |AxialFlow.foot σ α γ μ t z| ≤ |z|+t*(|σ|+α) := by
  have hv := AxialFlow.velocity_sub_center_le (σ := σ) (γ := γ) (s := μ) (t := t) (z := z) hα
  have hb : |AxialFlow.velocity σ α γ μ t z| ≤ |σ|+α := by
    have hh := abs_add_le (AxialFlow.velocity σ α γ μ t z-σ) σ
    rw [sub_add_cancel] at hh
    linarith
  unfold AxialFlow.foot
  calc
    _ ≤ |z|+|t*AxialFlow.velocity σ α γ μ t z| := abs_sub _ _
    _ = |z|+t*|AxialFlow.velocity σ α γ μ t z| := by rw [abs_mul,abs_of_nonneg ht]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hb ht)

end BoltzmannNonuniqueness.AxialBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricPositiveCompact
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurable two-beam coefficients from the actual geometric cold profiles -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem beamDensity_eq_relative {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 < r) (η σ : ℝ) (p : ℝ × Velocity) (ht : 0 ≤ p.1) :
    beamDensity θ η α γ r σ p = AxialBackground.relativeWeight r α γ
      (scale θ η (transverse p.2)) p.1 σ (axial p.2) := by
  unfold beamDensity
  rw [max_eq_right ht,AxialBackground.weight_eq_relative hr (scale_pos hθ η _) hα hγ ht]
  field_simp

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The selected two-beam field is the actual cold background away from null mesh circles -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem beamDensity_nonneg {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η σ : ℝ) (p : ℝ × Velocity) :
    0 ≤ beamDensity θ η α γ r σ p := by
  apply mul_nonneg (mul_nonneg (by norm_num) hr)
  exact AxialBackground.weight_nonneg (by norm_num) hα hγ (scale_pos hθ η _) (le_max_left 0 _) _ _

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MediumStateCollision
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The positive marked collision kernel of a measurable two-beam medium -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumMarkedRate_measurable (b : BeamCoefficients) (m : HistoryMark) :
    Measurable (mediumMarkedRate b m) := by
  have hp := b.plusPartner_measurable.comp (measurable_fst : Measurable (Prod.fst : MediumState → ℝ × V))
  have hm := b.minusPartner_measurable.comp (measurable_fst : Measurable (Prod.fst : MediumState → ℝ × V))
  have hbp := b.plusDensity_measurable.comp (measurable_fst : Measurable (Prod.fst : MediumState → ℝ × V))
  have hbm := b.minusDensity_measurable.comp (measurable_fst : Measurable (Prod.fst : MediumState → ℝ × V))
  unfold mediumMarkedRate
  apply Measurable.ennreal_ofReal
  unfold markedRate
  split
  · exact measurable_const.sub (measurable_const.mul
      ((hbp.mul (measurable_snd.sub hp).norm).add (hbm.mul (measurable_snd.sub hm).norm)))
  · split
    · exact (measurable_const.mul hbp).mul (measurable_snd.sub hp).norm
    · exact (measurable_const.mul hbm).mul (measurable_snd.sub hm).norm

theorem mediumMarkedKernel_apply (b : BeamCoefficients) (m : HistoryMark) (z : MediumState) :
    mediumMarkedKernel b m z = mediumMarkedRate b m z • markedChildKernel b m z := by
  rw [mediumMarkedKernel,Kernel.withDensity_apply]
  · exact withDensity_const _
  · exact (mediumMarkedRate_measurable b m).comp measurable_fst

theorem mediumMarkedKernel_lintegral (b : BeamCoefficients) (m : HistoryMark)
    (z : MediumState) {F : V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂mediumMarkedKernel b m z) = mediumMarkedRate b m z *
      ∫⁻ n : Sphere, F (markedChild m z.2 (b.plusPartner z.1) (b.minusPartner z.1) n.1)
        ∂sphereProbability := by
  rw [mediumMarkedKernel_apply,lintegral_smul_measure,smul_eq_mul]
  by_cases h0 : m = 0
  · simp [markedChildKernel,h0,markedChild,Kernel.deterministic_apply,lintegral_dirac]
  · rw [markedChildKernel,ite_eq_right h0,Kernel.comap_apply,outgoing_apply,
      lintegral_map hF (by unfold child; fun_prop)]
    congr 1
    apply lintegral_congr
    intro n
    simp [markedChild,h0]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Physical projection and local bounds of the positive two-beam kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumCollisionKernel_lintegral (b : BeamCoefficients) (z : MediumState)
    {F : V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂mediumCollisionKernel b z) =
      ∑ m : HistoryMark, mediumMarkedRate b m z *
        ∫⁻ n : Sphere, F (markedChild m z.2 (b.plusPartner z.1) (b.minusPartner z.1) n.1)
          ∂sphereProbability := by
  simp only [mediumCollisionKernel,add_apply,lintegral_add_measure,
    mediumMarkedKernel_lintegral b _ z hF,Fin.sum_univ_three]

theorem mediumCollisionKernel_projection (b : BeamCoefficients) (z : MediumState) :
    mediumCollisionKernel b z =
      ENNReal.ofReal (4*Real.pi*b.plusDensity z.1*‖z.2-b.plusPartner z.1‖) •
        outgoing (z.2,b.plusPartner z.1)+
      ENNReal.ofReal (4*Real.pi*b.minusDensity z.1*‖z.2-b.minusPartner z.1‖) •
        outgoing (z.2,b.minusPartner z.1)+
      ENNReal.ofReal (48*Real.pi-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
        (b.plusDensity z.1) (b.minusDensity z.1)) • Measure.dirac z.2 := by
  simp only [mediumCollisionKernel,add_apply,mediumMarkedKernel_apply,
    mediumMarkedRate,markedChildKernel,markedRate,Fin.isValue,one_ne_zero,
    show (2 : HistoryMark) ≠ 0 by decide,show (2 : HistoryMark) ≠ 1 by decide,
    ↓reduceIte,Kernel.deterministic_apply,Kernel.comap_apply]
  ac_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite medium histories equal powers of the actual marked event kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finishMediumFlight_measurable : Measurable finishMediumFlight := by
  unfold finishMediumFlight
  fun_prop

theorem physicalBlockTarget_measurable (x : V) (A κ d : ℝ) :
    MeasurableSet (physicalBlockTarget x A κ d) := by
  unfold physicalBlockTarget
  measurability

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedCollisionHistories
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # Marked reference and medium weights with an additional holding intensity -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem holdingWeight_measurable (C : ℝ≥0) : Measurable (holdingWeight C) :=
  measurable_of_countable _

theorem dampedParameterDensity_measurable (C : ℝ≥0) :
    Measurable (fun q : TimeFlightState × MarkedEventParameter => dampedParameterDensity C q.1 q.2) := by
  have hw : Measurable (fun q : TimeFlightState × MarkedEventParameter => waitingDensity q.1 q.2.2.1) :=
    waitingDensity_measurable.comp (show Measurable (fun q : TimeFlightState × MarkedEventParameter => (q.1,q.2.2.1)) by fun_prop)
  have hc : Measurable (fun q : TimeFlightState × MarkedEventParameter => clockSurvival C q.2.2.1) := by
    unfold clockSurvival
    fun_prop
  have hm : Measurable (fun q : TimeFlightState × MarkedEventParameter =>
      markedReferenceWeight q.1.2.2 q.2.1 q.2.2.2) := by
    have h : Measurable (fun q : HistoryMark × (RetainedState × Sphere) => markedReferenceWeight q.2.1 q.1 q.2.2) :=
      measurable_from_prod_countable_right (fun m : HistoryMark => markedReferenceWeight_measurable m)
    exact h.comp (show Measurable (fun q : TimeFlightState × MarkedEventParameter => (q.2.1,(q.1.2.2,q.2.2.2))) by fun_prop)
  exact (hw.mul hc).mul (hm.add ((holdingWeight_measurable C).comp (by fun_prop)))

theorem dampedMediumParameterDensity_measurable (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      dampedMediumParameterDensity C b endTime q.1 q.2) := by
  have hfixed (m : HistoryMark) : Measurable (fun q : PhysicalFlightState × EventParameter =>
      dampedMediumParameterDensity C b endTime q.1 (m,q.2)) := by
    have hx : Measurable (fun q : PhysicalFlightState × EventParameter => mediumPoint endTime q.1 q.2.1) :=
      (mediumPoint_measurable endTime).comp (show Measurable (fun q : PhysicalFlightState × EventParameter => (q.1,q.2.1)) by fun_prop)
    have hplus := b.plusPartner_measurable.comp hx
    have hminus := b.minusPartner_measurable.comp hx
    have hrplus := b.plusDensity_measurable.comp hx
    have hrminus := b.minusDensity_measurable.comp hx
    have hv : Measurable (fun q : PhysicalFlightState × EventParameter => q.1.2.2) := by fun_prop
    have hw : Measurable (fun q : PhysicalFlightState × EventParameter =>
        (Ioc 0 q.1.1).indicator (1 : ℝ → ℝ≥0∞) q.2.1) := by
      let A : Set (PhysicalFlightState × EventParameter) := {q | 0 < q.2.1 ∧ q.2.1 ≤ q.1.1}
      have hA : MeasurableSet A := by dsimp [A]; measurability
      exact measurable_const.indicator hA
    have hc : Measurable (fun q : PhysicalFlightState × EventParameter => clockSurvival C q.2.1) := by
      unfold clockSurvival
      fun_prop
    have hrate : Measurable (fun q : PhysicalFlightState × EventParameter =>
        markedRate m q.1.2.2 (b.plusPartner (mediumPoint endTime q.1 q.2.1))
          (b.minusPartner (mediumPoint endTime q.1 q.2.1))
          (b.plusDensity (mediumPoint endTime q.1 q.2.1))
          (b.minusDensity (mediumPoint endTime q.1 q.2.1))) := by
      unfold markedRate
      split
      · exact measurable_const.sub (measurable_const.mul
          ((hrplus.mul (hv.sub hplus).norm).add (hrminus.mul (hv.sub hminus).norm)))
      · split
        · exact (measurable_const.mul hrplus).mul (hv.sub hplus).norm
        · exact (measurable_const.mul hrminus).mul (hv.sub hminus).norm
    exact (hw.mul hc).mul (hrate.ennreal_ofReal.add (measurable_const : Measurable (fun _ : PhysicalFlightState × EventParameter => holdingWeight C m)))
  have hm : Measurable (fun q : HistoryMark × (PhysicalFlightState × EventParameter) =>
      dampedMediumParameterDensity C b endTime q.2.1 (q.1,q.2.2)) :=
    measurable_from_prod_countable_right hfixed
  exact hm.comp (show Measurable (fun q : PhysicalFlightState × MarkedEventParameter => (q.2.1,(q.1,q.2.2))) by fun_prop)

theorem holdingWeight_le {C : ℝ≥0} (m : HistoryMark) :
    holdingWeight C m ≤ ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) := by
  unfold holdingWeight
  split
  · exact le_rfl
  · exact bot_le

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The extra holding intensity preserves the local perturbation error -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem rate_add_holding_le {C : ℝ≥0} (hC : referenceClock ≤ C)
    {r : ℝ} (hr : r ≤ (referenceClock:ℝ)) (m : HistoryMark) :
    ENNReal.ofReal r+holdingWeight C m ≤ ENNReal.ofReal (C:ℝ) := by
  calc
    _ ≤ ENNReal.ofReal (referenceClock:ℝ)+ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hr) (holdingWeight_le m)
    _ = _ := by
      rw [← ENNReal.ofReal_add (show 0 ≤ (referenceClock:ℝ) from referenceClock.property)
        (show 0 ≤ (C:ℝ)-(referenceClock:ℝ) from sub_nonneg.mpr hC)]
      congr 1
      ring

theorem nearby_damped_parameter_bounds {C Cmax : ℝ≥0} (hC : referenceClock ≤ C) (hCmax : C ≤ Cmax)
    (b : BeamCoefficients) (endTime : ℝ)
    {p : TimeFlightState} {q : PhysicalFlightState} {a : MarkedEventParameter} {ε D : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hD : D ≤ 1) (ht : q.1 = p.1)
    (hv : ‖q.2.2-p.2.2.1‖ ≤ D) (hs : a.2.1 ∈ Ioc 0 p.1)
    (ha : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∈ referenceRegion)
    (hp : ‖b.plusPartner (mediumPoint endTime q a.2.1)-beamAxis‖ ≤ ε)
    (hm : ‖b.minusPartner (mediumPoint endTime q a.2.1)-(-beamAxis)‖ ≤ ε)
    (hbp : |b.plusDensity (mediumPoint endTime q a.2.1)-1| ≤ ε)
    (hbm : |b.minusDensity (mediumPoint endTime q a.2.1)-1| ≤ ε) :
    dampedParameterDensity C p a ≤ ENNReal.ofReal (Cmax:ℝ) ∧
    dampedMediumParameterDensity C b endTime q a ≤ ENNReal.ofReal (Cmax:ℝ) ∧
    dampedParameterDensity C p a ≤ dampedMediumParameterDensity C b endTime q a+
      ENNReal.ofReal (4*Real.pi*(2*D+8*ε)) := by
  have H := nearby_marked_rate_bounds a.1 p.2.2 hε hε1 hD hv hp hm hbp hbm
  have hc := clockSurvival_le_one C hs.1.le
  have hδ : 0 ≤ 4*Real.pi*(2*D+8*ε) := by
    have : 0 ≤ D := (norm_nonneg _).trans hv
    positivity
  have hr : ENNReal.ofReal (markedRate a.1 p.2.2.1 beamAxis (-beamAxis) 1 1) ≤
      ENNReal.ofReal (markedRate a.1 q.2.2
        (b.plusPartner (mediumPoint endTime q a.2.1))
        (b.minusPartner (mediumPoint endTime q a.2.1))
        (b.plusDensity (mediumPoint endTime q a.2.1))
        (b.minusDensity (mediumPoint endTime q a.2.1)))+
      ENNReal.ofReal (4*Real.pi*(2*D+8*ε)) := by
    rw [← ENNReal.ofReal_add H.1.1 hδ]
    apply ENNReal.ofReal_le_ofReal
    have hdiff := H.2.2
    rw [abs_sub_comm] at hdiff
    linarith [le_abs_self (markedRate a.1 p.2.2.1 beamAxis (-beamAxis) 1 1-
      markedRate a.1 q.2.2 (b.plusPartner (mediumPoint endTime q a.2.1))
        (b.minusPartner (mediumPoint endTime q a.2.1))
        (b.plusDensity (mediumPoint endTime q a.2.1))
        (b.minusDensity (mediumPoint endTime q a.2.1)))]
  have hR := (rate_add_holding_le hC H.2.1.2 a.1).trans (ENNReal.ofReal_le_ofReal hCmax)
  have hM := (rate_add_holding_le hC H.1.2 a.1).trans (ENNReal.ofReal_le_ofReal hCmax)
  simp only [dampedParameterDensity,dampedReferenceWeight,waitingDensity,
    markedReferenceWeight,dampedMediumParameterDensity,ht,indicator_of_mem hs,
    indicator_of_mem ha,Pi.one_apply,one_mul,mul_one]
  refine ⟨(mul_le_of_le_one_left' hc).trans hR,(mul_le_of_le_one_left' hc).trans hM,?_⟩
  calc
    _ ≤ clockSurvival C a.2.1*((_+ENNReal.ofReal (4*Real.pi*(2*D+8*ε)))+holdingWeight C a.1) :=
      mul_le_mul' le_rfl (add_le_add hr le_rfl)
    _ = clockSurvival C a.2.1*((_+holdingWeight C a.1)+ENNReal.ofReal (4*Real.pi*(2*D+8*ε))) := by
      congr 1
      ac_rfl
    _ = _ := mul_add _ _ _
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left' hc)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite positive weights at a common enlarged damping rate -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_word_weight_comparison (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (M η : ℝ≥0∞)
    (n : ℕ) (p : TimeFlightState) (q : PhysicalFlightState) (a : ParameterWord n)
    (h : DampedWordCoefficientClose C b endTime M η n p q a) :
    dampedWordDensity C n p a ≤ M^n ∧ dampedMediumWordDensity C b endTime n q a ≤ M^n ∧
    dampedWordDensity C n p a ≤ dampedMediumWordDensity C b endTime n q a+wordWeightError M n*η := by
  induction n generalizing p q with
  | zero => simp [dampedWordDensity,dampedMediumWordDensity,wordWeightError]
  | succ n ih =>
    obtain ⟨hR,hA,hRA⟩ := ih _ _ a.2 h.2.2.2
    refine ⟨?_,?_,?_⟩
    · exact (mul_le_mul' h.1 hR).trans_eq (pow_succ' M n).symm
    · exact (mul_le_mul' h.2.1 hA).trans_eq (pow_succ' M n).symm
    · change dampedParameterDensity C p a.1 *
          dampedWordDensity C n (markedParameterState p a.1) a.2 ≤
        dampedMediumParameterDensity C b endTime q a.1 *
          dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+_
      calc
        _ ≤ dampedParameterDensity C p a.1 *
            (dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              wordWeightError M n*η) := mul_le_mul' le_rfl hRA
        _ = dampedParameterDensity C p a.1 *
              dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              dampedParameterDensity C p a.1*(wordWeightError M n*η) := mul_add _ _ _
        _ ≤ (dampedMediumParameterDensity C b endTime q a.1+η)*
              dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              M*(wordWeightError M n*η) :=
          add_le_add (mul_le_mul' h.2.2.1 le_rfl) (mul_le_mul' h.1 le_rfl)
        _ = dampedMediumParameterDensity C b endTime q a.1 *
              dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              η*dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              M*(wordWeightError M n*η) := by rw [add_mul]
        _ ≤ dampedMediumParameterDensity C b endTime q a.1 *
              dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              η*M^n+M*(wordWeightError M n*η) :=
          add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hA)) le_rfl
        _ = _ := by simp only [wordWeightError] <;> ring

theorem damped_word_coefficients_close {C Cmax : ℝ≥0} (hC : referenceClock ≤ C) (hCmax : C ≤ Cmax) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) {p : TimeFlightState} {q : PhysicalFlightState} (a : ParameterWord n)
    {δ ε D : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hD : D ≤ 1)
    (hbudget : δ+(n:ℝ)*ε ≤ D) (ht : q.1 = p.1) (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (ha : GoodReferenceWord n p a) (hb : WordNearby b endTime ε n q a) :
    DampedWordCoefficientClose C b endTime (ENNReal.ofReal (Cmax:ℝ))
      (ENNReal.ofReal (4*Real.pi*(2*D+8*ε))) n p q a := by
  induction n generalizing p q δ with
  | zero => trivial
  | succ n ih =>
    have hvD : ‖q.2.2-p.2.2.1‖ ≤ D := hv.trans (by nlinarith)
    have H := nearby_damped_parameter_bounds hC hCmax b endTime hε hε1 hD ht hvD
      ha.1 ha.2.1 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1
    refine ⟨H.1,H.2.1,H.2.2,?_⟩
    apply ih a.2 (δ := δ+ε)
    · push_cast at hbudget ⊢
      linarith
    · change q.1-a.1.2.1 = p.1-a.1.2.1
      rw [ht]
    · exact medium_parameter_velocity_error b endTime ha.2.1 hv hb.1 hb.2.1
    · exact ha.2.2
    · exact hb.2.2.2.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical two-beam collision law with the additional holding mark -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumCollision_apply (C : ℝ≥0) (b : BeamCoefficients) (z : MediumState) :
    dampedMediumCollision C b z = mediumCollisionKernel b z+
      ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) • Measure.dirac z.2 := by
  rw [dampedMediumCollision,add_apply,Kernel.withDensity_apply _ (by fun_prop),
    withDensity_const,Kernel.deterministic_apply]

theorem dampedMediumCollision_lintegral (C : ℝ≥0) (b : BeamCoefficients) (z : MediumState)
    {F : V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂dampedMediumCollision C b z) =
      ∑ m : HistoryMark, (mediumMarkedRate b m z+holdingWeight C m) *
        ∫⁻ n : Sphere, F (markedChild m z.2 (b.plusPartner z.1) (b.minusPartner z.1) n.1)
          ∂sphereProbability := by
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib,← mediumCollisionKernel_lintegral b z hF,
    dampedMediumCollision_apply,lintegral_add_measure,lintegral_smul_measure,
    lintegral_dirac,smul_eq_mul]
  congr 1
  rw [Fin.sum_univ_three]
  simp [holdingWeight,markedChild]

theorem dampedMediumCollision_projection {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (z : MediumState)
    (hf : mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
      (b.plusDensity z.1) (b.minusDensity z.1) ≤ (referenceClock:ℝ)) :
    dampedMediumCollision C b z =
      ENNReal.ofReal (4*Real.pi*b.plusDensity z.1*‖z.2-b.plusPartner z.1‖) •
        outgoing (z.2,b.plusPartner z.1)+
      ENNReal.ofReal (4*Real.pi*b.minusDensity z.1*‖z.2-b.minusPartner z.1‖) •
        outgoing (z.2,b.minusPartner z.1)+
      ENNReal.ofReal ((C:ℝ)-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
        (b.plusDensity z.1) (b.minusDensity z.1)) • Measure.dirac z.2 := by
  have hf' : 0 ≤ 48*Real.pi-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
      (b.plusDensity z.1) (b.minusDensity z.1) := sub_nonneg.mpr hf
  have hδ : 0 ≤ (C:ℝ)-(referenceClock:ℝ) := sub_nonneg.mpr hC
  have he : ENNReal.ofReal (48*Real.pi-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
        (b.plusDensity z.1) (b.minusDensity z.1))+
      ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) =
      ENNReal.ofReal ((C:ℝ)-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
        (b.plusDensity z.1) (b.minusDensity z.1)) := by
    rw [← ENNReal.ofReal_add hf' hδ]
    congr 1
    change 48*Real.pi-_+((C:ℝ)-48*Real.pi) = (C:ℝ)-_
    ring
  rw [dampedMediumCollision_apply,mediumCollisionKernel_projection,add_assoc,← add_smul,he]

theorem dampedMediumStateCollision_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂dampedMediumStateCollision C b endTime p) =
      ∫⁻ v, F (p.1,(p.2.1,v)) ∂dampedMediumCollision C b ((endTime-p.1,p.2.1),p.2.2) := by
  have hm : Measurable (fun q : PhysicalFlightState × V => (q.1.1,(q.1.2.1,q.2))) := by fun_prop
  rw [dampedMediumStateCollision,Kernel.lintegral_map _ hm p hF]
  have hc : Measurable (fun q : PhysicalFlightState × V => F (q.1.1,(q.1.2.1,q.2))) := hF.comp hm
  exact Kernel.lintegral_id_prod hc _ p

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact angular formula for the reference kernel with additional holding -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedReferenceWeight_measurable (C : ℝ≥0) (m : HistoryMark) :
    Measurable (fun p : RetainedState × Sphere => dampedReferenceWeight C p.1 m p.2) :=
  (markedReferenceWeight_measurable m).add measurable_const

theorem dampedReference_integral (C : ℝ≥0) (v : RetainedState) {F : RetainedState → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ u, F u ∂branchingAt C v) =
      ∑ m : HistoryMark, ∫⁻ n, dampedReferenceWeight C v m n*F (markedReferenceState v m n)
        ∂sphereProbability := by
  have he (m : HistoryMark) :
      (∫⁻ n, dampedReferenceWeight C v m n*F (markedReferenceState v m n) ∂sphereProbability) =
      (∫⁻ n, markedReferenceWeight v m n*F (markedReferenceState v m n) ∂sphereProbability)+
      ∫⁻ n, holdingWeight C m*F (markedReferenceState v m n) ∂sphereProbability := by
    simp only [dampedReferenceWeight,add_mul]
    have hmap : Measurable (fun n : Sphere => (v,n)) := measurable_const.prodMk measurable_id
    have hw : Measurable (fun n : Sphere => markedReferenceWeight v m n) :=
      by simpa only [Function.comp_def] using (markedReferenceWeight_measurable m).comp hmap
    have hs : Measurable (fun n : Sphere => markedReferenceState v m n) :=
      by simpa only [Function.comp_def] using (markedReferenceState_measurable m).comp hmap
    exact lintegral_add_left (hw.mul (hF.comp hs)) _
  simp_rw [he]
  rw [Finset.sum_add_distrib,← markedReference_integral v hF,branchingAt_apply,
    lintegral_add_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul]
  congr 1
  rw [Fin.sum_univ_three]
  simp [holdingWeight,markedReferenceState,markedChild,stateProjection_apply]

theorem damped_eventHistory_marked_succ (C : ℝ≥0) {D : TimeFlightState → ℝ≥0∞}
    (hD : Measurable D) (n : ℕ) (p : TimeFlightState) :
    eventHistory C (branchingAt C) D (n+1) p =
      ∫⁻ s in Ioc 0 p.1, clockSurvival C s *
        ∑ m : HistoryMark, ∫⁻ θ, dampedReferenceWeight C p.2.2 m θ *
          eventHistory C (branchingAt C) D n
            (advanceState p s (markedReferenceState p.2.2 m θ)) ∂sphereProbability := by
  have he : (eventStep C (branchingAt C))^(n+1) =
      ((eventStep C (branchingAt C))^n) ∘ₖ eventStep C (branchingAt C) := by
    simpa only [pow_one] using Kernel.pow_add (eventStep C (branchingAt C)) n 1
  rw [eventHistory,he,Kernel.lintegral_comp _ _ _ hD]
  change (∫⁻ q, eventHistory C (branchingAt C) D n q ∂eventStep C (branchingAt C) p) = _
  rw [eventStep_lintegral _ _ _ (eventHistory_measurable _ _ hD n)]
  apply lintegral_congr
  intro s
  have hm : Measurable (fun u : RetainedState => eventHistory C (branchingAt C) D n (advanceState p s u)) :=
    (eventHistory_measurable _ _ hD n).comp (by unfold advanceState; fun_prop)
  rw [dampedReference_integral C p.2.2 hm]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Fixed mark, time and angle integrals at the larger damping rate -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedReferenceParameterDensity_measurable (C : ℝ≥0) (m : HistoryMark) :
    Measurable (fun q : TimeFlightState × EventParameter => dampedReferenceParameterDensity C q.1 m q.2) :=
  (dampedParameterDensity_measurable C).comp
    (show Measurable (fun q : TimeFlightState × EventParameter => (q.1,(m,q.2))) by fun_prop)

theorem damped_reference_parameter_integral (C : ℝ≥0) {F : TimeFlightState → ℝ≥0∞} (hF : Measurable F)
    (p : TimeFlightState) (m : HistoryMark) {T : ℝ} (hT : p.1 ≤ T) :
    (∫⁻ a, dampedReferenceParameterDensity C p m a*F (referenceParameterState p m a) ∂eventParameterMeasure T) =
      ∫⁻ s in Ioc 0 p.1, clockSurvival C s *
        ∫⁻ θ, dampedReferenceWeight C p.2.2 m θ *
          F (advanceState p s (markedReferenceState p.2.2 m θ)) ∂sphereProbability := by
  have hm : Measurable (fun a : EventParameter => dampedReferenceParameterDensity C p m a*
      F (referenceParameterState p m a)) :=
    ((dampedReferenceParameterDensity_measurable C m).comp (measurable_const.prodMk measurable_id)).mul
      (hF.comp ((referenceParameterState_measurable m).comp (measurable_const.prodMk measurable_id)))
  rw [eventParameterMeasure,lintegral_prod _ hm.aemeasurable]
  have he (s : ℝ) : (∫⁻ θ, dampedReferenceParameterDensity C p m (s,θ)*
      F (referenceParameterState p m (s,θ)) ∂sphereProbability) =
      (Ioc 0 p.1).indicator (fun r => clockSurvival C r*
        ∫⁻ θ, dampedReferenceWeight C p.2.2 m θ*
          F (advanceState p r (markedReferenceState p.2.2 m θ)) ∂sphereProbability) s := by
    by_cases hs : s ∈ Ioc 0 p.1
    · simp only [dampedReferenceParameterDensity,dampedParameterDensity,referenceParameterState,waitingDensity,
        indicator_of_mem hs,Pi.one_apply,one_mul,mul_assoc]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    · simp only [dampedReferenceParameterDensity,dampedParameterDensity,waitingDensity,indicator_of_notMem hs,zero_mul,lintegral_zero]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Ioc,Measure.restrict_restrict_of_subset]
  exact Ioc_subset_Ioc_right hT

theorem damped_eventHistory_parameter_succ (C : ℝ≥0) {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D)
    (n : ℕ) (p : TimeFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    eventHistory C (branchingAt C) D (n+1) p =
      ∑ m : HistoryMark, ∫⁻ a, dampedReferenceParameterDensity C p m a *
        eventHistory C (branchingAt C) D n (referenceParameterState p m a)
          ∂eventParameterMeasure T := by
  rw [damped_eventHistory_marked_succ C hD]
  have h (m : HistoryMark) := damped_reference_parameter_integral C
    (eventHistory_measurable C (branchingAt C) hD n) p m hT
  simp_rw [h]
  simp_rw [Finset.mul_sum]
  apply lintegral_finsetSum
  intro m _
  have hm : Measurable (fun a : EventParameter => dampedReferenceWeight C p.2.2 m a.2 *
      eventHistory C (branchingAt C) D n
        (advanceState p a.1 (markedReferenceState p.2.2 m a.2))) := by
    exact ((dampedReferenceWeight_measurable C m).comp (measurable_const.prodMk measurable_snd)).mul
      ((eventHistory_measurable C (branchingAt C) hD n).comp
        ((referenceParameterState_measurable m).comp (measurable_const.prodMk measurable_id)))
  exact (show Measurable (clockSurvival C) by unfold clockSurvival; fun_prop).mul
    hm.lintegral_prod_right'

theorem damped_eventHistory_marked_parameter_succ (C : ℝ≥0) {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D)
    (n : ℕ) (p : TimeFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    eventHistory C (branchingAt C) D (n+1) p =
      ∫⁻ a, dampedParameterDensity C p a *
        eventHistory C (branchingAt C) D n (markedParameterState p a)
          ∂markedEventMeasure T := by
  have hm : Measurable (fun a : MarkedEventParameter => dampedParameterDensity C p a*
      eventHistory C (branchingAt C) D n (markedParameterState p a)) :=
    (((dampedParameterDensity_measurable C).comp (measurable_const.prodMk measurable_id)).mul
      ((eventHistory_measurable C (branchingAt C) hD n).comp
        (markedParameterState_measurable.comp (measurable_const.prodMk measurable_id))))
  rw [markedEventMeasure,lintegral_prod _ hm.aemeasurable,lintegral_fintype]
  simp only [Measure.count_singleton,mul_one]
  exact damped_eventHistory_parameter_succ C hD n p hT

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact finite reference histories at the enlarged damping rate -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem holdingWeight_ne_top (C : ℝ≥0) (m : HistoryMark) : holdingWeight C m ≠ ⊤ := by
  unfold holdingWeight
  split
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

theorem dampedParameterDensity_ne_top (C : ℝ≥0) (p : TimeFlightState) (a : MarkedEventParameter) :
    dampedParameterDensity C p a ≠ ⊤ := by
  have hw : waitingDensity p a.2.1 ≠ ⊤ := by
    by_cases hs : a.2.1 ∈ Ioc 0 p.1 <;> simp [waitingDensity,hs]
  have hr : markedReferenceWeight p.2.2 a.1 a.2.2 ≠ ⊤ := by
    by_cases ha : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∈ referenceRegion
    · simp [markedReferenceWeight,ha]
    · simp [markedReferenceWeight,ha]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hw ENNReal.ofReal_ne_top)
    (ENNReal.add_ne_top.mpr ⟨hr,holdingWeight_ne_top C a.1⟩)

theorem dampedParameterDensity_zero (C : ℝ≥0) (p : TimeFlightState) (a : MarkedEventParameter)
    (ha : a.2.1 ∉ Ioc 0 p.1) : dampedParameterDensity C p a = 0 := by
  simp [dampedParameterDensity,waitingDensity,ha]

theorem dampedWordDensity_measurable (C : ℝ≥0) (n : ℕ) :
    Measurable (fun q : TimeFlightState × ParameterWord n => dampedWordDensity C n q.1 q.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hh : Measurable (fun q : TimeFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by fun_prop
    have ht : Measurable (fun q : TimeFlightState × ParameterWord (n+1) => q.2.2) := by fun_prop
    have hs : Measurable (fun q : TimeFlightState × ParameterWord (n+1) =>
        (markedParameterState q.1 q.2.1,q.2.2)) :=
      (markedParameterState_measurable.comp hh).prodMk ht
    exact ((dampedParameterDensity_measurable C).comp hh).mul (ih.comp hs)

theorem dampedWord_integral (C : ℝ≥0) {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D)
    (T : ℝ) (n : ℕ) (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) :
    (∫⁻ a, dampedWordDensity C n p a * D (parameterWordState n p a)
      ∂parameterWordMeasure T n) = eventHistory C (branchingAt C) D n p := by
  induction n generalizing p with
  | zero =>
    rw [eventHistory_zero]
    change (∫⁻ _a : PUnit, 1*D p ∂Measure.dirac PUnit.unit) = D p
    rw [lintegral_const,Measure.dirac_apply_of_mem (mem_univ _),mul_one,one_mul]
  | succ n ih =>
    have hmap : Measurable (fun a : ParameterWord (n+1) => (p,a)) :=
      measurable_const.prodMk measurable_id
    have hd : Measurable (fun a : ParameterWord (n+1) => dampedWordDensity C (n+1) p a) := by
      simpa only [Function.comp_def] using (dampedWordDensity_measurable C (n+1)).comp hmap
    have hs : Measurable (fun a : ParameterWord (n+1) => parameterWordState (n+1) p a) := by
      simpa only [Function.comp_def] using (parameterWordState_measurable (n+1)).comp hmap
    have hm : Measurable (fun a : ParameterWord (n+1) =>
        dampedWordDensity C (n+1) p a * D (parameterWordState (n+1) p a)) := hd.mul (hD.comp hs)
    rw [parameterWordMeasure,lintegral_prod _ hm.aemeasurable,
      damped_eventHistory_marked_parameter_succ C hD n p hp.2]
    apply lintegral_congr
    intro a
    change (∫⁻ w, (dampedParameterDensity C p a *
      dampedWordDensity C n (markedParameterState p a) w) *
        D (parameterWordState n (markedParameterState p a) w) ∂parameterWordMeasure T n) = _
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (dampedParameterDensity_ne_top C p a)]
    by_cases ha : a.2.1 ∈ Ioc 0 p.1
    · have ht := markedParameterState_time p a ha
      rw [ih (markedParameterState p a) ⟨ht.1,ht.2.trans hp.2⟩]
    · rw [dampedParameterDensity_zero C p a ha,zero_mul,zero_mul]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Enlarged damping preserves the geometric support of reference words -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedParameterDensity_zero_of_outside (C : ℝ≥0) (p : TimeFlightState)
    (a : MarkedEventParameter)
    (ha : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∉ referenceRegion) :
    dampedParameterDensity C p a = 0 := by
  by_cases hm : a.1 = 0
  · exact False.elim (ha (by simpa only [markedChild,hm,ite_eq_left] using p.2.2.2))
  · simp [dampedParameterDensity,dampedReferenceWeight,markedReferenceWeight,holdingWeight,ha,hm]

theorem goodReferenceWord_of_damped_density_ne_zero (C : ℝ≥0) (n : ℕ)
    (p : TimeFlightState) (a : ParameterWord n) (h : dampedWordDensity C n p a ≠ 0) :
    GoodReferenceWord n p a := by
  induction n generalizing p with
  | zero => trivial
  | succ n ih =>
    have hh := mul_ne_zero_iff.mp h
    refine ⟨?_,?_,ih _ a.2 hh.2⟩
    · by_contra ht
      exact hh.1 (dampedParameterDensity_zero C p a.1 ht)
    · by_contra hc
      exact hh.1 (dampedParameterDensity_zero_of_outside C p a.1 hc)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lower transfer at the same enlarged reference and physical damping -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_medium_word_integrand_bound {C Cmax : ℝ≥0} (hC : referenceClock ≤ C)
    (hCmax : C ≤ Cmax) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (a : ParameterWord n) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hp : 0 ≤ p.1) (hv : (n:ℝ)*ε ≤ 1)
    (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (hnear : GoodReferenceWord n p a → WordNearby b endTime ε n (embedFlightState p) a) :
    dampedWordDensity C n p a * flightSeed C
        ((blockTarget p.2.1 p.1 κ d).indicator 1) (parameterWordState n p a) ≤
      dampedMediumBlockIntegrand C b endTime p κ d n a+dampedHistoryPerturbationError Cmax n ε := by
  by_cases hr : dampedWordDensity C n p a = 0
  · rw [hr,zero_mul]
    exact bot_le
  have ha := goodReferenceWord_of_damped_density_ne_zero C n p a hr
  have hb := hnear ha
  by_cases hmem : finishFlight (parameterWordState n p a) ∈ blockTarget p.2.1 p.1 κ d
  · have hm := medium_word_target b endTime n p a hε hp hv hx ha hb hmem
    have ht := (medium_word_geometry b endTime n a (X := 0) (δ := 0) hε hp rfl
      (by simp [embedFlightState]) (by simp [embedFlightState]) ha hb).1
    have H := damped_word_coefficients_close hC hCmax b endTime n a (δ := 0) (D := (n:ℝ)*ε)
      hε hε1 hv (by simp) rfl (by simp [embedFlightState]) ha hb
    have hweight := (damped_word_weight_comparison C b endTime _ _ n p (embedFlightState p) a H).2.2
    have he : ENNReal.ofReal (4*Real.pi*(2*((n:ℝ)*ε)+8*ε)) =
        ENNReal.ofReal (4*Real.pi*((2*(n:ℝ)+8)*ε)) := by congr 1; ring
    rw [he] at hweight
    have hc := clockSurvival_le_one C (parameterWordState_time n p a hp ha).1
    simp only [flightSeed,dampedMediumBlockIntegrand,indicator_of_mem hmem,indicator_of_mem hm,
      Pi.one_apply,mul_one,ht]
    calc
      _ ≤ (dampedMediumWordDensity C b endTime n (embedFlightState p) a+
          dampedHistoryPerturbationError Cmax n ε)*clockSurvival C (parameterWordState n p a).1 :=
        mul_le_mul' hweight le_rfl
      _ = _ := add_mul _ _ _
      _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' hc)
  · simp only [flightSeed,indicator_of_notMem hmem,mul_zero]
    exact bot_le

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The damped one-event kernel for finite marked histories in a measurable medium -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumParameterDensity_ne_top (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) (a : MarkedEventParameter) :
    dampedMediumParameterDensity C b endTime p a ≠ ⊤ := by
  unfold dampedMediumParameterDensity
  by_cases ht : a.2.1 ∈ Ioc 0 p.1
  · rw [indicator_of_mem ht,Pi.one_apply,one_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,holdingWeight_ne_top C a.1⟩)
  · simp [ht]

theorem dampedMediumEventDensity_measurable (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    Measurable (Function.uncurry (dampedMediumEventDensity C b endTime)) :=
  (dampedMediumParameterDensity_measurable C b endTime).comp measurable_snd

instance dampedMediumEventKernel_isSFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) :
    IsSFiniteKernel (dampedMediumEventKernel C b endTime T) := by
  have hd : IsSFiniteKernel (Kernel.withDensity
      (Kernel.id ×ₖ Kernel.const PhysicalFlightState (markedEventMeasure T))
      (dampedMediumEventDensity C b endTime)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro p a
    exact dampedMediumParameterDensity_ne_top C b endTime a.1 a.2
  unfold dampedMediumEventKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem dampedMediumEventKernel_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂dampedMediumEventKernel C b endTime T p) =
      ∫⁻ a, dampedMediumParameterDensity C b endTime p a * F (mediumParameterState b endTime p a)
        ∂markedEventMeasure T := by
  have hcomp : Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      F (mediumParameterState b endTime q.1 q.2)) := by
    simpa only [Function.comp_def] using hF.comp (mediumParameterState_measurable b endTime)
  have hm : Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      dampedMediumParameterDensity C b endTime q.1 q.2 * F (mediumParameterState b endTime q.1 q.2)) :=
    (dampedMediumParameterDensity_measurable C b endTime).mul hcomp
  rw [dampedMediumEventKernel,Kernel.lintegral_map _ (mediumParameterState_measurable b endTime) p hF,
    Kernel.lintegral_withDensity _ (dampedMediumEventDensity_measurable C b endTime) p hcomp]
  simpa only [dampedMediumEventDensity,Function.comp_def,Kernel.const_apply] using!
    Kernel.lintegral_id_prod hm (Kernel.const PhysicalFlightState (markedEventMeasure T)) p

instance dampedMediumEventKernel_pow_isSFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    IsSFiniteKernel ((dampedMediumEventKernel C b endTime T)^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [show (dampedMediumEventKernel C b endTime T)^(n+1) =
        ((dampedMediumEventKernel C b endTime T)^n) ∘ₖ dampedMediumEventKernel C b endTime T by
      simpa only [pow_one] using Kernel.pow_add (dampedMediumEventKernel C b endTime T) n 1]
    let _ := ih
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Physical collision-time formula for the marked medium event kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_medium_parameter_integral (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) (m : HistoryMark) {T : ℝ} (hT : p.1 ≤ T)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ a, dampedMediumParameterDensity C b endTime p (m,a) *
      F (mediumParameterState b endTime p (m,a)) ∂eventParameterMeasure T) =
    ∫⁻ s in Ioc 0 p.1, clockSurvival C s *
      ((mediumMarkedRate b m (mediumPoint endTime p s,p.2.2)+holdingWeight C m) *
        ∫⁻ n : Sphere, F (mediumParameterState b endTime p (m,(s,n)))
          ∂sphereProbability) := by
  have hpair : Measurable (fun a : EventParameter => (p,(m,a))) := by fun_prop
  have hm : Measurable (fun a : EventParameter =>
      dampedMediumParameterDensity C b endTime p (m,a) *
        F (mediumParameterState b endTime p (m,a))) :=
    ((dampedMediumParameterDensity_measurable C b endTime).comp hpair).mul
      (hF.comp ((mediumParameterState_measurable b endTime).comp hpair))
  rw [eventParameterMeasure,lintegral_prod _ hm.aemeasurable]
  have he (s : ℝ) : (∫⁻ n : Sphere, dampedMediumParameterDensity C b endTime p (m,(s,n)) *
      F (mediumParameterState b endTime p (m,(s,n))) ∂sphereProbability) =
      (Ioc 0 p.1).indicator (fun s => clockSurvival C s *
        ((mediumMarkedRate b m (mediumPoint endTime p s,p.2.2)+holdingWeight C m) *
          ∫⁻ n : Sphere, F (mediumParameterState b endTime p (m,(s,n)))
            ∂sphereProbability)) s := by
    by_cases hs : s ∈ Ioc 0 p.1
    · simp only [dampedMediumParameterDensity,indicator_of_mem hs,Pi.one_apply,one_mul,
        mediumMarkedRate,mul_assoc]
      unfold clockSurvival
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,holdingWeight_ne_top C m⟩)]
    · simp [dampedMediumParameterDensity,hs]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Ioc,Measure.restrict_restrict_of_subset]
  exact Ioc_subset_Ioc_right hT

theorem dampedMediumEventKernel_physical_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂dampedMediumEventKernel C b endTime T p) =
    ∫⁻ s in Ioc 0 p.1, clockSurvival C s *
      ∫⁻ v, F (p.1-s,((mediumPoint endTime p s).2,v))
        ∂dampedMediumCollision C b (mediumPoint endTime p s,p.2.2) := by
  rw [dampedMediumEventKernel_lintegral C b endTime T p hF]
  have hpair : Measurable (fun a : MarkedEventParameter => (p,a)) := by fun_prop
  have hm : Measurable (fun a : MarkedEventParameter =>
      dampedMediumParameterDensity C b endTime p a * F (mediumParameterState b endTime p a)) :=
    ((dampedMediumParameterDensity_measurable C b endTime).comp hpair).mul
      (hF.comp ((mediumParameterState_measurable b endTime).comp hpair))
  rw [markedEventMeasure,lintegral_prod _ hm.aemeasurable,lintegral_fintype]
  simp only [Measure.count_singleton,mul_one]
  simp_rw [damped_medium_parameter_integral C b endTime p _ hT hF]
  rw [← lintegral_finsetSum]
  · apply lintegral_congr
    intro s
    rw [← Finset.mul_sum,dampedMediumCollision_lintegral C b _
      (F := fun v => F (p.1-s,((mediumPoint endTime p s).2,v)))
      (hF.comp (by fun_prop))]
    rfl
  · intro m _
    have hrate : Measurable (fun s : ℝ =>
        (mediumMarkedRate b m (mediumPoint endTime p s,p.2.2)+holdingWeight C m)) :=
      ((mediumMarkedRate_measurable b m).comp (show Measurable (fun s : ℝ => (mediumPoint endTime p s,p.2.2)) by unfold mediumPoint; fun_prop)).add measurable_const
    have hi : Measurable (fun a : EventParameter =>
        F (mediumParameterState b endTime p (m,a))) :=
      hF.comp ((mediumParameterState_measurable b endTime).comp
        (show Measurable (fun a : EventParameter => (p,(m,a))) by fun_prop))
    exact (show Measurable (clockSurvival C) by
      unfold clockSurvival; fun_prop).mul (hrate.mul hi.lintegral_prod_right')

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite medium words whose collision velocities stay in the physical box -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedBoundedWordDensity_measurable (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (n : ℕ) :
    Measurable (fun q : PhysicalFlightState × ParameterWord n =>
      dampedBoundedWordDensity C b endTime n q.1 q.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hh : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by
      fun_prop
    have hs : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) =>
        mediumParameterState b endTime q.1 q.2.1) :=
      (mediumParameterState_measurable b endTime).comp hh
    have ht : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => q.2.2) := by
      fun_prop
    have hbox : Measurable ({q : PhysicalFlightState | ‖q.2.2‖ ≤ 6}.indicator
        (1 : PhysicalFlightState → ℝ≥0∞)) :=
      measurable_const.indicator (measurableSet_le (by fun_prop) measurable_const)
    exact ((dampedMediumParameterDensity_measurable C b endTime).comp hh).mul
      ((hbox.comp hs).mul (ih.comp (hs.prodMk ht)))

theorem dampedBoundedWordDensity_eq (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) {p : TimeFlightState} {q : PhysicalFlightState} (a : ParameterWord n)
    {δ ε : ℝ} (hbudget : δ+(n:ℝ)*ε ≤ 1)
    (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (ha : GoodReferenceWord n p a) (hb : WordNearby b endTime ε n q a) :
    dampedBoundedWordDensity C b endTime n q a = dampedMediumWordDensity C b endTime n q a := by
  induction n generalizing p q δ with
  | zero => rfl
  | succ n ih =>
    have hv' := medium_parameter_velocity_error b endTime ha.2.1 hv hb.1 hb.2.1
    have hbud' : (δ+ε)+(n:ℝ)*ε ≤ 1 := by
      push_cast at hbudget
      linarith
    have hε : 0 ≤ ε := (norm_nonneg _).trans hb.1
    have hδε : δ+ε ≤ 1 := by nlinarith
    have hnorm : ‖(mediumParameterState b endTime q a.1).2.2‖ ≤ 6 := by
      have hh := norm_add_le
        ((mediumParameterState b endTime q a.1).2.2-(markedParameterState p a.1).2.2.1)
        (markedParameterState p a.1).2.2.1
      rw [sub_add_cancel] at hh
      linarith [retainedState_norm (markedParameterState p a.1).2.2]
    change dampedMediumParameterDensity C b endTime q a.1 *
        ({q : PhysicalFlightState | ‖q.2.2‖ ≤ 6}.indicator 1
          (mediumParameterState b endTime q a.1) *
            dampedBoundedWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2) = _
    have hmem : mediumParameterState b endTime q a.1 ∈
        {q : PhysicalFlightState | ‖q.2.2‖ ≤ 6} := hnorm
    rw [indicator_of_mem hmem,Pi.one_apply,one_mul,
      ih a.2 hbud' hv' ha.2.2 hb.2.2.2.2]
    rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform smallness of the finite-history perturbation error -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedHistoryPerturbationError_continuous (Cmax : ℝ≥0) (n : ℕ) : Continuous (dampedHistoryPerturbationError Cmax n) := by
  exact (ENNReal.continuous_const_mul (wordWeightError_ne_top ENNReal.ofReal_ne_top n)).comp
    (ENNReal.continuous_ofReal.comp (by fun_prop))

theorem dampedFiniteHistoryError_continuous (Cmax : ℝ≥0) (N : ℕ) (T : ℝ) : Continuous (dampedFiniteHistoryError Cmax N T) := by
  apply continuous_finsetSum
  intro n _hn
  exact (ENNReal.continuous_mul_const (ENNReal.pow_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))).comp
      (dampedHistoryPerturbationError_continuous Cmax n)

theorem dampedFiniteHistoryError_zero (Cmax : ℝ≥0) (N : ℕ) (T : ℝ) : dampedFiniteHistoryError Cmax N T 0 = 0 := by
  simp [dampedFiniteHistoryError,dampedHistoryPerturbationError]

theorem dampedFiniteHistoryError_small (Cmax : ℝ≥0) (N : ℕ) (T : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Icc 0 ε₀, dampedFiniteHistoryError Cmax N T ε < 1 := by
  have hh : ∀ᶠ ε in 𝓝 (0 : ℝ), dampedFiniteHistoryError Cmax N T ε < 1 :=
    (dampedFiniteHistoryError_continuous Cmax N T).continuousAt.eventually
      (gt_mem_nhds (by rw [dampedFiniteHistoryError_zero]; norm_num))
  obtain ⟨r,hr,hsmall⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨r/2,by positivity,fun ε hε => hsmall ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hε.1]
  exact hε.2.trans_lt (half_lt_self hr)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedBranchingBlocks
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # The event kernel with all intermediate velocities in the physical box -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

instance dampedBoundedEventKernel_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) :
    IsSFiniteKernel (dampedBoundedEventKernel C b endTime T) := by
  unfold dampedBoundedEventKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem dampedBoundedEventKernel_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂dampedBoundedEventKernel C b endTime T p) =
      ∫⁻ a, dampedMediumParameterDensity C b endTime p a *
        (mediumVelocityBox.indicator 1 (mediumParameterState b endTime p a) *
          F (mediumParameterState b endTime p a)) ∂markedEventMeasure T := by
  rw [dampedBoundedEventKernel,Kernel.lintegral_restrict,
    ← lintegral_indicator mediumVelocityBox_measurable,
    dampedMediumEventKernel_lintegral C b endTime T p (hF.indicator mediumVelocityBox_measurable)]
  apply lintegral_congr
  intro a
  by_cases ha : mediumParameterState b endTime p a ∈ mediumVelocityBox
  · simp [ha]
  · simp [ha]

instance dampedBoundedEventKernel_pow_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    IsSFiniteKernel ((dampedBoundedEventKernel C b endTime T)^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [show (dampedBoundedEventKernel C b endTime T)^(n+1) =
        ((dampedBoundedEventKernel C b endTime T)^n) ∘ₖ dampedBoundedEventKernel C b endTime T by
      simpa only [pow_one] using Kernel.pow_add (dampedBoundedEventKernel C b endTime T) n 1]
    let _ := ih
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem dampedBoundedWord_integral (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) (n : ℕ) (p : PhysicalFlightState) :
    (∫⁻ a, dampedBoundedWordDensity C b endTime n p a * F (mediumWordState b endTime n p a)
      ∂parameterWordMeasure T n) = ∫⁻ q, F q ∂((dampedBoundedEventKernel C b endTime T)^n) p := by
  induction n generalizing p with
  | zero =>
    change (∫⁻ _a : PUnit, 1*F p ∂Measure.dirac PUnit.unit) = ∫⁻ q, F q ∂Kernel.id p
    simp [Kernel.id_apply,lintegral_dirac' _ hF]
  | succ n ih =>
    have hmap : Measurable (fun a : ParameterWord (n+1) => (p,a)) :=
      measurable_const.prodMk measurable_id
    have hd : Measurable (fun a : ParameterWord (n+1) => dampedBoundedWordDensity C b endTime (n+1) p a) :=
      (dampedBoundedWordDensity_measurable C b endTime (n+1)).comp hmap
    have hs : Measurable (fun a : ParameterWord (n+1) => mediumWordState b endTime (n+1) p a) :=
      (mediumWordState_measurable b endTime (n+1)).comp hmap
    have hm : Measurable (fun a : ParameterWord (n+1) =>
        dampedBoundedWordDensity C b endTime (n+1) p a * F (mediumWordState b endTime (n+1) p a)) :=
      hd.mul (hF.comp hs)
    rw [parameterWordMeasure,lintegral_prod _ hm.aemeasurable]
    rw [show (dampedBoundedEventKernel C b endTime T)^(n+1) =
        ((dampedBoundedEventKernel C b endTime T)^n) ∘ₖ dampedBoundedEventKernel C b endTime T by
      simpa only [pow_one] using Kernel.pow_add (dampedBoundedEventKernel C b endTime T) n 1,
      Kernel.lintegral_comp _ _ _ hF,
      dampedBoundedEventKernel_lintegral C b endTime T p
        (hF.lintegral_kernel (κ := (dampedBoundedEventKernel C b endTime T)^n))]
    apply lintegral_congr
    intro a
    change (∫⁻ w, (dampedMediumParameterDensity C b endTime p a *
        (mediumVelocityBox.indicator 1 (mediumParameterState b endTime p a) *
          dampedBoundedWordDensity C b endTime n (mediumParameterState b endTime p a) w)) *
        F (mediumWordState b endTime n (mediumParameterState b endTime p a) w)
          ∂parameterWordMeasure T n) = _
    have hb : mediumVelocityBox.indicator (1 : PhysicalFlightState → ℝ≥0∞)
        (mediumParameterState b endTime p a) ≠ ⊤ := by
      by_cases ha : mediumParameterState b endTime p a ∈ mediumVelocityBox <;> simp [ha]
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (dampedMediumParameterDensity_ne_top C b endTime p a),
      lintegral_const_mul' _ _ hb,ih]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lower transfer of reference blocks with every velocity kept bounded -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_bounded_word_integrand_bound {C Cmax : ℝ≥0} (hC : referenceClock ≤ C)
    (hCmax : C ≤ Cmax) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (a : ParameterWord n) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hp : 0 ≤ p.1) (hv : (n:ℝ)*ε ≤ 1)
    (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (hnear : GoodReferenceWord n p a → WordNearby b endTime ε n (embedFlightState p) a) :
    dampedWordDensity C n p a * flightSeed C
        ((blockTarget p.2.1 p.1 κ d).indicator 1) (parameterWordState n p a) ≤
      dampedBoundedBlockIntegrand C b endTime p κ d n a+dampedHistoryPerturbationError Cmax n ε := by
  by_cases hr : dampedWordDensity C n p a = 0
  · rw [hr,zero_mul]
    exact bot_le
  have ha := goodReferenceWord_of_damped_density_ne_zero C n p a hr
  have he := dampedBoundedWordDensity_eq C b endTime n a (δ := 0)
    (by simpa using hv) (by simp [embedFlightState]) ha (hnear ha)
  unfold dampedBoundedBlockIntegrand
  rw [he]
  exact damped_medium_word_integrand_bound hC hCmax b endTime n p a hε hε1 hp hv hx hnear

theorem damped_bounded_word_integral_lower {C Cmax : ℝ≥0} (hC : referenceClock ≤ C)
    (hCmax : C ≤ Cmax) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (T : ℝ) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hp : 0 ≤ p.1) (hpT : p.1 ≤ T)
    (hv : (n:ℝ)*ε ≤ 1) (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (hnear : ∀ a, GoodReferenceWord n p a → WordNearby b endTime ε n (embedFlightState p) a) :
    eventHistory C (branchingAt C)
        (flightSeed C ((blockTarget p.2.1 p.1 κ d).indicator 1)) n p ≤
      (∫⁻ a, dampedBoundedBlockIntegrand C b endTime p κ d n a ∂parameterWordMeasure T n)+
        dampedHistoryPerturbationError Cmax n ε*(3*ENNReal.ofReal T)^n := by
  have hf : Measurable ((blockTarget p.2.1 p.1 κ d).indicator (1 : FlightState → ℝ≥0∞)) :=
    measurable_const.indicator (blockTarget_measurable _ _ _ _)
  rw [← dampedWord_integral C (flightSeed_measurable C hf) T n p ⟨hp,hpT⟩]
  calc
    _ ≤ ∫⁻ a, dampedBoundedBlockIntegrand C b endTime p κ d n a+dampedHistoryPerturbationError Cmax n ε
        ∂parameterWordMeasure T n :=
      lintegral_mono (fun a => damped_bounded_word_integrand_bound hC hCmax b endTime n p a
        hε hε1 hp hv hx (hnear a))
    _ = _ := by rw [lintegral_add_right _ measurable_const,lintegral_const,parameterWordMeasure_mass]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniformly positive finite branching blocks in a nearby measurable medium -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_bounded_finite_history_block_transfer (Cmax : ℝ≥0) (N : ℕ) (T : ℝ) {κ d : ℝ}
    (hκ : 0 < κ) (hd : 0 < d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc 0 T, ∀ z : FlightState,
      (7 : ℝ≥0∞) < (∑ n ∈ Finset.range N, eventHistory C (branchingAt C)
        (flightSeed C ((blockTarget z.1 A κ d).indicator 1)) n (A,z)) →
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ n < N, ∀ a : ParameterWord n, GoodReferenceWord n (A,z) a →
        WordNearby b endTime ε n (embedFlightState (A,z)) a) →
      (6 : ℝ≥0∞) < dampedBoundedBlockMass C b endTime T (A,z) κ d N := by
  obtain ⟨r,hr,hrsmall⟩ := dampedFiniteHistoryError_small Cmax N T
  let L : ℝ := (N:ℝ)+1
  have hL : 0 < L := by dsimp [L] <;> positivity
  let ε₀ := min (1/4:ℝ) (min (1/L) (min ((d*κ/8)/L) r))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    simp only [lt_min_iff]
    exact ⟨by norm_num,one_div_pos.mpr hL,by positivity,hr⟩
  refine ⟨ε₀,hε₀,?_⟩
  intro C hC hCmax ε hε A hA z href b endTime hnear
  have hcut : ε ≤ min (1/4:ℝ) (min (1/L) (min ((d*κ/8)/L) r)) := hε.2
  have hquarter := hcut.trans (min_le_left _ _)
  have htail := hcut.trans (min_le_right _ _)
  have hεL := htail.trans (min_le_left _ _)
  have htail' := htail.trans (min_le_right _ _)
  have hεd := htail'.trans (min_le_left _ _)
  have hεr := htail'.trans (min_le_right _ _)
  have hmass := hrsmall ε ⟨hε.1,hεr⟩
  have hsum : (∑ n ∈ Finset.range N, eventHistory C (branchingAt C)
      (flightSeed C ((blockTarget z.1 A κ d).indicator 1)) n (A,z)) ≤
      dampedBoundedBlockMass C b endTime T (A,z) κ d N+dampedFiniteHistoryError Cmax N T ε := by
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          ((∫⁻ a, dampedBoundedBlockIntegrand C b endTime (A,z) κ d n a ∂parameterWordMeasure T n)+
            dampedHistoryPerturbationError Cmax n ε*(3*ENNReal.ofReal T)^n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN := (Finset.mem_range.mp hn).le
        have hnL : (n:ℝ) ≤ L :=
          (Nat.cast_le.mpr hnN).trans (le_add_of_nonneg_right (by norm_num))
        have hv : (n:ℝ)*ε ≤ 1 :=
          (mul_le_mul_of_nonneg_right hnL hε.1).trans
            (by simpa only [mul_comm] using (le_div_iff₀ hL).mp hεL)
        have hx' : (n:ℝ)*ε ≤ d*κ/8 :=
          (mul_le_mul_of_nonneg_right hnL hε.1).trans
            (by simpa only [mul_comm] using (le_div_iff₀ hL).mp hεd)
        have hx : 2*A*((n:ℝ)*ε) ≤ d*κ*A/4 := by
          convert mul_le_mul_of_nonneg_left hx' (show 0 ≤ (2:ℝ)*A from mul_nonneg (by norm_num) hA.1) using 1
          all_goals try with_reducible_and_instances rfl
          ring
        exact damped_bounded_word_integral_lower hC hCmax b endTime n (A,z) T hε.1 hquarter hA.1 hA.2
          hv hx (hnear n (Finset.mem_range.mp hn))
      _ = _ := by rw [Finset.sum_add_distrib]; rfl
  by_contra hbad
  have hupper := hsum.trans (add_le_add (le_of_not_gt hbad) hmass.le)
  norm_num at hupper
  exact (not_lt_of_ge hupper) href

theorem uniform_damped_bounded_block_growth {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Cmax : ℝ≥0, ∃ N : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ n < N, ∀ a : ParameterWord n, GoodReferenceWord n (A,z) a →
        WordNearby b endTime ε n (embedFlightState (A,z)) a) →
      (6 : ℝ≥0∞) < dampedBoundedBlockMass C b endTime T (A,z) κ d N := by
  obtain ⟨A₀,hA₀,hdepth⟩ := uniform_damped_finite_block_growth_q80 hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT Cmax
  obtain ⟨N,hN⟩ := hdepth T hT Cmax
  obtain ⟨ε₀,hε₀,htransfer⟩ := damped_bounded_finite_history_block_transfer Cmax N T hκ hd
  refine ⟨N,ε₀,hε₀,?_⟩
  intro C hC hCmax ε hε A hA z b endTime hnear
  exact htransfer C hC hCmax ε hε A ⟨hA₀.le.trans hA.1,hA.2⟩ z (hN C hC hCmax A hA z) b endTime hnear

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Endpoint measures for the bounded physical collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumFlightSeed_measurable (C : ℝ≥0) {f : V × V → ℝ≥0∞}
    (hf : Measurable f) : Measurable (dampedMediumFlightSeed C f) :=
  (show Measurable (fun p : PhysicalFlightState => clockSurvival C p.1) by
    unfold clockSurvival; fun_prop).mul (hf.comp finishMediumFlight_measurable)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BackgroundBeamCloseness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The selected mesh scale stays close to the center of a small transverse window -/

noncomputable section

namespace BoltzmannNonuniqueness.GeometricBackground

theorem scale_ratio_error {r ρ μ δ h : ℝ} (_hr : 0 < r) (hμ : 0 < μ)
    (hδ : 0 ≤ δ) (hδ1 : δ < 1) (hh : 0 ≤ h)
    (hwindow : |ρ-r| ≤ δ*r) (hlo : μ ≤ ρ) (hhi : ρ ≤ (1+h)*μ) :
    |r/μ-1| ≤ (h+δ)/(1-δ) := by
  have hw := abs_le.mp hwindow
  have hd : 0 < 1-δ := sub_pos.mpr hδ1
  have hp : 0 < 1+δ := by positivity
  have hlow : 1/(1+δ) ≤ r/μ := (div_le_div_iff₀ hp hμ).mpr (by nlinarith)
  have hone : 1-δ ≤ 1/(1+δ) := (le_div_iff₀ hp).mpr (by nlinarith [sq_nonneg δ])
  have hupp : r/μ ≤ (1+h)/(1-δ) := (div_le_div_iff₀ hμ hd).mpr (by nlinarith)
  have he : (1+h)/(1-δ)-1 = (h+δ)/(1-δ) := by field_simp <;> ring
  have hQ : δ ≤ (h+δ)/(1-δ) := (le_div_iff₀ hd).mpr (by nlinarith [sq_nonneg δ])
  apply abs_le.mpr
  constructor
  · linarith
  · linarith

theorem selected_scale_ratio_error {θ η r δ : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hr : 0 < r) (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (y : VelocityWeight.Transverse) (hy : 0 < ‖y‖) (hwindow : |‖y‖-r| ≤ δ*r) :
    |r/scale θ η y-1| ≤ (Real.exp η-1+δ)/(1-δ) := by
  have hb := GeometricMesh.cell_bounds hθ hη hy
  apply scale_ratio_error hr (scale_pos hθ η y) hδ hδ1
    (sub_nonneg.mpr (Real.one_le_exp hη.le)) hwindow hb.1
  simpa only [scale,add_sub_cancel] using hb.2.le

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Quantitative closeness of the actual compressed beam density -/

noncomputable section

open Set
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialBackground

theorem axial_weight_close_to_one {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x| ≤ δ → 1-S x ≤ ε := by
  have hcont : ContinuousAt S 0 := continuous_S.continuousAt
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hcont ε hε
  refine ⟨δ/2,by positivity,fun x hx => ?_⟩
  have hdist : dist x 0 < δ := by
    simpa only [Real.dist_eq,sub_zero] using hx.trans_lt (half_lt_self hδ)
  have hh := hclose hdist
  have hzero : S 0 = 1 := by simp [S]
  rw [hzero,Real.dist_eq] at hh
  have hlow := (abs_lt.mp hh).1
  linarith

theorem beam_argument_bound {r μ α γ t C σ z : ℝ} (_hr : 0 < r) (hμ : 0 < μ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (htC : t ≤ C*r) (hzC : |z| ≤ C*r) (hR : r/μ ≤ 2) (hσ : |σ| = 1) :
    |γ*AxialFlow.foot σ α γ μ t z/μ| ≤ 6*C*γ ∧ t*α*γ/μ ≤ 2*C*γ := by
  have hrμ : r ≤ 2*μ := (div_le_iff₀ hμ).mp hR
  have hf := foot_abs_bound hα ht σ γ μ z
  rw [hσ] at hf
  have hfoot : |AxialFlow.foot σ α γ μ t z| ≤ 3*C*r := by
    have htα : t*(1+α) ≤ 2*t := by nlinarith
    linarith
  constructor
  · rw [abs_div,abs_mul,abs_of_nonneg hγ,abs_of_pos hμ]
    apply (div_le_iff₀ hμ).mpr
    calc
      γ*|AxialFlow.foot σ α γ μ t z| ≤ γ*(3*C*r) := mul_le_mul_of_nonneg_left hfoot hγ
      _ ≤ γ*(3*C*(2*μ)) := by gcongr
      _ = _ := by ring
  · apply (div_le_iff₀ hμ).mpr
    have hta : t*α ≤ t := mul_le_of_le_one_right ht hα1
    calc
      t*α*γ ≤ t*γ := mul_le_mul_of_nonneg_right hta hγ
      _ ≤ (C*r)*γ := mul_le_mul_of_nonneg_right htC hγ
      _ ≤ (C*(2*μ))*γ := by gcongr
      _ = _ := by ring

theorem relativeWeight_close {r μ α γ t ε : ℝ} (hr : 0 ≤ r) (hμ : 0 < μ)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ht : 0 ≤ t) (_hε : 0 ≤ ε)
    (hR : r/μ ≤ 2) (hmesh : |r/μ-1| ≤ ε/5) (σ z : ℝ)
    (hS : 1-S (γ*AxialFlow.foot σ α γ μ t z/μ) ≤ ε/5)
    (hc : t*α*γ/μ ≤ ε/5) : |relativeWeight r α γ μ t σ z-1| ≤ ε := by
  have hh := relativeWeight_error hr hμ hα hγ ht σ z
  have hs0 : 0 ≤ 1-S (γ*AxialFlow.foot σ α γ μ t z/μ) := sub_nonneg.mpr (S_le_one _)
  have hc0 : 0 ≤ t*α*γ/μ := by positivity
  have hbound : (r/μ)*(1-S (γ*AxialFlow.foot σ α γ μ t z/μ)+t*α*γ/μ) ≤
      2*(ε/5+ε/5) := mul_le_mul hR (add_le_add hS hc) (add_nonneg hs0 hc0) (by norm_num)
  linarith

end BoltzmannNonuniqueness.AxialBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricDampedRetention
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform local closeness of the selected geometric cold beams -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem join_zero_axis (z : ℝ) : PlaneChart.join 0 z = z • ReferenceGeometry.beamAxis := by
  apply split.injective
  rw [show split (PlaneChart.join 0 z) = (z,0) from split.apply_symm_apply (z,0),split_apply]
  apply Prod.ext
  · simp [axial,ReferenceGeometry.beamAxis]
  · apply (WithLp.ext_iff 2).mpr
    funext i
    fin_cases i <;> simp [transverse,ReferenceGeometry.beamAxis]

theorem beamVelocity_error {α : ℝ} (hα : 0 ≤ α) (θ η γ σ : ℝ) (p : ℝ × Velocity) :
    ‖beamVelocity θ η α γ σ p-σ • ReferenceGeometry.beamAxis‖ ≤ α := by
  unfold beamVelocity
  rw [join_zero_axis,← sub_smul,norm_smul,Real.norm_eq_abs,ReferenceGeometry.axis_norms.2.2,mul_one]
  exact AxialFlow.velocity_sub_center_le hα

theorem selected_scale_error_small {θ η r ε : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hηsmall : η ≤ Real.log (1+ε/20)) (hr : 0 < r)
    (y : Transverse) (hy : 0 < ‖y‖) (hw : |‖y‖-r| ≤ (ε/20)*r) :
    |r/scale θ η y-1| ≤ ε/5 := by
  have hδ : 0 ≤ ε/20 := by positivity
  have hδ1 : ε/20 < 1 := by linarith
  have hscale := selected_scale_ratio_error hθ hη hr hδ hδ1 y hy hw
  have he : Real.exp η-1 ≤ ε/20 := by
    have hh := Real.exp_le_exp.mpr hηsmall
    rw [Real.exp_log (by positivity : 0 < 1+ε/20)] at hh
    linarith
  apply hscale.trans
  apply (div_le_iff₀ (sub_pos.mpr hδ1)).mpr
  nlinarith

theorem beam_density_tolerance {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 0 < C) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ {θ η r α γ t : ℝ},
      0 < θ → 0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      0 ≤ α → α ≤ 1 → 0 ≤ γ → γ ≤ γ₀ → 0 ≤ t → t ≤ C*r →
      ∀ x : Velocity, 0 < ‖transverse x‖ →
      |‖transverse x‖-r| ≤ (ε/20)*r → |axial x| ≤ C*r →
      ∀ σ : ℝ, |σ| = 1 → |beamDensity θ η α γ r σ (t,x)-1| ≤ ε := by
  obtain ⟨δ,hδ,hS⟩ := AxialBackground.axial_weight_close_to_one (div_pos hε (by norm_num : (0:ℝ)<5))
  let γ₀ := min (δ/(6*C)) ((ε/5)/(2*C))
  have hγ₀ : 0 < γ₀ := lt_min (by positivity) (by positivity)
  refine ⟨γ₀,hγ₀,?_⟩
  intro θ η r α γ t hθ hη hηsmall hr hα hα1 hγ hγsmall ht htC x hx hwindow hz σ hσ
  have hmesh := selected_scale_error_small hθ hη hε hε1 hηsmall hr (transverse x) hx hwindow
  have hR : r/scale θ η (transverse x) ≤ 2 := by
    have hh := (abs_le.mp hmesh).2
    linarith
  have hb := AxialBackground.beam_argument_bound hr (scale_pos hθ η _) hα hα1 hγ ht hC.le
    htC hz hR hσ
  have hg1 : 6*C*γ ≤ δ := by
    have hh := (le_div_iff₀ (by positivity : 0 < 6*C)).mp
      (hγsmall.trans (min_le_left _ _))
    nlinarith
  have hg2 : 2*C*γ ≤ ε/5 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*C)).mp
      (hγsmall.trans (min_le_right _ _))
    nlinarith
  rw [beamDensity_eq_relative hθ hα hγ hr η σ (t,x) ht]
  exact AxialBackground.relativeWeight_close hr.le (scale_pos hθ η _) hα hγ ht hε.le
    hR hmesh σ (axial x) (hS _ (hb.1.trans hg1)) (hb.2.trans hg2)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The normalized holding term is the actual geometric loss complement -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumCollision_eq_nonzero_marks {D : ℝ≥0} (hD : referenceClock ≤ D)
    (b : BeamCoefficients) (z : MediumState)
    (hf : mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
      (b.plusDensity z.1) (b.minusDensity z.1) ≤ (referenceClock:ℝ)) :
    dampedMediumCollision D b z = mediumMarkedKernel b 1 z+mediumMarkedKernel b 2 z+
      ENNReal.ofReal ((D:ℝ)-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
        (b.plusDensity z.1) (b.minusDensity z.1)) • Measure.dirac z.2 := by
  rw [dampedMediumCollision_projection hD b z hf,
    mediumMarkedKernel_apply,mediumMarkedKernel_apply]
  simp only [mediumMarkedRate,markedRate,markedChildKernel,Fin.isValue,one_ne_zero,
    show (2 : HistoryMark) ≠ 0 by decide,show (2 : HistoryMark) ≠ 1 by decide,
    ↓reduceIte,Kernel.comap_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LargeOutput
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform decay of the normalized kernel at large output velocity -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.SheetMeasures
open BoltzmannNonuniqueness.ChartKernel
open BoltzmannNonuniqueness.UniformGain
open BoltzmannNonuniqueness.LargeOutputSlices

namespace BoltzmannNonuniqueness.LargeOutput

theorem transverse_norm_le (v : Velocity) : ‖transverse v‖ ≤ ‖v‖ := by
  have h := norm_sq_split v
  nlinarith [sq_nonneg (axial v), norm_nonneg (transverse v), norm_nonneg v]

end BoltzmannNonuniqueness.LargeOutput

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SmallFirstGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A uniform small-input bound for small transverse incoming velocities -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.SheetGain
open BoltzmannNonuniqueness.SlopedChart
open BoltzmannNonuniqueness.AffineSlices

namespace BoltzmannNonuniqueness.SmallInputGeometry

theorem abs_axial_le_norm (v : Velocity) : |axial v| ≤ ‖v‖ := by
  have h := norm_sq_split v
  nlinarith [sq_abs (axial v), sq_nonneg ‖transverse v‖, abs_nonneg (axial v), norm_nonneg v]

end BoltzmannNonuniqueness.SmallInputGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LateBoxAccessMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The expanding boxes used in the finite-horizon growth contradiction -/

noncomputable section

open Set Metric

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lateBox_measurable (κ d t : ℝ) : MeasurableSet (lateBox κ d t) := by
  unfold lateBox
  measurability

theorem physicalBlockTarget_subset_lateBox {κ d t Δ : ℝ} {p q : V × V}
    (hp : p ∈ lateBox κ d t) (hq : q ∈ physicalBlockTarget p.1 Δ κ d) :
    q ∈ lateBox κ d (t+Δ) := by
  refine ⟨?_,hq.2⟩
  have he : q.1-(κ*(t+Δ)) • firstAxis =
      (q.1-(p.1+(κ*Δ) • firstAxis))+(p.1-(κ*t) • firstAxis) := by module
  rw [he]
  have hh := norm_add_le (q.1-(p.1+(κ*Δ) • firstAxis)) (p.1-(κ*t) • firstAxis)
  have hb := add_lt_add hq.1 hp.1
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform cold-density scales on the expanding transverse boxes -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lateBox_radius_bounds {κ d t : ℝ} (hκ : 0 < κ) (ht : 0 < t)
    {p : V × V} (hp : p ∈ lateBox κ d t) :
    (1-d)*κ*t < ‖transverse p.1‖ ∧ ‖transverse p.1‖ < (1+d)*κ*t ∧
      |axial p.1| < d*κ*t := by
  let c : V := (κ*t) • firstAxis
  have hcax : axial c = 0 := by
    simp [c,axial,firstAxis,EuclideanSpace.single]
  have hcnorm : ‖c‖ = κ*t := by
    simp [c,norm_smul,axis_norms.1,Real.norm_eq_abs,abs_of_pos hκ,abs_of_pos ht]
  have hctn : ‖transverse c‖ = κ*t := by
    have hh := norm_sq_split c
    rw [hcnorm,hcax] at hh
    nlinarith [norm_nonneg (transverse c),mul_pos hκ ht]
  have he : ‖transverse p.1-transverse c‖ < d*κ*t := by
    rw [← PlaneChart.transverse_sub]
    exact (LargeOutput.transverse_norm_le _).trans_lt hp.1
  have hlo := norm_sub_norm_le (transverse c) (transverse p.1)
  have hhi := norm_sub_norm_le (transverse p.1) (transverse c)
  rw [norm_sub_rev] at hlo
  have ha := (SmallInputGeometry.abs_axial_le_norm (p.1-c)).trans_lt hp.1
  rw [PlaneChart.axial_sub,hcax,sub_zero] at ha
  exact ⟨by rw [hctn] at hlo; nlinarith,
    by rw [hctn] at hhi; nlinarith,ha⟩

theorem lateBox_geometric_scale {κ d t : ℝ} (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hd : d ≤ 1/2) (ht : 0 < t) {p : V × V} (hp : p ∈ lateBox κ d t) :
    0 < ‖transverse p.1‖ ∧ t ≤ (4/κ)*‖transverse p.1‖/2 ∧
      |axial p.1| ≤ (4/κ)*‖transverse p.1‖/2 := by
  obtain ⟨hlo,hhi,hax⟩ := lateBox_radius_bounds hκ ht hp
  have hhalf : κ*t/2 < ‖transverse p.1‖ := by
    have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ ht).le
    nlinarith
  have hr : 0 < ‖transverse p.1‖ := lt_trans (by positivity) hhalf
  have he : (4/κ)*‖transverse p.1‖/2 = 2*‖transverse p.1‖/κ := by ring
  have htime : t ≤ 2*‖transverse p.1‖/κ :=
    (le_div_iff₀ hκ).mpr (by nlinarith)
  have haxr : |axial p.1| ≤ ‖transverse p.1‖ := by
    have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ ht).le
    nlinarith
  have hrr : ‖transverse p.1‖ ≤ 2*‖transverse p.1‖/κ := by
    apply (le_div_iff₀ hκ).mpr
    nlinarith [mul_le_mul_of_nonneg_right hκ₁ hr.le]
  refine ⟨hr,?_,?_⟩
  · simpa only [he] using htime
  · simpa only [he] using haxr.trans hrr

theorem lateBox_block_duration {κ d t K A₀ : ℝ} (hκ : 0 < κ) (ht : 0 < t)
    (hd : d ≤ 1/2) (hK : 0 < K) (hA₀ : 0 < A₀)
    {p : V × V} (hp : p ∈ lateBox κ d t) :
    (K/(4*‖transverse p.1‖)) * ((8*κ*A₀/K)*t) ∈ Icc A₀ (4*A₀) := by
  obtain ⟨hlo,hhi,_⟩ := lateBox_radius_bounds hκ ht hp
  have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ ht).le
  have hr : 0 < ‖transverse p.1‖ := by nlinarith
  have he : (K/(4*‖transverse p.1‖)) * ((8*κ*A₀/K)*t) =
      2*κ*A₀*t/‖transverse p.1‖ := by field_simp [hK.ne',hr.ne'] <;> ring
  rw [he]
  constructor
  · apply (le_div_iff₀ hr).mpr
    have hru : ‖transverse p.1‖ ≤ 2*κ*t := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hru hA₀.le]
  · apply (div_le_iff₀ hr).mpr
    have hrl : κ*t ≤ 2*‖transverse p.1‖ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hrl (show 0 ≤ 2*A₀ by positivity)]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WindowLocalizedSource
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A single physical damping rate for all starts in a short time window -/

noncomputable section
open Set
open scoped NNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem window_damping_range {κ d b W s : ℝ}
    (hκ : 0 < κ) (hκsmall : κ ≤ 1) (hb : 0 < b) (hW : W ≤ κ*b/200)
    (hs : s ∈ Icc b (b+W)) (hd : d ≤ 1/2) {p : V × V} (hp : p ∈ lateBox κ d s) :
    (referenceClock:ℝ) ≤ 192*Real.pi*‖transverse p.1‖/(κ*b) ∧
      192*Real.pi*‖transverse p.1‖/(κ*b) ≤ 12*(referenceClock:ℝ) := by
  have hspos := hb.trans_le hs.1
  obtain ⟨hlo,hhi,_⟩ := lateBox_radius_bounds hκ hspos hp
  have hd' := mul_le_mul_of_nonneg_right hd (mul_pos hκ hspos).le
  have hkb : κ*b ≤ b := by nlinarith [mul_le_mul_of_nonneg_right hκsmall hb.le]
  have hst : s ≤ 2*b := by linarith [hs.2]
  have hrlo : κ*b/2 ≤ ‖transverse p.1‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hs.1 hκ.le]
  have hrhi : ‖transverse p.1‖ ≤ 3*(κ*b) := by
    nlinarith [mul_le_mul_of_nonneg_left hst hκ.le]
  constructor
  · apply (le_div_iff₀ (mul_pos hκ hb)).mpr
    change 48*Real.pi*(κ*b) ≤ 192*Real.pi*‖transverse p.1‖
    nlinarith [mul_le_mul_of_nonneg_left hrlo (show 0 ≤ 192*Real.pi by positivity),
      mul_pos Real.pi_pos (mul_pos hκ hb)]
  · apply (div_le_iff₀ (mul_pos hκ hb)).mpr
    change 192*Real.pi*‖transverse p.1‖ ≤ 12*(48*Real.pi)*(κ*b)
    nlinarith [mul_le_mul_of_nonneg_left hrhi (show 0 ≤ 192*Real.pi by positivity)]

theorem window_damping_normalization {κ b K r : ℝ}
    (hκ : 0 < κ) (hb : 0 < b) (hr : 0 < r) :
    (K/(4*r))*(192*Real.pi*r/(κ*b)) = 48*Real.pi*K/(κ*b) := by
  field_simp
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalEvolution
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Damped free waiting in physical flight coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalAdvance_measurable :
    Measurable (fun q : PhysicalFlightState × ℝ => physicalAdvance q.1 q.2) := by
  unfold physicalAdvance
  fun_prop

theorem physicalWaitingWeight_measurable (C : ℝ≥0) : Measurable (physicalWaitingWeight C) := by
  unfold physicalWaitingWeight
  exact (show Measurable (fun q : PhysicalFlightState × ℝ => clockSurvival C q.2) by
    unfold clockSurvival; fun_prop).indicator
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst.fst))

theorem physicalWaitingKernel_lintegral (C : ℝ≥0) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalWaitingKernel C p) =
      ∫⁻ s in Ioc 0 p.1, clockSurvival C s * F (physicalAdvance p s) := by
  have hc : Measurable (fun q : PhysicalFlightState × ℝ => F (physicalAdvance q.1 q.2)) :=
    hF.comp physicalAdvance_measurable
  have hd : Measurable (Function.uncurry
      (fun (_ : PhysicalFlightState) q => physicalWaitingWeight C q)) :=
    (physicalWaitingWeight_measurable C).comp measurable_snd
  rw [physicalWaitingKernel,Kernel.lintegral_map _ physicalAdvance_measurable p hF,
    Kernel.lintegral_withDensity _ hd p hc]
  have hi : Measurable (fun q : PhysicalFlightState × ℝ =>
      physicalWaitingWeight C q*F (physicalAdvance q.1 q.2)) :=
    (physicalWaitingWeight_measurable C).mul hc
  rw [Kernel.lintegral_id_prod hi]
  change (∫⁻ s, physicalWaitingWeight C (p,s)*F (physicalAdvance p s)) = _
  rw [← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro s
  by_cases hs : s ∈ Ioc 0 p.1
  · simp [physicalWaitingWeight,hs,hs.1,hs.2]
  · simp [physicalWaitingWeight,hs,show ¬(0 < s ∧ s≤p.1) from hs]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # One marked physical collision after waiting with a prescribed damping rate -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalMarkedCollision_velocity_integral (b : BeamCoefficients) (endTime : ℝ)
    (m : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedCollision b endTime m p) =
      ∫⁻ v, F (p.1,(p.2.1,v))
        ∂mediumMarkedKernel b m ((endTime-p.1,p.2.1),p.2.2) := by
  have hm : Measurable (fun q : PhysicalFlightState × V => (q.1.1,(q.1.2.1,q.2))) := by
    fun_prop
  have hc : Measurable (fun q : PhysicalFlightState × V => F (q.1.1,(q.1.2.1,q.2))) :=
    hF.comp hm
  rw [physicalMarkedCollision,Kernel.lintegral_map _ hm p hF]
  exact Kernel.lintegral_id_prod hc _ p

theorem physicalMarkedCollision_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (m : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedCollision b endTime m p) =
      mediumMarkedRate b m ((endTime-p.1,p.2.1),p.2.2)*
        ∫⁻ n : Sphere, F (p.1,(p.2.1,markedChild m p.2.2
          (b.plusPartner (endTime-p.1,p.2.1)) (b.minusPartner (endTime-p.1,p.2.1)) n.1))
          ∂sphereProbability := by
  rw [physicalMarkedCollision_velocity_integral b endTime m p hF]
  exact mediumMarkedKernel_lintegral b m _ (hF.comp (by fun_prop))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Gain-only physical histories with a chosen damping constant -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalBeamCollision_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) (F : PhysicalFlightState → ℝ≥0∞) :
    (∫⁻ q, F q ∂physicalBeamCollision b endTime p) =
      (∫⁻ q, F q ∂physicalMarkedCollision b endTime 1 p)+
      (∫⁻ q, F q ∂physicalMarkedCollision b endTime 2 p) := by
  change (∫⁻ q, F q ∂(physicalMarkedCollision b endTime 1 p+
    physicalMarkedCollision b endTime 2 p)) = _
  exact lintegral_add_measure _ _ _

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Damped endpoints of the gain-only physical collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

instance physicalGainEndpoint_sFinite (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) : IsSFiniteKernel (physicalGainEndpoint b endTime C n) := by
  have : IsSFiniteKernel (Kernel.withDensity ((physicalBeamEvent b endTime C)^n)
      (fun _ p => clockSurvival C p.1)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  unfold physicalGainEndpoint
  first | exact Measure.isProbabilityMeasure_map (by first | (apply Measurable.aemeasurable; apply finishMediumFlight_measurable <;> assumption)) | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedEndpointHistories
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Each marked event is damped free waiting followed by physical collision -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumEventKernel_eq_comp (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    dampedMediumEventKernel C b endTime T p =
      (dampedMediumStateCollision C b endTime ∘ₖ physicalWaitingKernel C) p := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [dampedMediumEventKernel_physical_lintegral C b endTime p hT hF,
    Kernel.lintegral_comp _ _ _ hF,
    physicalWaitingKernel_lintegral C p hF.lintegral_kernel]
  apply lintegral_congr
  intro s
  rw [dampedMediumStateCollision_lintegral C b endTime _ hF]
  simp only [physicalAdvance,mediumPoint]
  rw [show endTime-(p.1-s) = endTime-p.1+s by ring]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite marked histories are iterated physical waiting and collision -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_mediumEventKernel_remaining_le (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ∀ᵐ q ∂dampedMediumEventKernel C b endTime T p, q.1 ≤ p.1 := by
  rw [ae_iff]
  let A : Set PhysicalFlightState := {q | ¬q.1 ≤ p.1}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  change dampedMediumEventKernel C b endTime T p A = 0
  rw [← lintegral_indicator_one hA,
    dampedMediumEventKernel_physical_lintegral C b endTime p hT
      (F := A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) (measurable_const.indicator hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hsp : p.1-s ≤ p.1 := sub_le_self _ hs.1.le
  have hz : ∀ v : V, A.indicator (1 : PhysicalFlightState → ℝ≥0∞)
      (p.1-s,((mediumPoint endTime p s).2,v)) = 0 := by
    intro v
    exact indicator_of_notMem (by simpa only [A,mem_ofPred_eq,not_not] using hsp) _
  simp only [hz,lintegral_zero,mul_zero,Pi.zero_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Fixed time-window representations of the bounded event histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_boundedMediumEventKernel_eq_physical (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    dampedBoundedEventKernel C b endTime T p = dampedBoundedPhysicalEvent C b endTime p := by
  rw [dampedBoundedEventKernel,Kernel.restrict_apply,
    dampedBoundedPhysicalEvent,Kernel.restrict_apply,dampedMediumEventKernel_eq_comp C b endTime p hT]

theorem damped_boundedMediumEventKernel_remaining_le (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ∀ᵐ q ∂dampedBoundedEventKernel C b endTime T p, q.1 ≤ p.1 := by
  rw [dampedBoundedEventKernel,Kernel.restrict_apply]
  exact ae_restrict_of_ae (damped_mediumEventKernel_remaining_le C b endTime p hT)

theorem damped_boundedMediumEventKernel_pow_eq_physical (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ((dampedBoundedEventKernel C b endTime T)^n) p = ((dampedBoundedPhysicalEvent C b endTime)^n) p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have hpow (L : Kernel PhysicalFlightState PhysicalFlightState) :
        L^(n+1) = (L^n) ∘ₖ L := by
      simpa only [pow_one] using Kernel.pow_add L n 1
    rw [hpow,hpow,Kernel.comp_apply,Kernel.comp_apply]
    calc
      (dampedBoundedEventKernel C b endTime T p).bind ((dampedBoundedEventKernel C b endTime T)^n) =
          (dampedBoundedEventKernel C b endTime T p).bind ((dampedBoundedPhysicalEvent C b endTime)^n) := by
        apply Measure.bind_congr_right
        filter_upwards [damped_boundedMediumEventKernel_remaining_le C b endTime p hT] with q hq
        exact ih q (hq.trans hT)
      _ = _ := by rw [damped_boundedMediumEventKernel_eq_physical C b endTime p hT]


end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The damped residence-time kernel along a free characteristic -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

theorem residenceWeight_measurable (C b : ℝ) : Measurable (residenceWeight C b) := by
  unfold residenceWeight
  have hm : Measurable (fun p : (ℝ × Phase) × ℝ =>
      ENNReal.ofReal (Real.exp (C*(p.1.1-p.2)))) := by fun_prop
  exact hm.indicator ((measurableSet_lt measurable_fst.fst measurable_snd).inter
    (measurableSet_le measurable_snd measurable_const))

theorem residenceKernel_lintegral (C b : ℝ) (z : ℝ × Phase)
    {f : ℝ × Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂residenceKernel C b z) =
      ∫⁻ t in Ioc z.1 b, ENNReal.ofReal (Real.exp (C*(z.1-t)))*f (t,z.2) := by
  have hm : Measurable (fun q : (ℝ × Phase) × ℝ => (q.2,q.1.2)) := by fun_prop
  have hc : Measurable (fun q : (ℝ × Phase) × ℝ => f (q.2,q.1.2)) := hf.comp hm
  have hd : Measurable (Function.uncurry (fun (_ : ℝ × Phase) q => residenceWeight C b q)) :=
    (residenceWeight_measurable C b).comp measurable_snd
  rw [residenceKernel,Kernel.lintegral_map _ hm z hf,
    Kernel.lintegral_withDensity _ hd z hc]
  have hi : Measurable (fun q : (ℝ × Phase) × ℝ =>
      residenceWeight C b q*f (q.2,q.1.2)) := (residenceWeight_measurable C b).mul hc
  rw [Kernel.lintegral_id_prod hi]
  change (∫⁻ t, residenceWeight C b (z,t)*f (t,z.2)) = _
  rw [← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ Ioc z.1 b
  · simp [residenceWeight,ht,ht.1,ht.2]
  · simp [residenceWeight,ht,show ¬(z.1<t ∧ t≤b) from ht]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Terminal phase slices of a positive source history -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

theorem phaseEndpointKernel_lintegral (C t : ℝ) (z : ℝ × Phase)
    {f : Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂phaseEndpointKernel C t z) =
      ENNReal.ofReal (Real.exp (C*(z.1-t)))*f z.2 := by
  have hm : Measurable (Function.uncurry (fun (z : ℝ × Phase) (_ : Phase) =>
      ENNReal.ofReal (Real.exp (C*(z.1-t))))) := by fun_prop
  rw [phaseEndpointKernel,Kernel.lintegral_withDensity _ hm z hf,
    Kernel.deterministic_apply,lintegral_dirac']
  exact measurable_const.mul hf

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TransportedKernelRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Coordinate transport of the finite collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem transportedKernel_lintegral (e : X ≃ᵐ Y) (K : Kernel Y Y) (x : X)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂transportedKernel e K x) = ∫⁻ y, f (e.symm y) ∂K (e x) := by
  rw [transportedKernel,Kernel.lintegral_map _ e.symm.measurable x hf,Kernel.comap_apply]

theorem transportedKernel_id (e : X ≃ᵐ Y) :
    transportedKernel e Kernel.id = Kernel.id := by
  apply Kernel.ext_fun
  intro x f hf
  have hc : Measurable (fun y => f (e.symm y)) := hf.comp e.symm.measurable
  rw [transportedKernel_lintegral e _ x hf,Kernel.id_apply,Kernel.id_apply,
    lintegral_dirac' _ hc,lintegral_dirac' _ hf]
  rw [e.symm_apply_apply]

theorem transportedKernel_compKernel (e : X ≃ᵐ Y) (K L : Kernel Y Y) :
    transportedKernel e (K ∘ₖ L) = transportedKernel e K ∘ₖ transportedKernel e L := by
  apply Kernel.ext_fun
  intro x f hf
  have hc : Measurable (fun y => f (e.symm y)) := hf.comp e.symm.measurable
  rw [transportedKernel_lintegral e _ x hf,
    Kernel.lintegral_comp _ _ _ hc,
    Kernel.lintegral_comp _ _ _ hf,
    transportedKernel_lintegral e _ x hf.lintegral_kernel]
  apply lintegral_congr
  intro y
  rw [transportedKernel_lintegral e _ _ hf,e.apply_symm_apply]

theorem transportedKernel_pow (e : X ≃ᵐ Y) (K : Kernel Y Y) (n : ℕ) :
    transportedKernel e (K^n) = (transportedKernel e K)^n := by
  induction n with
  | zero => exact transportedKernel_id e
  | succ n ih =>
    rw [show K^(n+1) = (K^n) ∘ₖ K by simpa only [pow_one] using Kernel.pow_add K n 1,
      transportedKernel_compKernel,ih]
    simpa only [pow_one] using (Kernel.pow_add (transportedKernel e K) n 1).symm

theorem transportedKernel_symm (e : X ≃ᵐ Y) (K : Kernel X X) :
    transportedKernel e (transportedKernel e.symm K) = K := by
  apply Kernel.ext_fun
  intro x f hf
  have hc : Measurable (fun y => f (e.symm y)) := hf.comp e.symm.measurable
  rw [transportedKernel_lintegral e _ x hf,
    transportedKernel_lintegral e.symm _ _ hc]
  simp only [MeasurableEquiv.symm_symm,MeasurableEquiv.symm_apply_apply]

end BoltzmannNonuniqueness

end

end

section

/-! # Constant density weights commute with a measurable change of kernel coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem transportedKernel_constDensity (e : X ≃ᵐ Y) (K : Kernel Y Y) [IsSFiniteKernel K]
    (c : ℝ) :
    transportedKernel e (K.withDensity (fun _ _ => ENNReal.ofReal c)) =
      (transportedKernel e K).withDensity (fun _ _ => ENNReal.ofReal c) := by
  apply Kernel.ext_fun
  intro x f hf
  have hc : Measurable (fun y => f (e.symm y)) := hf.comp e.symm.measurable
  rw [transportedKernel_lintegral e _ x hf,
    Kernel.lintegral_withDensity (f := fun (_ : Y) (_ : Y) => ENNReal.ofReal c) K
      (by fun_prop) (e x) hc,
    Kernel.lintegral_withDensity (f := fun (_ : X) (_ : X) => ENNReal.ofReal c)
      (transportedKernel e K) (by fun_prop) x hf,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    transportedKernel_lintegral e K x hf]

end BoltzmannNonuniqueness

end

end

section

/-! # Coordinate transport of a measurable output restriction -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem transportedKernel_restrict (e : X ≃ᵐ Y) (K : Kernel Y Y)
    {A : Set Y} (hA : MeasurableSet A) :
    transportedKernel e (K.restrict hA) = (transportedKernel e K).restrict (e.measurable hA) := by
  apply Kernel.ext_fun
  intro x f hf
  rw [transportedKernel_lintegral e _ x hf,Kernel.lintegral_restrict,
    ← lintegral_indicator hA,Kernel.lintegral_restrict,
    ← lintegral_indicator (e.measurable hA),
    transportedKernel_lintegral e K x (hf.indicator (e.measurable hA))]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ A
  · simp [hy]
  · simp [hy]

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalGlobalRenormalized
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Remaining-flight time and characteristic spacetime coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightCharacteristic_advance (endTime : ℝ) (p : PhysicalFlightState) (s : ℝ) :
    flightCharacteristicEquiv endTime (physicalAdvance p s) =
      ((flightCharacteristicEquiv endTime p).1+s,(flightCharacteristicEquiv endTime p).2) := by
  have ht : endTime-(p.1-s) = endTime-p.1+s := by ring
  change (endTime-(p.1-s),(p.2.1+s • p.2.2-(endTime-(p.1-s)) • p.2.2,p.2.2)) = _
  rw [ht,add_smul]
  simp only [flightCharacteristicEquiv,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk]
  congr 2
  abel

theorem translated_time_lintegral (c a : ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s in Ioc 0 a, f (c+s)) = ∫⁻ t in Ioc c (c+a), f t := by
  have hset : (fun s : ℝ => c+s) ⁻¹' Ioc c (c+a) = Ioc 0 a := by
    ext s
    simp only [mem_preimage,mem_Ioc]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [← hset]
  exact (measurePreserving_add_left (volume : Measure ℝ) c).setLIntegral_comp_preimage
    measurableSet_Ioc hf

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Free waiting is exactly characteristic residence under the flight chart -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightCharacteristic_waiting_lintegral (C : ℝ≥0) (endTime : ℝ)
    (p : PhysicalFlightState) {F : ℝ × WeakTime.Phase → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F (flightCharacteristicEquiv endTime q) ∂physicalWaitingKernel C p) =
      ∫⁻ z, F z ∂WeakTime.residenceKernel C endTime (flightCharacteristicEquiv endTime p) := by
  let z := flightCharacteristicEquiv endTime p
  have hc : Measurable (fun q => F (flightCharacteristicEquiv endTime q)) :=
    hF.comp (flightCharacteristicEquiv endTime).measurable
  rw [physicalWaitingKernel_lintegral C p hc,WeakTime.residenceKernel_lintegral _ _ _ hF]
  have hf : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp ((C : ℝ)*(z.1-t)))*F (t,z.2)) :=
    (show Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp ((C : ℝ)*(z.1-t)))) by
      fun_prop).mul (hF.comp (measurable_id.prodMk measurable_const))
  have ht := translated_time_lintegral z.1 p.1 _ hf
  have hz : z.1+p.1 = endTime := by dsimp [z,flightCharacteristicEquiv] <;> ring
  rw [hz] at ht
  rw [← ht]
  apply lintegral_congr
  intro s
  rw [flightCharacteristic_advance]
  dsimp only [z]
  congr 1
  unfold clockSurvival
  congr 2
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MediumEndpointTransport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The physical marked histories in characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalWaitingKernel_eq_transport (C : ℝ≥0) (endTime : ℝ) :
    physicalWaitingKernel C = transportedKernel (flightCharacteristicEquiv endTime)
      (WeakTime.residenceKernel C endTime) := by
  apply Kernel.ext_fun
  intro p f hf
  rw [transportedKernel_lintegral _ _ p hf]
  have H := flightCharacteristic_waiting_lintegral C endTime p
    (F := fun z => f ((flightCharacteristicEquiv endTime).symm z))
    (hf.comp (flightCharacteristicEquiv endTime).symm.measurable)
  simpa only [MeasurableEquiv.symm_apply_apply] using H

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_KernelConjugacy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Iteration commutes with an exact measurable change of coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem kernel_eq_transport_of_map (e : X ≃ᵐ Y) (K : Kernel X X) (L : Kernel Y Y)
    (h : ∀ x, (K x).map e = L (e x)) : K = transportedKernel e L := by
  apply Kernel.ext_fun
  intro x f hf
  have hc : Measurable (fun y => f (e.symm y)) := hf.comp e.symm.measurable
  have H := congrArg (fun μ : Measure Y => ∫⁻ y, f (e.symm y) ∂μ) (h x)
  rw [lintegral_map hc e.measurable] at H
  rw [transportedKernel_lintegral e L x hf]
  simpa only [MeasurableEquiv.symm_apply_apply] using H

theorem transportedKernel_map (e : X ≃ᵐ Y) (L : Kernel Y Y) (x : X) :
    (transportedKernel e L x).map e = L (e x) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hc : Measurable (fun x => f (e x)) := hf.comp e.measurable
  rw [lintegral_map hf e.measurable,transportedKernel_lintegral e L x hc]
  simp only [MeasurableEquiv.apply_symm_apply]

theorem kernel_pow_map (e : X ≃ᵐ Y) (K : Kernel X X) (L : Kernel Y Y)
    (h : ∀ x, (K x).map e = L (e x)) (n : ℕ) (x : X) :
    ((K^n) x).map e = (L^n) (e x) := by
  rw [kernel_eq_transport_of_map e K L h,← transportedKernel_pow]
  exact transportedKernel_map e (L^n) x

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_NormalOutgoingSymmetry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedEventKernel_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumEventKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumEventKernel_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalGainEndpoint_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.stateKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_pow_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalGainTransport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Physical gain histories in the characteristic coordinates of the hot balance -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physical_terminal_characteristic (endTime : ℝ) (C : ℝ≥0)
    (f : V × V → ℝ≥0∞) (p : PhysicalFlightState) :
    clockSurvival C p.1 * f (finishMediumFlight p) =
      ENNReal.ofReal (Real.exp ((C:ℝ)*((flightCharacteristicEquiv endTime p).1-endTime))) *
        f (EuclideanFlight.flight endTime (flightCharacteristicEquiv endTime p).2) := by
  have hx : EuclideanFlight.flight endTime (flightCharacteristicEquiv endTime p).2 =
      finishMediumFlight p := by
    apply Prod.ext
    · dsimp [EuclideanFlight.flight,flightCharacteristicEquiv,finishMediumFlight]
      module
    · rfl
  rw [hx]
  unfold clockSurvival
  congr 3
  dsimp [flightCharacteristicEquiv]
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_BeamNormalOutgoing
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Space-time coordinates normalized by the local cold density -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem normalizedPoint_bounds {ρ t₀ A : ℝ} (hρ : 0 < ρ) (x₀ : V) (p : ℝ × V)
    (ht : p.1 ∈ Icc 0 A) (hx : ‖p.2‖ ≤ 6*A) :
    (normalizedPoint ρ t₀ x₀ p).1 ∈ Icc t₀ (t₀+A/ρ) ∧
      ‖(normalizedPoint ρ t₀ x₀ p).2-x₀‖ ≤ 6*A/ρ := by
  constructor
  · constructor
    · change t₀ ≤ t₀+p.1/ρ
      exact le_add_of_nonneg_right (div_nonneg ht.1 hρ.le)
    · change t₀+p.1/ρ ≤ t₀+A/ρ
      exact add_le_add le_rfl (div_le_div_of_nonneg_right ht.2 hρ.le)
  · simp only [normalizedPoint,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      abs_inv,abs_of_pos hρ]
    simpa only [div_eq_mul_inv,mul_comm] using mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hρ.le)

theorem normalized_beam_near (b : BeamCoefficients) {ρ t₀ A ε : ℝ}
    (hρ : 0 < ρ) (x₀ : V)
    (hnear : ∀ p : ℝ × V, p.1 ∈ Icc t₀ (t₀+A/ρ) → ‖p.2-x₀‖ ≤ 6*A/ρ → BeamNear b ε p)
    (p : ℝ × V) (ht : p.1 ∈ Icc 0 A) (hx : ‖p.2‖ ≤ 6*A) :
    BeamNear (b.normalized ρ t₀ x₀) ε p := by
  have H := normalizedPoint_bounds (t₀ := t₀) hρ x₀ p ht hx
  exact hnear _ H.1 H.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical beam source in characteristic variables has no terminal-time dependence -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem beamCharacteristicKernel_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (z : ℝ × WeakTime.Phase) {F : ℝ × WeakTime.Phase → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂beamCharacteristicKernel b endTime z) =
      mediumMarkedRate b 1 (characteristicBeamPoint z,z.2.2) *
        (∫⁻ n : Sphere, F (characteristicBeamJump z
          (markedChild 1 z.2.2 (b.plusPartner (characteristicBeamPoint z))
            (b.minusPartner (characteristicBeamPoint z)) n.1)) ∂sphereProbability) +
      mediumMarkedRate b 2 (characteristicBeamPoint z,z.2.2) *
        (∫⁻ n : Sphere, F (characteristicBeamJump z
          (markedChild 2 z.2.2 (b.plusPartner (characteristicBeamPoint z))
            (b.minusPartner (characteristicBeamPoint z)) n.1)) ∂sphereProbability) := by
  let e := flightCharacteristicEquiv endTime
  have hm : Measurable (fun q : PhysicalFlightState => F (e q)) := hF.comp e.measurable
  have ht : endTime-(e.symm z).1 = z.1 := by
    change endTime-(endTime-z.1) = z.1
    ring
  have hj (v : V) : e ((e.symm z).1,((e.symm z).2.1,v)) = characteristicBeamJump z v := by
    change (endTime-(endTime-z.1),
      (z.2.1+z.1 • z.2.2-(endTime-(endTime-z.1)) • v,v)) = _
    rw [sub_sub_cancel]
    rfl
  rw [beamCharacteristicKernel,transportedKernel_lintegral _ _ _ hF]
  change (∫⁻ q, F (e q) ∂physicalBeamCollision b endTime (e.symm z)) = _
  rw [physicalBeamCollision_lintegral,physicalMarkedCollision_lintegral b endTime 1 _ hm,
    physicalMarkedCollision_lintegral b endTime 2 _ hm]
  simp_rw [hj]
  rw [ht]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A velocity margin for smooth cutoffs around the bounded physical histories -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem medium_frequency_seven {v wp wm : V} {bp bm : ℝ}
    (hv : ‖v‖ ≤ 7) (hwp : ‖wp‖ ≤ 2) (hwm : ‖wm‖ ≤ 2)
    (hbp : 0 ≤ bp) (hbm : 0 ≤ bm) (hbp1 : bp ≤ 5/4) (hbm1 : bm ≤ 5/4) :
    0 ≤ mediumFrequency v wp wm bp bm ∧ mediumFrequency v wp wm bp bm ≤ 45*Real.pi := by
  have hp : ‖v-wp‖ ≤ 9 := (norm_sub_le v wp).trans (by linarith)
  have hm : ‖v-wm‖ ≤ 9 := (norm_sub_le v wm).trans (by linarith)
  have hp' : bp*‖v-wp‖ ≤ 45/4 := by
    calc
      _ ≤ (5/4:ℝ)*9 := mul_le_mul hbp1 hp (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hm' : bm*‖v-wm‖ ≤ 45/4 := by
    calc
      _ ≤ (5/4:ℝ)*9 := mul_le_mul hbm1 hm (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  constructor
  · unfold mediumFrequency
    positivity
  · unfold mediumFrequency
    have h := mul_le_mul_of_nonneg_left (add_le_add hp' hm') (by positivity : 0 ≤ 2*Real.pi)
    nlinarith

theorem BeamNear.frequency_margin {b : BeamCoefficients} {ε : ℝ} {p : ℝ × V}
    (hε : ε ≤ 1/4) (hnear : BeamNear b ε p) {v : V} (hv : ‖v‖ ≤ 7) :
    0 ≤ mediumFrequency v (b.plusPartner p) (b.minusPartner p)
      (b.plusDensity p) (b.minusDensity p) ∧
    mediumFrequency v (b.plusPartner p) (b.minusPartner p)
      (b.plusDensity p) (b.minusDensity p) ≤ 45*Real.pi := by
  have hwp : ‖b.plusPartner p‖ ≤ 2 := by
    have h := norm_add_le (b.plusPartner p-beamAxis) beamAxis
    rw [sub_add_cancel,axis_norms.2.2] at h
    linarith [hnear.1]
  have hwm : ‖b.minusPartner p‖ ≤ 2 := by
    have h := norm_add_le (b.minusPartner p-(-beamAxis)) (-beamAxis)
    rw [sub_add_cancel,norm_neg,axis_norms.2.2] at h
    linarith [hnear.2.1]
  have hp := abs_le.mp hnear.2.2.1
  have hm := abs_le.mp hnear.2.2.2
  exact medium_frequency_seven hv hwp hwm (by linarith [hp.1]) (by linarith [hm.1])
    (by linarith [hp.2]) (by linarith [hm.2])

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The two atomic cold beams as a measurable partner kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem beamPartnerKernel_apply (b : BeamCoefficients) (p : ℝ × V) :
    beamPartnerKernel b p = beamMeasure b p := by
  rw [beamPartnerKernel,add_apply,
    Kernel.withDensity_apply (f := fun p _ => ENNReal.ofReal (b.plusDensity p)) _
      (b.plusDensity_measurable.ennreal_ofReal.comp measurable_fst),
    Kernel.withDensity_apply (f := fun p _ => ENNReal.ofReal (b.minusDensity p)) _
      (b.minusDensity_measurable.ennreal_ofReal.comp measurable_fst),
    withDensity_const,withDensity_const,Kernel.deterministic_apply,Kernel.deterministic_apply]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The atomic beam's genuine normal-angle collision law in characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem beamNormalCharacteristicKernel_lintegral (b : BeamCoefficients)
    (z : CharacteristicPhase) {f : CharacteristicPhase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ q, f q ∂beamNormalCharacteristicKernel b z) =
      ∫⁻ v, f (characteristicBeamJump z v)
        ∂normalGainKernel (beamPartnerKernel b) (characteristicBeamPoint z,z.2.2) := by
  rw [beamNormalCharacteristicKernel,transportedKernel_lintegral _ _ z hf,
    normalPhaseGainKernel_lintegral_gain _ _
      (f := fun y => f (characteristicEquiv.symm y)) (hf.comp characteristicEquiv.symm.measurable)]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The two atomic partners' normal-angle gain equals the outgoing-sphere gain -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem normalGain_beam_projection (b : BeamCoefficients) (p : ℝ × V) (v : V)
    (hp : 0 ≤ b.plusDensity p) (hm : 0 ≤ b.minusDensity p) :
    normalGainKernel (beamPartnerKernel b) (p,v) =
      ENNReal.ofReal (4*Real.pi*b.plusDensity p*‖v-b.plusPartner p‖) • outgoing (v,b.plusPartner p)+
      ENNReal.ofReal (4*Real.pi*b.minusDensity p*‖v-b.minusPartner p‖) • outgoing (v,b.minusPartner p) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [normalGainKernel_lintegral _ _ hf]
  simp_rw [normal_left_integral_outgoing _ _ hf,normal_right_integral_outgoing _ _ hf]
  rw [beamPartnerKernel_apply,beamMeasure]
  simp only [lintegral_add_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul]
  rw [outgoing_swap (b.plusPartner p) v,outgoing_swap (b.minusPartner p) v,
    norm_sub_rev (b.plusPartner p) v,norm_sub_rev (b.minusPartner p) v]
  have hc (a : ℝ) (hn : 0 ≤ a) (r : ℝ) :
      2*(ENNReal.ofReal a*ENNReal.ofReal (2*Real.pi*r)) = ENNReal.ofReal (4*Real.pi*a*r) := by
    rw [← ENNReal.ofReal_mul hn,← ENNReal.ofReal_ofNat 2,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [show (ENNReal.ofReal (b.plusDensity p)*
      (ENNReal.ofReal (2*Real.pi*‖v-b.plusPartner p‖)*∫⁻ u, f u ∂outgoing (v,b.plusPartner p))+
      ENNReal.ofReal (b.minusDensity p)*
      (ENNReal.ofReal (2*Real.pi*‖v-b.minusPartner p‖)*∫⁻ u, f u ∂outgoing (v,b.minusPartner p)))+
      (ENNReal.ofReal (b.plusDensity p)*
      (ENNReal.ofReal (2*Real.pi*‖v-b.plusPartner p‖)*∫⁻ u, f u ∂outgoing (v,b.plusPartner p))+
      ENNReal.ofReal (b.minusDensity p)*
      (ENNReal.ofReal (2*Real.pi*‖v-b.minusPartner p‖)*∫⁻ u, f u ∂outgoing (v,b.minusPartner p))) =
      (2*(ENNReal.ofReal (b.plusDensity p)*ENNReal.ofReal (2*Real.pi*‖v-b.plusPartner p‖)))*
        (∫⁻ u, f u ∂outgoing (v,b.plusPartner p))+
      (2*(ENNReal.ofReal (b.minusDensity p)*ENNReal.ofReal (2*Real.pi*‖v-b.minusPartner p‖)))*
        (∫⁻ u, f u ∂outgoing (v,b.minusPartner p)) by ring]
  rw [hc _ hp _,
    hc _ hm _]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ScaledBoundedEvent
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Equal scaled partner measures give equal scaled normal-angle gains -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem normalGainKernel_smul_eq_of_measure_smul_eq
    (K : Kernel X Velocity) (L : Kernel Y Velocity) [IsSFiniteKernel K] [IsSFiniteKernel L]
    (x : X) (y : Y) (v : Velocity) (c d : ℝ≥0∞) (h : c • K x = d • L y) :
    c • normalGainKernel K (x,v) = d • normalGainKernel L (y,v) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hl := congrArg (fun μ : Measure Velocity => ∫⁻ w, ∫⁻ ω,
    ENNReal.ofReal (collisionKernel w v ω)*f (scatterLeft w v ω) ∂sphereArea ∂μ) h
  have hr := congrArg (fun μ : Measure Velocity => ∫⁻ w, ∫⁻ ω,
    ENNReal.ofReal (collisionKernel w v ω)*f (scatterRight w v ω) ∂sphereArea ∂μ) h
  simp only [lintegral_smul_measure,smul_eq_mul] at hl hr
  rw [lintegral_smul_measure,lintegral_smul_measure,smul_eq_mul,smul_eq_mul,
    normalGainKernel_lintegral K (x,v) hf,normalGainKernel_lintegral L (y,v) hf,
    mul_add,mul_add,hl,hr]

end BoltzmannNonuniqueness

end

end

section

/-! # Positive collision-time integrals under the local density scale -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem scaled_time_lintegral {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ s in Ioc 0 a, ENNReal.ofReal ρ*f (ρ*s)) =
      ∫⁻ t in Ioc 0 (ρ*a), f t := by
  have hm : MeasurePreserving (fun s : ℝ => ρ*s)
      (ENNReal.ofReal ρ • (volume : Measure ℝ)) volume := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.map_smul]
    simpa only [abs_of_pos hρ] using Real.smul_map_volume_mul_left hρ.ne'
  have hs : (fun s : ℝ => ρ*s) ⁻¹' Ioc 0 (ρ*a) = Ioc 0 a := by
    ext s
    simp only [mem_preimage,mem_Ioc]
    constructor
    · rintro ⟨h₁,h₂⟩
      constructor <;> nlinarith
    · rintro ⟨h₁,h₂⟩
      exact ⟨mul_pos hρ h₁,mul_le_mul_of_nonneg_left h₂ hρ.le⟩
  have H := hm.setLIntegral_comp_preimage (s := Ioc 0 (ρ*a)) measurableSet_Ioc hf
  rw [hs,Measure.restrict_smul,lintegral_smul_measure,smul_eq_mul] at H
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact H

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact local density normalization of physical flight states -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightScale_advance (ρ : ℝ) (hρ : ρ ≠ 0) (x₀ : V)
    (p : PhysicalFlightState) (s : ℝ) :
    flightScaleEquiv ρ hρ x₀ (physicalAdvance p s) =
      physicalAdvance (flightScaleEquiv ρ hρ x₀ p) (ρ*s) := by
  apply Prod.ext
  · dsimp [flightScaleEquiv,physicalAdvance]
    ring
  · apply Prod.ext
    · dsimp [flightScaleEquiv,physicalAdvance]
      module
    · rfl

theorem normalized_mediumPoint (ρ : ℝ) (hρ : ρ ≠ 0) (t₀ endTime : ℝ) (x₀ : V)
    (p : PhysicalFlightState) (s : ℝ) :
    normalizedPoint ρ t₀ x₀
      (mediumPoint (ρ*(endTime-t₀)) (flightScaleEquiv ρ hρ x₀ p) (ρ*s)) =
      mediumPoint endTime p s := by
  apply Prod.ext
  · dsimp [normalizedPoint,mediumPoint,flightScaleEquiv]
    field_simp
    ring
  · dsimp [normalizedPoint,mediumPoint,flightScaleEquiv]
    rw [show ρ • (p.2.1-x₀)+(ρ*s) • p.2.2 =
      ρ • (p.2.1-x₀+s • p.2.2) by module,smul_smul,inv_mul_cancel₀ hρ,one_smul]
    abel

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The density-scaled waiting kernel has the reference clock -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem scaled_waiting_lintegral (C : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ) (x₀ : V)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    ENNReal.ofReal ρ * (∫⁻ q, F (flightScaleEquiv ρ hρ.ne' x₀ q)
      ∂physicalWaitingKernel (Real.toNNReal ρ*C) p) =
      ∫⁻ q, F q ∂physicalWaitingKernel C (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  let e := flightScaleEquiv ρ hρ.ne' x₀
  have hc : Measurable (fun q => F (e q)) := hF.comp e.measurable
  have hf : Measurable (fun s : ℝ => clockSurvival C s * F (physicalAdvance (e p) s)) :=
    (show Measurable (clockSurvival C) by unfold clockSurvival; fun_prop).mul
      (hF.comp (physicalAdvance_measurable.comp (measurable_const.prodMk measurable_id)))
  rw [physicalWaitingKernel_lintegral _ _ hc,physicalWaitingKernel_lintegral _ _ hF]
  change ENNReal.ofReal ρ * (∫⁻ s in Ioc 0 p.1,
    clockSurvival (Real.toNNReal ρ*C) s * F (e (physicalAdvance p s))) =
      ∫⁻ s in Ioc 0 (ρ*p.1), clockSurvival C s * F (physicalAdvance (e p) s)
  rw [← scaled_time_lintegral hρ p.1 hf,← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro s
  have he := flightScale_advance ρ hρ.ne' x₀ p s
  change e (physicalAdvance p s) = physicalAdvance (e p) (ρ*s) at he
  rw [he]
  congr 2
  unfold clockSurvival
  congr 2
  push_cast
  rw [Real.coe_toNNReal _ hρ.le]
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The measurable two-beam collision law under local density normalization -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumCollisionKernel_normalized (b : BeamCoefficients) (ρ t₀ : ℝ) (x₀ : V)
    (z : MediumState) :
    mediumCollisionKernel (b.normalized ρ t₀ x₀) z =
      mediumCollisionKernel b (normalizedPoint ρ t₀ x₀ z.1,z.2) := by
  rw [mediumCollisionKernel_projection,mediumCollisionKernel_projection]
  rfl

theorem normalized_flight_location (ρ : ℝ) (hρ : ρ ≠ 0) (t₀ endTime : ℝ) (x₀ : V)
    (p : PhysicalFlightState) :
    normalizedPoint ρ t₀ x₀
      (ρ*(endTime-t₀)-(flightScaleEquiv ρ hρ x₀ p).1,
        (flightScaleEquiv ρ hρ x₀ p).2.1) = (endTime-p.1,p.2.1) := by
  simpa only [mediumPoint,mul_zero,zero_add,add_zero,zero_smul] using
    normalized_mediumPoint ρ hρ t₀ endTime x₀ p 0

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedLocalBeamBlock
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform branching growth from coefficient bounds only on the visited cylinder -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniform_damped_bounded_local_block {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Cmax : ℝ≥0, ∃ N : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ y : ℝ × V, y.1 ∈ Icc (endTime-A) endTime → ‖y.2-z.1‖ ≤ 6*A → BeamNear b ε y) →
      (6 : ℝ≥0∞) < dampedBoundedBlockMass C b endTime T (A,z) κ d N := by
  obtain ⟨A₀,hA₀,hgrowth⟩ := uniform_damped_bounded_block_growth hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT Cmax
  obtain ⟨N,ε₁,hε₁,hblock⟩ := hgrowth T hT Cmax
  let L : ℝ := (N:ℝ)+1
  have hL : 0 < L := by dsimp [L] <;> positivity
  refine ⟨N,min ε₁ (1/L),lt_min hε₁ (one_div_pos.mpr hL),?_⟩
  intro C hC hCmax ε hε A hA z b endTime hnear
  apply hblock C hC hCmax ε ⟨hε.1,hε.2.trans (min_le_left _ _)⟩ A hA z b endTime
  intro n hn a ha
  have hnL : (n:ℝ) ≤ L := (Nat.cast_le.mpr hn.le).trans (le_add_of_nonneg_right (by norm_num))
  have hbudget : (n:ℝ)*ε ≤ 1 :=
    (mul_le_mul_of_nonneg_right hnL hε.1).trans (by
      have hh := (le_div_iff₀ hL).mp (hε.2.trans (min_le_right _ _))
      simpa only [mul_comm] using hh)
  exact wordNearby_from_start b endTime A z hε.1 (hA₀.le.trans hA.1) hnear n hbudget a ha

theorem uniform_damped_bounded_physical_block {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Cmax : ℝ≥0, ∃ N : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc A₀ T, ∀ v : RetainedState,
      ∀ (b : BeamCoefficients) (ρ t₀ : ℝ) (x₀ : V), 0 < ρ →
      (∀ p : ℝ × V, p.1 ∈ Icc t₀ (t₀+A/ρ) → ‖p.2-x₀‖ ≤ 6*A/ρ → BeamNear b ε p) →
      (6 : ℝ≥0∞) < dampedBoundedBlockMass C (b.normalized ρ t₀ x₀) A T (A,(0,v)) κ d N := by
  obtain ⟨A₀,hA₀,hgrowth⟩ := uniform_damped_bounded_local_block hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT Cmax
  obtain ⟨N,ε₀,hε₀,hblock⟩ := hgrowth T hT Cmax
  refine ⟨N,ε₀,hε₀,?_⟩
  intro C hC hCmax ε hε A hA v b ρ t₀ x₀ hρ hnear
  apply hblock C hC hCmax ε hε A hA (0,v) (b.normalized ρ t₀ x₀) A
  intro p hp hx
  exact normalized_beam_near b hρ x₀ hnear p (by simpa using hp) (by simpa using hx)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricAnnularFrequency
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual geometric cold coefficients are close throughout a short physical cylinder -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem beam_near_on_cylinder {ε C : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hC : 1 ≤ C) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ {θ η r α γ ρ t₀ A : ℝ},
      (hθ : 0 < θ) → 0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ → 0 < ρ → 0 ≤ t₀ →
      t₀ ≤ C*r/2 → 6*A/ρ ≤ (ε/20)*r →
      ∀ x₀ : Velocity, ‖transverse x₀‖ = r → |axial x₀| ≤ C*r/2 →
      ∀ p : ℝ × Velocity, p.1 ∈ Icc t₀ (t₀+A/ρ) → ‖p.2-x₀‖ ≤ 6*A/ρ →
        BeamNear (beamCoefficients hθ hα hγ η r) ε p := by
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  obtain ⟨γ₀,hγ₀,hdensity⟩ := beam_density_tolerance hε hε1 hCpos
  refine ⟨γ₀,hγ₀,?_⟩
  intro θ η r α γ ρ t₀ A hθ hη hηsmall hr hα hαε hγ hγsmall hρ ht₀ ht₀C hshort x₀ hx₀ hz₀ p hpt hpx
  have hdist : ‖p.2-x₀‖ ≤ (ε/20)*r := hpx.trans hshort
  have hδr : (ε/20)*r ≤ C*r/2 := by nlinarith
  have htime : A/ρ ≤ C*r/2 := by
    rw [mul_div_assoc] at hshort
    have hCr : 0 ≤ C*r := mul_nonneg hCpos.le hr.le
    linarith
  have ht : 0 ≤ p.1 := ht₀.trans hpt.1
  have htC : p.1 ≤ C*r := by linarith [hpt.2]
  have htrans : |‖transverse p.2‖-r| ≤ (ε/20)*r := by
    calc
      _ = |‖transverse p.2‖-‖transverse x₀‖| := by rw [hx₀]
      _ ≤ ‖transverse p.2-transverse x₀‖ := abs_norm_sub_norm_le _ _
      _ = ‖transverse (p.2-x₀)‖ := by rw [PlaneChart.transverse_sub]
      _ ≤ ‖p.2-x₀‖ := LargeOutput.transverse_norm_le _
      _ ≤ _ := hdist
  have hxpos : 0 < ‖transverse p.2‖ := by
    have hh := (abs_le.mp htrans).1
    nlinarith
  have hzC : |axial p.2| ≤ C*r := by
    have hh := abs_add_le (axial p.2-axial x₀) (axial x₀)
    rw [sub_add_cancel] at hh
    have hh' : |axial p.2-axial x₀| ≤ (ε/20)*r := by
      rw [← PlaneChart.axial_sub]
      exact (SmallInputGeometry.abs_axial_le_norm _).trans hdist
    linarith
  have hd (σ : ℝ) (hσ : |σ| = 1) : |beamDensity θ η α γ r σ p-1| ≤ ε :=
    hdensity hθ hη hηsmall hr hα (hαε.trans hε1) hγ hγsmall ht htC p.2 hxpos htrans hzC σ hσ
  have hp := (beamVelocity_error hα θ η γ 1 p).trans hαε
  have hm := (beamVelocity_error hα θ η γ (-1) p).trans hαε
  refine ⟨?_,?_,hd 1 (by norm_num),hd (-1) (by norm_num)⟩
  · simpa only [beamCoefficients,one_smul] using hp
  · simpa only [beamCoefficients,neg_one_smul] using hm

theorem cylinder_small_of_density_scale {A K r ε : ℝ} (hK : 0 < K) (hr : 0 < r)
    (hbudget : 480*A ≤ ε*K) : 6*A/(K/(4*r)) ≤ (ε/20)*r := by
  have hρ : 0 < K/(4*r) := by positivity
  apply (div_le_iff₀ hρ).mpr
  have he : (ε/20)*r*(K/(4*r)) = ε*K/80 := by field_simp <;> ring
  rw [he]
  linarith

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A finite growing block for the actual geometric cold coefficients -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_damped_bounded_block_growth {d κ C : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) (hC : 1 ≤ C) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Dmax : ℝ≥0,
      ∃ N : ℕ, ∃ ε γ₀ : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ D : ℝ≥0, referenceClock ≤ D → D ≤ Dmax →
      ∀ {θ η r α γ K t₀ A : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*T ≤ ε*K → 0 ≤ t₀ → t₀ ≤ C*r/2 → A ∈ Icc A₀ T →
      ∀ (x₀ : Velocity) (v : RetainedState), ‖transverse x₀‖ = r → |axial x₀| ≤ C*r/2 →
      (6 : ℝ≥0∞) < dampedBoundedBlockMass D
        ((beamCoefficients hθ hα hγ η r).normalized (K/(4*r)) t₀ x₀)
        A T (A,(0,v)) κ d N := by
  obtain ⟨A₀,hA₀,hblock⟩ := uniform_damped_bounded_physical_block hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT Dmax
  obtain ⟨N,ε₀,hε₀,hgrowth⟩ := hblock T hT Dmax
  let ε := min ε₀ (1/4:ℝ)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hεsmall : ε ≤ 1/4 := min_le_right _ _
  obtain ⟨γ₀,hγ₀,hnear⟩ := beam_near_on_cylinder hε (by linarith) hC
  refine ⟨N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro D hD hDmax θ η r α γ K t₀ A hθ hη hηsmall hr hα hαε hγ hγsmall hK hlarge ht₀ ht₀C hA x₀ v hx₀ hz₀
  have hρ : 0 < K/(4*r) := by positivity
  have hbudget : 480*A ≤ ε*K := (mul_le_mul_of_nonneg_left hA.2 (by norm_num)).trans hlarge
  have hshort := cylinder_small_of_density_scale hK hr hbudget
  apply hgrowth D hD hDmax ε ⟨hε.le,min_le_left _ _⟩ A hA v (beamCoefficients hθ hα hγ η r)
    (K/(4*r)) t₀ x₀ hρ
  exact hnear hθ hη hηsmall hr hα hαε hγ hγsmall hρ ht₀ ht₀C hshort x₀ hx₀ hz₀

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedBoundedEndpointTransport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The measurable two-beam collision law under local density normalization -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumCollision_normalized (C : ℝ≥0) (b : BeamCoefficients) (ρ t₀ : ℝ) (x₀ : V)
    (z : MediumState) :
    dampedMediumCollision C (b.normalized ρ t₀ x₀) z =
      dampedMediumCollision C b (normalizedPoint ρ t₀ x₀ z.1,z.2) := by
  rw [dampedMediumCollision_apply,dampedMediumCollision_apply,mediumCollisionKernel_normalized]

theorem dampedMediumStateCollision_scale_map (C : ℝ≥0) (b : BeamCoefficients) (ρ : ℝ) (hρ : ρ ≠ 0)
    (t₀ endTime : ℝ) (x₀ : V) (p : PhysicalFlightState) :
    (dampedMediumStateCollision C b endTime p).map (flightScaleEquiv ρ hρ x₀) =
      dampedMediumStateCollision C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀))
        (flightScaleEquiv ρ hρ x₀ p) := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hc : Measurable (fun q => F (flightScaleEquiv ρ hρ x₀ q)) :=
    hF.comp (flightScaleEquiv ρ hρ x₀).measurable
  rw [lintegral_map hF (flightScaleEquiv ρ hρ x₀).measurable,
    dampedMediumStateCollision_lintegral C b endTime p hc,
    dampedMediumStateCollision_lintegral C _ _ _ hF,
    dampedMediumCollision_normalized,normalized_flight_location]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Enlarged-damping physical histories in characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedStateCollision_eq_transport (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    dampedMediumStateCollision C b endTime = transportedKernel (flightCharacteristicEquiv endTime)
      (dampedCharacteristicKernel C b endTime) :=
  (transportedKernel_symm (flightCharacteristicEquiv endTime) _).symm

theorem dampedCharacteristicKernel_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (z : ℝ × WeakTime.Phase) {f : ℝ × WeakTime.Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ q, f q ∂dampedCharacteristicKernel C b endTime z) =
      ∫⁻ v, f (z.1,(z.2.1+z.1 • z.2.2-z.1 • v,v))
        ∂dampedMediumCollision C b ((z.1,z.2.1+z.1 • z.2.2),z.2.2) := by
  have hc : Measurable (fun q => f (flightCharacteristicEquiv endTime q)) :=
    hf.comp (flightCharacteristicEquiv endTime).measurable
  rw [dampedCharacteristicKernel,transportedKernel_lintegral _ _ z hf]
  simp only [MeasurableEquiv.symm_symm]
  rw [dampedMediumStateCollision_lintegral C b endTime _ hc]
  simp only [flightCharacteristicEquiv,MeasurableEquiv.symm_mk,MeasurableEquiv.coe_mk,
    Equiv.coe_fn_mk,Equiv.coe_fn_symm_mk,sub_sub_cancel]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The enlarged-damping characteristic kernel is gain plus positive retention -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem characteristicBeamFrequency_measurable (b : BeamCoefficients) :
    Measurable (characteristicBeamFrequency b) := by
  have hm : Measurable characteristicBeamPoint := by unfold characteristicBeamPoint; fun_prop
  have hp := b.plusPartner_measurable.comp hm
  have hn := b.minusPartner_measurable.comp hm
  have hdp := b.plusDensity_measurable.comp hm
  have hdn := b.minusDensity_measurable.comp hm
  unfold characteristicBeamFrequency mediumFrequency
  fun_prop

theorem dampedCharacteristicKernel_projection {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (endTime : ℝ) (z : ℝ × WeakTime.Phase)
    (hf : characteristicBeamFrequency b z ≤ (referenceClock : ℝ)) :
    dampedCharacteristicKernel C b endTime z =
      positiveSourceKernel (beamCharacteristicKernel b endTime) (fun _ => 1)
        (fun q => (C : ℝ)-characteristicBeamFrequency b q) z := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hm : Measurable (characteristicBeamJump z) := by unfold characteristicBeamJump; fun_prop
  have hj : Measurable (fun v => F (characteristicBeamJump z v)) := hF.comp hm
  rw [dampedCharacteristicKernel_lintegral C b endTime z hF]
  change (∫⁻ v, F (characteristicBeamJump z v)
    ∂dampedMediumCollision C b (characteristicBeamPoint z,z.2.2)) = _
  rw [dampedMediumCollision_eq_nonzero_marks hC b (characteristicBeamPoint z,z.2.2) hf,
    lintegral_add_measure,lintegral_add_measure,lintegral_smul_measure,
    mediumMarkedKernel_lintegral b 1 _ hj,mediumMarkedKernel_lintegral b 2 _ hj,
    lintegral_dirac,smul_eq_mul,
    positiveSourceKernel_one_lintegral (beamCharacteristicKernel b endTime)
      (r := fun q => (C : ℝ)-characteristicBeamFrequency b q) (measurable_const.sub
      (characteristicBeamFrequency_measurable b)) z hF,
    beamCharacteristicKernel_lintegral b endTime z hF]
  congr 1
  simp only [characteristicBeamJump,add_sub_cancel_right]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The physical collision intensity and clock normalize by the same density -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaledCollision_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂dampedDensityScaledCollision C b endTime ρ p) =
      ENNReal.ofReal (ρ : ℝ) * ∫⁻ q, F q ∂dampedMediumStateCollision C b endTime p := by
  rw [dampedDensityScaledCollision,Kernel.lintegral_withDensity _ (by fun_prop) p hF,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem dampedDensityScaledEvent_scale_map (C : ℝ≥0) (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (p : PhysicalFlightState) :
    (dampedDensityScaledEventKernel C b endTime (Real.toNNReal ρ) p).map (flightScaleEquiv ρ hρ.ne' x₀) =
      (dampedMediumStateCollision C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)) ∘ₖ
        physicalWaitingKernel C) (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  apply Measure.ext_of_lintegral
  intro F hF
  let e := flightScaleEquiv ρ hρ.ne' x₀
  let L := dampedMediumStateCollision C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀))
  have hc : Measurable (fun q => F (e q)) := hF.comp e.measurable
  have he (q : PhysicalFlightState) :
      (∫⁻ r, F (e r) ∂dampedMediumStateCollision C b endTime q) = ∫⁻ r, F r ∂L (e q) := by
    rw [← lintegral_map hF e.measurable,dampedMediumStateCollision_scale_map C b ρ hρ.ne' t₀ endTime x₀ q]
  rw [lintegral_map hF e.measurable,dampedDensityScaledEventKernel,Kernel.lintegral_comp _ _ _ hc,
    Kernel.lintegral_comp _ _ _ hF]
  simp_rw [dampedDensityScaledCollision_lintegral C b endTime _ _ hc,he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [Real.coe_toNNReal _ hρ.le]
  exact scaled_waiting_lintegral C hρ x₀ p (hF.lintegral_kernel (κ := L))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Local density normalization preserves the bounded physical event histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedBoundedDensityScaledEvent_map (C : ℝ≥0) (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (p : PhysicalFlightState) :
    (dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ) p).map
      (flightScaleEquiv ρ hρ.ne' x₀) =
      dampedBoundedPhysicalEvent C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀))
        (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  have hs : (flightScaleEquiv ρ hρ.ne' x₀) ⁻¹' mediumVelocityBox = mediumVelocityBox := rfl
  rw [dampedBoundedDensityScaledEvent,Kernel.restrict_apply,← hs,
    ← Measure.restrict_map (flightScaleEquiv ρ hρ.ne' x₀).measurable mediumVelocityBox_measurable,
    dampedDensityScaledEvent_scale_map C b hρ t₀ endTime x₀ p]
  rfl

theorem dampedBoundedDensityScaledEvent_pow_map (C : ℝ≥0) (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (n : ℕ) (p : PhysicalFlightState) :
    (((dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ))^n) p).map
      (flightScaleEquiv ρ hρ.ne' x₀) =
      ((dampedBoundedPhysicalEvent C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)))^n)
        (flightScaleEquiv ρ hρ.ne' x₀ p) :=
  kernel_pow_map (flightScaleEquiv ρ hρ.ne' x₀) _ _
    (dampedBoundedDensityScaledEvent_map C b hρ t₀ endTime x₀) n p

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The density-scaled physical histories use the same scaled characteristic clock -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaledCollision_transport (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) :
    dampedDensityScaledCollision C b endTime ρ = transportedKernel (flightCharacteristicEquiv endTime)
      (densityScaledCharacteristicKernel C b endTime ρ) := by
  rw [densityScaledCharacteristicKernel,transportedKernel_constDensity]
  simp only [← dampedStateCollision_eq_transport,dampedDensityScaledCollision]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Density scaling gives the exact physical gain and loss-complement coefficients -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem densityScaledCharacteristicKernel_projection {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) (z : ℝ × WeakTime.Phase)
    (hf : characteristicBeamFrequency b z ≤ (referenceClock : ℝ)) :
    densityScaledCharacteristicKernel C b endTime ρ z =
      ENNReal.ofReal (ρ : ℝ) • beamCharacteristicKernel b endTime z+
      ENNReal.ofReal (((ρ*C : ℝ≥0):ℝ)-(ρ:ℝ)*characteristicBeamFrequency b z) • Measure.dirac z := by
  have hm : ENNReal.ofReal (ρ : ℝ)*ENNReal.ofReal ((C:ℝ)-characteristicBeamFrequency b z) =
      ENNReal.ofReal (((ρ*C : ℝ≥0):ℝ)-(ρ:ℝ)*characteristicBeamFrequency b z) := by
    rw [← ENNReal.ofReal_mul (p := (ρ : ℝ))
      (q := (C:ℝ)-characteristicBeamFrequency b z) (show (0:ℝ) ≤ (ρ:ℝ) from ρ.property),NNReal.coe_mul]
    congr 1
    ring
  apply Measure.ext_of_lintegral
  intro f hfn
  rw [densityScaledCharacteristicKernel,Kernel.lintegral_withDensity
    (f := fun (_ : ℝ × WeakTime.Phase) (_ : ℝ × WeakTime.Phase) => ENNReal.ofReal (ρ : ℝ))
    (dampedCharacteristicKernel C b endTime) (by fun_prop) z hfn,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    dampedCharacteristicKernel_projection hC b endTime z hf,
    positiveSourceKernel_one_lintegral _ (r := fun q => (C:ℝ)-characteristicBeamFrequency b q)
      (measurable_const.sub (characteristicBeamFrequency_measurable b)) z hfn,
    lintegral_add_measure,lintegral_smul_measure,lintegral_smul_measure,lintegral_dirac,
    smul_eq_mul,smul_eq_mul,mul_add,← mul_assoc,hm]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedGeometricBlock
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The finite-speed cone of the velocity-truncated physical histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem boundedFlightCone_measurable (p : PhysicalFlightState) :
    MeasurableSet {q | boundedFlightCone p q} := by
  have hv : Measurable (fun q : PhysicalFlightState => ‖q.2.2‖) := by fun_prop
  have hx : Measurable (fun q : PhysicalFlightState => ‖q.2.1-p.2.1‖) := by fun_prop
  have ht : Measurable (fun q : PhysicalFlightState => 6*(p.1-q.1)) := by fun_prop
  unfold boundedFlightCone
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_le hv measurable_const).inter (measurableSet_le hx ht)))

theorem boundedFlightCone_refl {p : PhysicalFlightState} (ht : 0 ≤ p.1) (hv : ‖p.2.2‖ ≤ 6) :
    boundedFlightCone p p := by
  exact ⟨ht,le_rfl,hv,by simp⟩

theorem boundedFlightCone_trans {p q r : PhysicalFlightState}
    (hpq : boundedFlightCone p q) (hqr : boundedFlightCone q r) : boundedFlightCone p r := by
  refine ⟨hqr.1,hqr.2.1.trans hpq.2.1,hqr.2.2.1,?_⟩
  calc
    ‖r.2.1-p.2.1‖ = ‖(r.2.1-q.2.1)+(q.2.1-p.2.1)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖r.2.1-q.2.1‖+‖q.2.1-p.2.1‖ := norm_add_le _ _
    _ ≤ 6*(q.1-r.1)+6*(p.1-q.1) := add_le_add hqr.2.2.2 hpq.2.2.2
    _ = 6*(p.1-r.1) := by ring

theorem boundedFlightCone_step {p : PhysicalFlightState} {s : ℝ} {v : V}
    (hs : s ∈ Ioc 0 p.1) (hp : ‖p.2.2‖ ≤ 6) (hv : ‖v‖ ≤ 6) :
    boundedFlightCone p (p.1-s,(p.2.1+s • p.2.2,v)) := by
  refine ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1.le,hv,?_⟩
  simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs.1]
  have hm := mul_le_mul_of_nonneg_left hp hs.1.le
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Actual bounded physical events stay in their finite-speed cone almost everywhere -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaledEvent_ae_geometry (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) (p : PhysicalFlightState) (hp : ‖p.2.2‖ ≤ 6) :
    ∀ᵐ q ∂dampedDensityScaledEventKernel C b endTime ρ p,
      0 ≤ q.1 ∧ q.1 ≤ p.1 ∧ ‖q.2.1-p.2.1‖ ≤ 6*(p.1-q.1) := by
  let A : Set PhysicalFlightState :=
    {q | ¬(0 ≤ q.1 ∧ q.1 ≤ p.1 ∧ ‖q.2.1-p.2.1‖ ≤ 6*(p.1-q.1))}
  have hA : MeasurableSet A := by
    dsimp [A]
    measurability
  have hF : Measurable (A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [ae_iff]
  change dampedDensityScaledEventKernel C b endTime ρ p A = 0
  rw [← lintegral_indicator_one hA,dampedDensityScaledEventKernel,
    Kernel.lintegral_comp _ _ _ hF,
    physicalWaitingKernel_lintegral (ρ*C) p hF.lintegral_kernel]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [dampedDensityScaledCollision_lintegral _ _ _ _ _ hF,
    dampedMediumStateCollision_lintegral _ _ _ _ hF]
  have hz (v : V) : A.indicator (1 : PhysicalFlightState → ℝ≥0∞)
      ((physicalAdvance p s).1,((physicalAdvance p s).2.1,v)) = 0 := by
    have hc := boundedFlightCone_step hs hp (show ‖(0:V)‖ ≤ 6 by simp)
    apply indicator_of_notMem
    exact fun h => h ⟨hc.1,hc.2.1,hc.2.2.2⟩
  simp only [hz,lintegral_zero,mul_zero,Pi.zero_apply]

theorem dampedBoundedDensityScaledEvent_ae_cone (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) (p : PhysicalFlightState) (hp : ‖p.2.2‖ ≤ 6) :
    ∀ᵐ q ∂dampedBoundedDensityScaledEvent C b endTime ρ p, boundedFlightCone p q := by
  change ∀ᵐ q ∂(dampedDensityScaledEventKernel C b endTime ρ p).restrict mediumVelocityBox,
    boundedFlightCone p q
  filter_upwards [ae_restrict_of_ae (dampedDensityScaledEvent_ae_geometry C b endTime ρ p hp),
    ae_restrict_mem mediumVelocityBox_measurable] with q hq hv
  exact ⟨hq.1,hq.2.1,hv,hq.2.2⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionWaitingCone
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separate collision and free-waiting laws preserve the reachable cone -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaledCollision_ae_fixed (C : ℝ≥0) (b : BeamCoefficients)
    (T : ℝ) (ρ : ℝ≥0) (p : PhysicalFlightState) :
    ∀ᵐ q ∂dampedDensityScaledCollision C b T ρ p, q.1 = p.1 ∧ q.2.1 = p.2.1 := by
  let A : Set PhysicalFlightState := {q | ¬(q.1 = p.1 ∧ q.2.1 = p.2.1)}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hF : Measurable (A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [ae_iff]
  change dampedDensityScaledCollision C b T ρ p A = 0
  rw [← lintegral_indicator_one hA,dampedDensityScaledCollision_lintegral C b T ρ p hF,
    dampedMediumStateCollision_lintegral C b T p hF]
  have hz (v : V) : A.indicator (1 : PhysicalFlightState → ℝ≥0∞) (p.1,(p.2.1,v)) = 0 := by
    apply indicator_of_notMem
    simp [A]
  simp only [hz,lintegral_zero,mul_zero]

theorem physicalWaitingKernel_ae_cone (C : ℝ≥0) (p : PhysicalFlightState) (hp : ‖p.2.2‖ ≤ 6) :
    ∀ᵐ q ∂physicalWaitingKernel C p, boundedFlightCone p q := by
  let A : Set PhysicalFlightState := {q | ¬boundedFlightCone p q}
  have hA : MeasurableSet A := (boundedFlightCone_measurable p).compl
  have hF : Measurable (A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [ae_iff]
  change physicalWaitingKernel C p A = 0
  rw [← lintegral_indicator_one hA,physicalWaitingKernel_lintegral C p hF]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hz : A.indicator (1 : PhysicalFlightState → ℝ≥0∞) (physicalAdvance p s) = 0 := by
    apply indicator_of_notMem
    exact fun h => h (boundedFlightCone_step hs hp hp)
  rw [hz,mul_zero]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_BeamNormalCharacteristicIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A density-scaled normal-angle beam source with its exact loss complement -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem scaledBeamNormalKernel_apply (b : BeamCoefficients) (ρ : ℝ) (z : CharacteristicPhase) :
    scaledBeamNormalKernel b ρ z = ENNReal.ofReal ρ • beamNormalCharacteristicKernel b z := by
  rw [scaledBeamNormalKernel,Kernel.withDensity_apply _ (by fun_prop),withDensity_const]

theorem beamNormalRetainedKernel_lintegral (b : BeamCoefficients) (ρ C : ℝ)
    (z : CharacteristicPhase) {f : CharacteristicPhase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂beamNormalRetainedKernel b ρ C z) =
      ENNReal.ofReal ρ*(∫⁻ y, f y ∂beamNormalCharacteristicKernel b z)+
        ENNReal.ofReal (C-ρ*characteristicBeamFrequency b z)*f z := by
  rw [beamNormalRetainedKernel,positiveSourceKernel_one_lintegral _
    (r := fun z => C-ρ*characteristicBeamFrequency b z)
    (measurable_const.sub (measurable_const.mul (characteristicBeamFrequency_measurable b))) z hf,
    scaledBeamNormalKernel_apply,lintegral_smul_measure,smul_eq_mul]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact identification of physical angular histories in characteristic coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem beamNormalCharacteristicKernel_eq (b : BeamCoefficients) (endTime : ℝ)
    (z : CharacteristicPhase) (hp : 0 ≤ b.plusDensity (characteristicBeamPoint z))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint z)) :
    beamNormalCharacteristicKernel b z = beamCharacteristicKernel b endTime z := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hj : Measurable (fun v => f (characteristicBeamJump z v)) := by
    apply hf.comp
    unfold characteristicBeamJump
    fun_prop
  rw [beamNormalCharacteristicKernel_lintegral b z hf,
    normalGain_beam_projection b (characteristicBeamPoint z) z.2.2 hp hm,
    lintegral_add_measure,lintegral_smul_measure,lintegral_smul_measure,smul_eq_mul,
    smul_eq_mul,outgoing_lintegral _ _ hj,outgoing_lintegral _ _ hj,
    beamCharacteristicKernel_lintegral b endTime z hf]
  unfold mediumMarkedRate markedRate markedChild
  norm_num
  rw [sphereProbability,lintegral_smul_measure,lintegral_smul_measure,smul_eq_mul,smul_eq_mul]
  simp only [mul_assoc]
  simp only [ENNReal.ofReal_mul (p := (4:ℝ)) (q := Real.pi) (by norm_num),
    ENNReal.ofReal_ofNat]

theorem beamNormalRetainedKernel_eq_scaled {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (endTime : ℝ) (ρ : ℝ≥0) (z : CharacteristicPhase)
    (hp : 0 ≤ b.plusDensity (characteristicBeamPoint z))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint z))
    (hf : characteristicBeamFrequency b z ≤ (referenceClock:ℝ)) :
    beamNormalRetainedKernel b ρ (ρ*C) z = densityScaledCharacteristicKernel C b endTime ρ z := by
  rw [densityScaledCharacteristicKernel_projection hC b endTime ρ z hf]
  apply Measure.ext_of_lintegral
  intro f hfn
  rw [beamNormalRetainedKernel_lintegral b ρ (ρ*C) z hfn,
    beamNormalCharacteristicKernel_eq b endTime z hp hm,lintegral_add_measure,
    lintegral_smul_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul,smul_eq_mul]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalizedDampedBalance
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The localized normal-angle collision law in physical flight coordinates -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem localizedNormalCollision_eq_restrict {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (ρ : ℝ≥0) (T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) (p : PhysicalFlightState)
    (hz : flightCharacteristicEquiv T p ∈ coldCharacteristicDomain a η l)
    (hp : 0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T p)))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T p)))
    (hf : characteristicBeamFrequency b (flightCharacteristicEquiv T p) ≤ (referenceClock:ℝ)) :
    localizedNormalCollision b ρ (ρ*C) T a η l hΩ p =
      (dampedDensityScaledCollision C b T ρ p).restrict ((flightCharacteristicEquiv T) ⁻¹' Ω) := by
  classical
  apply Measure.ext_of_lintegral
  intro f hfn
  let e := flightCharacteristicEquiv T
  rw [localizedNormalCollision,transportedKernel_lintegral _ _ p hfn,
    localizedNormalBeamKernel,Kernel.piecewise_apply,ite_eq_left hz,Kernel.restrict_apply,
    beamNormalRetainedKernel_eq_scaled hC b T ρ (e p) hp hm hf]
  have he := congrArg (fun K : Kernel PhysicalFlightState PhysicalFlightState => K p)
    (transportedKernel_restrict e (densityScaledCharacteristicKernel C b T ρ) hΩ)
  rw [← dampedDensityScaledCollision_transport] at he
  change (∫⁻ y in Ω, f (e.symm y) ∂densityScaledCharacteristicKernel C b T ρ (e p)) =
    ∫⁻ x, f x ∂((dampedDensityScaledCollision C b T ρ).restrict (e.measurable hΩ)) p
  rw [← he,transportedKernel_lintegral _ _ p hfn]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite bounded physical histories are dominated by the localized actual angular histories -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem boundedCollision_le_localized {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (ρ : ℝ≥0) (T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    {p q : PhysicalFlightState} (hq : boundedFlightCone p q)
    (hΩcone : ∀ r, boundedFlightCone p r → flightCharacteristicEquiv T r ∈ Ω)
    (hz : flightCharacteristicEquiv T q ∈ coldCharacteristicDomain a η l)
    (hp : 0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)))
    (hf : characteristicBeamFrequency b (flightCharacteristicEquiv T q) ≤ (referenceClock:ℝ)) :
    (dampedDensityScaledCollision C b T ρ q).restrict mediumVelocityBox ≤
      localizedNormalCollision b ρ (ρ*C) T a η l hΩ q := by
  rw [localizedNormalCollision_eq_restrict hC b ρ T a η l hΩ q hz hp hm hf]
  apply Measure.restrict_mono_ae
  filter_upwards [dampedDensityScaledCollision_ae_fixed C b T ρ q] with r hr
  intro hv
  apply hΩcone r
  exact ⟨hr.1 ▸ hq.1,hr.1 ▸ hq.2.1,hv,by rw [hr.1,hr.2]; exact hq.2.2.2⟩

theorem boundedHistory_le_localized {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (ρ : ℝ≥0) (T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    (p : PhysicalFlightState) (ht : 0 ≤ p.1) (hv : ‖p.2.2‖ ≤ 6)
    (hΩcone : ∀ q, boundedFlightCone p q → flightCharacteristicEquiv T q ∈ Ω)
    (hlocal : ∀ q, boundedFlightCone p q →
      flightCharacteristicEquiv T q ∈ coldCharacteristicDomain a η l ∧
      0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)) ∧
      0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)) ∧
      characteristicBeamFrequency b (flightCharacteristicEquiv T q) ≤ (referenceClock:ℝ))
    (n : ℕ) :
    ((dampedBoundedDensityScaledEvent C b T ρ)^n) p ≤
      ((localizedNormalPhysicalEvent b ρ (ρ*C) T a η l hΩ)^n) p := by
  apply kernel_pow_le_on_invariant _ _ {q | boundedFlightCone p q} _ _ n p
    (boundedFlightCone_refl ht hv)
  · intro q hq
    filter_upwards [dampedBoundedDensityScaledEvent_ae_cone C b T ρ q hq.2.2.1] with r hr
    exact boundedFlightCone_trans hq hr
  · intro q hq
    unfold dampedBoundedDensityScaledEvent dampedDensityScaledEventKernel localizedNormalPhysicalEvent
    rw [← Kernel.comp_restrict,← NNReal.coe_mul,Real.toNNReal_coe]
    apply KernelHistoryOrder.measure_comp_mono_ae (hμ := le_rfl)
    filter_upwards [physicalWaitingKernel_ae_cone (ρ*C) q hq.2.2.1] with r hr
    have hpr := boundedFlightCone_trans hq hr
    obtain ⟨hz,hp,hm,hf⟩ := hlocal r hpr
    exact boundedCollision_le_localized hC b ρ T a η l hΩ hpr hΩcone hz hp hm hf

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedEntryPortion
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Every nonempty physical history strictly advances collision time -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaledEvent_ae_strict_time (C : ℝ≥0) (b : BeamCoefficients)
    (T : ℝ) (ρ : ℝ≥0) (p : PhysicalFlightState) :
    ∀ᵐ q ∂dampedDensityScaledEventKernel C b T ρ p, 0 ≤ q.1 ∧ q.1 < p.1 := by
  let A : Set PhysicalFlightState := {q | ¬(0 ≤ q.1 ∧ q.1 < p.1)}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hF : Measurable (A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [ae_iff]
  change dampedDensityScaledEventKernel C b T ρ p A = 0
  rw [← lintegral_indicator_one hA,dampedDensityScaledEventKernel,Kernel.lintegral_comp _ _ _ hF,
    physicalWaitingKernel_lintegral (ρ*C) p hF.lintegral_kernel]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [dampedDensityScaledCollision_lintegral _ _ _ _ _ hF,
    dampedMediumStateCollision_lintegral _ _ _ _ hF]
  have hz (v : V) : A.indicator (1 : PhysicalFlightState → ℝ≥0∞)
      ((physicalAdvance p s).1,((physicalAdvance p s).2.1,v)) = 0 := by
    apply indicator_of_notMem
    exact fun h => h ⟨sub_nonneg.mpr hs.2,sub_lt_self _ hs.1⟩
  simp only [hz,lintegral_zero,mul_zero,Pi.zero_apply]

theorem dampedBoundedDensityScaledEvent_ae_time_window (C : ℝ≥0) (b : BeamCoefficients)
    (T : ℝ) (ρ : ℝ≥0) {p q : PhysicalFlightState} (hq : boundedFlightCone p q) :
    ∀ᵐ r ∂dampedBoundedDensityScaledEvent C b T ρ q, T-p.1 < T-r.1 ∧ T-r.1 ≤ T := by
  change ∀ᵐ r ∂(dampedDensityScaledEventKernel C b T ρ q).restrict mediumVelocityBox, _
  filter_upwards [ae_restrict_of_ae (dampedDensityScaledEvent_ae_strict_time C b T ρ q)] with r hr
  exact ⟨sub_lt_sub_left (hr.2.trans_le hq.2.1) T,sub_le_self _ hr.1⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FlightConeLocalization
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite-speed history stays in the physical cutoff core -/

noncomputable section

open Set
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem boundedFlightCone_characteristic {t₀ Δ : ℝ} {x v : V} {q : PhysicalFlightState}
    (hq : boundedFlightCone (Δ,(x,v)) q) :
    let z := flightCharacteristicEquiv (t₀+Δ) q
    z.1 ∈ Icc t₀ (t₀+Δ) ∧ ‖z.2.2‖ ≤ 6 ∧
      ‖z.2.1+t₀ • z.2.2-x‖ ≤ 12*Δ ∧ ‖q.2.1-x‖ ≤ 6*Δ := by
  have hd : 0 ≤ Δ-q.1 := sub_nonneg.mpr hq.2.1
  have hd' : Δ-q.1 ≤ Δ := sub_le_self _ hq.1
  have hpos : 0 ≤ Δ := hq.1.trans hq.2.1
  refine ⟨⟨?_,?_⟩,hq.2.2.1,?_,?_⟩
  · change t₀ ≤ t₀+Δ-q.1
    linarith
  · change t₀+Δ-q.1 ≤ t₀+Δ
    linarith [hq.1]
  · change ‖(q.2.1-(t₀+Δ-q.1) • q.2.2)+t₀ • q.2.2-x‖ ≤ 12*Δ
    have he : (q.2.1-(t₀+Δ-q.1) • q.2.2)+t₀ • q.2.2-x =
        (q.2.1-x)-(Δ-q.1) • q.2.2 := by module
    rw [he]
    calc
      _ ≤ ‖q.2.1-x‖+‖(Δ-q.1) • q.2.2‖ := norm_sub_le _ _
      _ ≤ 6*(Δ-q.1)+(Δ-q.1)*6 := by
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
        exact add_le_add hq.2.2.2 (mul_le_mul_of_nonneg_left hq.2.2.1 hd)
      _ ≤ 12*Δ := by linarith
  · exact hq.2.2.2.trans (mul_le_mul_of_nonneg_left hd' (by norm_num))

theorem boundedFlightCone_cold_domain {a t₀ Δ η l : ℝ} {x v : V} {q : PhysicalFlightState}
    (ha : a ≤ t₀) (hl : 0 ≤ l)
    (hcut : Real.exp η*l+6*Δ < ‖transverse x‖)
    (hq : boundedFlightCone (Δ,(x,v)) q) :
    flightCharacteristicEquiv (t₀+Δ) q ∈ coldCharacteristicDomain a η l := by
  obtain ⟨ht,_,_,hpos⟩ := boundedFlightCone_characteristic hq
  have htrans : ‖transverse x‖-‖transverse q.2.1‖ ≤ 6*Δ := by
    calc
      _ ≤ ‖transverse x-transverse q.2.1‖ := norm_sub_norm_le _ _
      _ = ‖transverse (x-q.2.1)‖ := by rw [PlaneChart.transverse_sub]
      _ ≤ ‖x-q.2.1‖ := LargeOutput.transverse_norm_le _
      _ = ‖q.2.1-x‖ := norm_sub_rev _ _
      _ ≤ _ := hpos
  have hrad : Real.exp η*l < ‖transverse q.2.1‖ := by linarith
  have hn : 0 < ‖transverse q.2.1‖ := (mul_nonneg (Real.exp_pos η).le hl).trans_lt hrad
  change a ≤ t₀+Δ-q.1 ∧
    0 < ‖transverse ((q.2.1-(t₀+Δ-q.1) • q.2.2)+(t₀+Δ-q.1) • q.2.2)‖ ∧
    Real.exp η*l < ‖transverse ((q.2.1-(t₀+Δ-q.1) • q.2.2)+(t₀+Δ-q.1) • q.2.2)‖
  rw [sub_add_cancel]
  exact ⟨ha.trans ht.1,hn,hrad⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ScaledBlockMass
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Terminal survival and physical positions of density-scaled histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finishFlight_scaled (ρ : ℝ) (hρ : ρ ≠ 0) (x₀ : V) (p : PhysicalFlightState) :
    finishMediumFlight (flightScaleEquiv ρ hρ x₀ p) =
      (ρ • ((finishMediumFlight p).1-x₀),(finishMediumFlight p).2) := by
  apply Prod.ext
  · dsimp [finishMediumFlight,flightScaleEquiv]
    module
  · rfl

theorem finishFlight_scale_inverse (ρ : ℝ) (hρ : ρ ≠ 0) (x₀ : V)
    (p : PhysicalFlightState) :
    (x₀+ρ⁻¹ • (finishMediumFlight (flightScaleEquiv ρ hρ x₀ p)).1,
      (finishMediumFlight (flightScaleEquiv ρ hρ x₀ p)).2) = finishMediumFlight p := by
  rw [finishFlight_scaled,smul_smul,inv_mul_cancel₀ hρ,one_smul]
  simp

theorem clockSurvival_scaled (C : ℝ≥0) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) :
    clockSurvival C (ρ*s) = clockSurvival (Real.toNNReal ρ*C) s := by
  unfold clockSurvival
  congr 2
  rw [NNReal.coe_mul,Real.coe_toNNReal _ hρ.le]
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The displacement target under the local density scale -/

noncomputable section

open Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem scaled_block_target {ρ : ℝ} (hρ : 0 < ρ) (x : V) (Δ κ d : ℝ) (q : V × V) :
    (x+ρ⁻¹ • q.1,q.2) ∈ physicalBlockTarget x Δ κ d ↔
      q ∈ physicalBlockTarget 0 (ρ*Δ) κ d := by
  have he : (x+ρ⁻¹ • q.1)-(x+(κ*Δ) • firstAxis) =
      ρ⁻¹ • (q.1-(κ*(ρ*Δ)) • firstAxis) := by
    rw [smul_sub,smul_smul,show ρ⁻¹*(κ*(ρ*Δ)) = κ*Δ by field_simp [hρ.ne']]
    abel
  change (‖(x+ρ⁻¹ • q.1)-(x+(κ*Δ) • firstAxis)‖ < d*κ*Δ ∧ ‖q.2‖ < 5) ↔
    (‖q.1-(0+(κ*(ρ*Δ)) • firstAxis)‖ < d*κ*(ρ*Δ) ∧ ‖q.2‖ < 5)
  rw [he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hρ,zero_add]
  have hnorm : ρ⁻¹*‖q.1-(κ*(ρ*Δ)) • firstAxis‖ =
      ‖q.1-(κ*(ρ*Δ)) • firstAxis‖/ρ := by ring
  rw [hnorm,div_lt_iff₀ hρ]
  have hprod : d*κ*Δ*ρ = d*κ*(ρ*Δ) := by ring
  rw [hprod]

theorem scaled_block_indicator {ρ : ℝ} (hρ : 0 < ρ) (x : V) (Δ κ d : ℝ) (q : V × V) :
    (physicalBlockTarget x Δ κ d).indicator (1 : V × V → ℝ≥0∞) (x+ρ⁻¹ • q.1,q.2) =
      (physicalBlockTarget 0 (ρ*Δ) κ d).indicator 1 q := by
  by_cases hq : q ∈ physicalBlockTarget 0 (ρ*Δ) κ d
  · simp [hq,(scaled_block_target hρ x Δ κ d q).mpr hq]
  · simp [hq,show (x+ρ⁻¹ • q.1,q.2) ∉ physicalBlockTarget x Δ κ d from
      fun h => hq ((scaled_block_target hρ x Δ κ d q).mp h)]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedLateBoxPhysicalBlock
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Scaled finite histories and terminal survival at the enlarged damping -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaled_bounded_history_map (C : ℝ≥0) (b : BeamCoefficients)
    {ρ : ℝ} (hρ : 0 < ρ) (t₀ endTime : ℝ) (x₀ : V) (n : ℕ)
    (p : PhysicalFlightState) {T : ℝ} (hT : ρ*p.1 ≤ T) :
    (((dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ))^n) p).map
      (flightScaleEquiv ρ hρ.ne' x₀) =
      ((dampedBoundedEventKernel C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)) T)^n)
        (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  rw [dampedBoundedDensityScaledEvent_pow_map C b hρ t₀ endTime x₀ n p,
    damped_boundedMediumEventKernel_pow_eq_physical C _ _ _ _ hT]

theorem dampedDensityScaled_endpoint_integral (C : ℝ≥0) (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : ρ*p.1 ≤ T)
    {F : V × V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, clockSurvival (Real.toNNReal ρ*C) q.1 * F (finishMediumFlight q)
      ∂((dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ))^n) p) =
    ∫⁻ q, clockSurvival C q.1 *
      F (x₀+ρ⁻¹ • (finishMediumFlight q).1,(finishMediumFlight q).2)
      ∂((dampedBoundedEventKernel C (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)) T)^n)
        (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  let g : PhysicalFlightState → ℝ≥0∞ := fun q => clockSurvival C q.1 *
    F (x₀+ρ⁻¹ • (finishMediumFlight q).1,(finishMediumFlight q).2)
  have hg : Measurable g := by
    apply (show Measurable (fun q : PhysicalFlightState => clockSurvival C q.1) by
      unfold clockSurvival; fun_prop).mul
    exact hF.comp (by unfold finishMediumFlight; fun_prop)
  have H := congrArg (fun μ : Measure PhysicalFlightState => ∫⁻ q, g q ∂μ)
    (dampedDensityScaled_bounded_history_map C b hρ t₀ endTime x₀ n p hT)
  rw [lintegral_map hg (flightScaleEquiv ρ hρ.ne' x₀).measurable] at H
  calc
    _ = ∫⁻ q, g (flightScaleEquiv ρ hρ.ne' x₀ q)
        ∂((dampedBoundedDensityScaledEvent C b endTime (Real.toNNReal ρ))^n) p := by
      apply lintegral_congr
      intro q
      dsimp only [g]
      rw [finishFlight_scale_inverse]
      change _ = clockSurvival C (ρ*q.1)*F (finishMediumFlight q)
      rw [clockSurvival_scaled C hρ]
    _ = _ := H

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact physical-time mass of each finite normalized branching block -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaledBlockMass_eq (C : ℝ≥0) (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ : ℝ) (x : V) (Δ : ℝ) (v : RetainedState) (κ d : ℝ) (N : ℕ) {T : ℝ}
    (hT : ρ*Δ ≤ T) :
    dampedDensityScaledBlockMass C b (t₀+Δ) ρ x Δ v κ d N =
      dampedBoundedBlockMass C (b.normalized ρ t₀ x) (ρ*Δ) T (ρ*Δ,(0,v)) κ d N := by
  unfold dampedDensityScaledBlockMass dampedBoundedBlockMass
  apply Finset.sum_congr rfl
  intro n _hn
  have H := dampedDensityScaled_endpoint_integral C b hρ t₀ (t₀+Δ) x n
    (Δ,(x,(v : V))) hT
    (F := (physicalBlockTarget x Δ κ d).indicator (1 : V × V → ℝ≥0∞))
    (measurable_const.indicator (physicalBlockTarget_measurable _ _ _ _))
  rw [H]
  have ht : ρ*(t₀+Δ-t₀) = ρ*Δ := by ring
  have hp : flightScaleEquiv ρ hρ.ne' x (Δ,(x,(v : V))) = (ρ*Δ,(0,(v : V))) := by
    simp [flightScaleEquiv]
  rw [ht,hp]
  simp_rw [scaled_block_indicator hρ x Δ κ d]
  exact (dampedBoundedWord_integral C (b.normalized ρ t₀ x) (ρ*Δ) T
    (dampedMediumFlightSeed_measurable C (measurable_const.indicator
      (physicalBlockTarget_measurable 0 (ρ*Δ) κ d))) n
        (embedFlightState (ρ*Δ,(0,v)))).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LateBoxCommonDamping
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Physical branching growth for a whole interval of durations -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lateBox_duration_window {κ d t K A₀ Δ : ℝ}
    (hκ : 0 < κ) (ht : 0 < t) (hd : d ≤ 1/2) (hK : 0 < K) (hA₀ : 0 < A₀)
    {p : V × V} (hp : p ∈ lateBox κ d t)
    (hlo : (8*κ*A₀/K)*t ≤ Δ) (hhi : Δ ≤ (16*κ*A₀/K)*t) :
    (K/(4*‖transverse p.1‖))*Δ ∈ Icc A₀ (8*A₀) := by
  have hrad : 0 < ‖transverse p.1‖ := by
    obtain ⟨h,_,_⟩ := lateBox_radius_bounds hκ ht hp
    have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ ht).le
    nlinarith
  have hρ : 0 ≤ K/(4*‖transverse p.1‖) := by positivity
  have hb := lateBox_block_duration hκ ht hd hK hA₀ hp
  constructor
  · exact hb.1.trans (mul_le_mul_of_nonneg_left hlo hρ)
  · have hh := mul_le_mul_of_nonneg_left hhi hρ
    have he : (16*κ*A₀/K)*t = 2*((8*κ*A₀/K)*t) := by ring
    rw [he,mul_left_comm] at hh
    exact hh.trans (by nlinarith [hb.2])

theorem lateBox_damped_duration_growth {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/2) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ Dmax : ℝ≥0, ∃ N : ℕ, ∃ ε γ₀ : ℝ,
      0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ D : ℝ≥0, referenceClock ≤ D → D ≤ Dmax →
      ∀ {θ η α γ K t Δ : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*(8*A₀) ≤ ε*K → 0 < t →
      (8*κ*A₀/K)*t ≤ Δ → Δ ≤ (16*κ*A₀/K)*t →
      ∀ (x : V) (v : RetainedState), (x,(v:V)) ∈ lateBox κ d t →
      (6:ℝ≥0∞) < dampedDensityScaledBlockMass D
        (GeometricBackground.beamCoefficients hθ hα hγ η ‖transverse x‖)
        (t+Δ) (K/(4*‖transverse x‖)) x Δ v κ d N := by
  have hM : 1 ≤ 4/κ := (le_div_iff₀ hκ).mpr (by linarith)
  obtain ⟨A₀,hA₀,hblock⟩ := GeometricBackground.geometric_damped_bounded_block_growth
    hd (by linarith) hκ hκsmall hg hM
  refine ⟨A₀,hA₀,?_⟩
  intro Dmax
  obtain ⟨N,ε,γ₀,hε,hεsmall,hγ₀,hgrowth⟩ := hblock (8*A₀) (by linarith) Dmax
  refine ⟨N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro D hD hDmax θ η α γ K t Δ hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge ht hlo hhi x v hp
  have hs := lateBox_geometric_scale hκ hκsmall.le hdsmall ht hp
  have hr := hs.1
  have hρ : 0 < K/(4*‖transverse x‖) := by positivity
  have hA := lateBox_duration_window hκ ht hdsmall hK hA₀ hp hlo hhi
  rw [dampedDensityScaledBlockMass_eq D _ hρ t x Δ v κ d N hA.2]
  exact hgrowth D hD hDmax hθ hη hηsmall hs.1 hα hαsmall hγ hγsmall hK hKlarge
    ht.le hs.2.1 hA x v rfl hs.2.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalizedBlockComparison
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Retaining the actual open-left collision-time window in physical histories -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem localizedNormalWindowEvent_transport (b : BeamCoefficients) (ρ : ℝ)
    (C : ℝ≥0) (T a η l s : ℝ) {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) :
    localizedNormalWindowEvent b ρ C T a η l s hΩ =
      transportedKernel (flightCharacteristicEquiv T)
        (((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s T))) ∘ₖ
            WeakTime.residenceKernel C T) := by
  rw [transportedKernel_compKernel,transportedKernel_restrict,
    ← physicalWaitingKernel_eq_transport,Kernel.comp_restrict]
  simp only [localizedNormalWindowEvent,localizedNormalPhysicalEvent,localizedNormalCollision,
    Real.toNNReal_coe]
  rfl

theorem boundedHistory_le_localized_window {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (ρ : ℝ≥0) (T a η l : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    (p : PhysicalFlightState) (ht : 0 ≤ p.1) (hv : ‖p.2.2‖ ≤ 6)
    (hΩcone : ∀ q, boundedFlightCone p q → flightCharacteristicEquiv T q ∈ Ω)
    (hlocal : ∀ q, boundedFlightCone p q →
      flightCharacteristicEquiv T q ∈ coldCharacteristicDomain a η l ∧
      0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)) ∧
      0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)) ∧
      characteristicBeamFrequency b (flightCharacteristicEquiv T q) ≤ (referenceClock:ℝ))
    (n : ℕ) :
    ((dampedBoundedDensityScaledEvent C b T ρ)^n) p ≤
      ((localizedNormalWindowEvent b ρ (ρ*C) T a η l (T-p.1) hΩ)^n) p := by
  apply kernel_pow_le_on_invariant _ _ {q | boundedFlightCone p q} _ _ n p
    (boundedFlightCone_refl ht hv)
  · intro q hq
    filter_upwards [dampedBoundedDensityScaledEvent_ae_cone C b T ρ q hq.2.2.1] with r hr
    exact boundedFlightCone_trans hq hr
  · intro q hq
    have he : dampedBoundedDensityScaledEvent C b T ρ q ≤
        localizedNormalPhysicalEvent b ρ (ρ*C) T a η l hΩ q := by
      simpa only [pow_one] using boundedHistory_le_localized hC b ρ T a η l hΩ q hq.1 hq.2.2.1
        (fun r hr => hΩcone r (boundedFlightCone_trans hq hr))
        (fun r hr => hlocal r (boundedFlightCone_trans hq hr)) 1
    have htwin : ∀ᵐ r ∂dampedBoundedDensityScaledEvent C b T ρ q,
        r ∈ physicalCollisionWindow (T-p.1) T :=
      dampedBoundedDensityScaledEvent_ae_time_window C b T ρ hq
    calc
      _ = (dampedBoundedDensityScaledEvent C b T ρ q).restrict
          (physicalCollisionWindow (T-p.1) T) := (Measure.restrict_eq_self_of_ae_mem htwin).symm
      _ ≤ _ := Measure.restrict_mono_measure he _

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Physical normal-angle histories end at the hot trace's characteristic endpoint -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem localizedNormalWindowEvent_pow_transport (b : BeamCoefficients) (ρ : ℝ)
    (C : ℝ≥0) (T a η l s : ℝ) {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) (n : ℕ) :
    (localizedNormalWindowEvent b ρ C T a η l s hΩ)^n =
      transportedKernel (flightCharacteristicEquiv T)
        ((((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Set.Ioc s T))) ∘ₖ
            WeakTime.residenceKernel C T)^n) := by
  rw [transportedKernel_pow,← localizedNormalWindowEvent_transport]

theorem localizedNormal_endpoint_characteristic (b : BeamCoefficients) (ρ : ℝ)
    (C : ℝ≥0) (T a η l s : ℝ) {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    (n : ℕ) (p : PhysicalFlightState) {f : V × V → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ q, clockSurvival C q.1*f (finishMediumFlight q)
      ∂((localizedNormalWindowEvent b ρ C T a η l s hΩ)^n) p) =
    ∫⁻ q, f (EuclideanFlight.flight T q)
      ∂(WeakTime.phaseEndpointKernel C T ∘ₖ
        ((((localizedNormalBeamKernel b ρ C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Set.Ioc s T))) ∘ₖ
            WeakTime.residenceKernel C T)^n)) (flightCharacteristicEquiv T p) := by
  have hg : Measurable (fun z => f (EuclideanFlight.flight T z)) :=
    hf.comp (EuclideanFlight.flight_measurePreserving T).measurable
  have hw : Measurable (fun q : PhysicalFlightState => clockSurvival C q.1*f (finishMediumFlight q)) :=
    (show Measurable (fun q : PhysicalFlightState => clockSurvival C q.1) by
      unfold clockSurvival; fun_prop).mul (hf.comp finishMediumFlight_measurable)
  rw [localizedNormalWindowEvent_pow_transport,transportedKernel_lintegral _ _ _ hw,
    Kernel.lintegral_comp _ _ _ hg]
  apply lintegral_congr
  intro z
  rw [WeakTime.phaseEndpointKernel_lintegral _ _ _ hg,physical_terminal_characteristic T C f]
  simp only [MeasurableEquiv.apply_symm_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The finite physical branching block lies below the actual angular endpoint histories -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalBlock_le_localized {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (ρ : ℝ≥0) (s Δ a η l κ d : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω) (x : V) (v : RetainedState)
    (hΔ : 0 ≤ Δ) (hv : ‖(v:V)‖ ≤ 6) (hp : (x,(v:V)) ∈ lateBox κ d s)
    (hΩcone : ∀ q, boundedFlightCone (Δ,(x,(v:V))) q → flightCharacteristicEquiv (s+Δ) q ∈ Ω)
    (hlocal : ∀ q, boundedFlightCone (Δ,(x,(v:V))) q →
      flightCharacteristicEquiv (s+Δ) q ∈ coldCharacteristicDomain a η l ∧
      0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv (s+Δ) q)) ∧
      0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv (s+Δ) q)) ∧
      characteristicBeamFrequency b (flightCharacteristicEquiv (s+Δ) q) ≤ (referenceClock:ℝ))
    (N : ℕ) :
    dampedDensityScaledBlockMass C b (s+Δ) ρ x Δ v κ d N ≤
      localizedHistoryBlockMass b ρ (ρ*C) (s+Δ) a η l s hΩ (lateBox κ d (s+Δ)) N
        (flightCharacteristicEquiv (s+Δ) (Δ,(x,(v:V)))) := by
  let A := lateBox κ d (s+Δ)
  have hA : MeasurableSet A := lateBox_measurable _ _ _
  have hf : Measurable (A.indicator (1 : V × V → ℝ≥0∞)) := measurable_const.indicator hA
  unfold dampedDensityScaledBlockMass localizedHistoryBlockMass
  simp only [Real.toNNReal_coe]
  apply Finset.sum_le_sum
  intro n _hn
  have hle := boundedHistory_le_localized_window hC b ρ (s+Δ) a η l hΩ
    (Δ,(x,(v:V))) hΔ hv hΩcone hlocal n
  have htime : (s+Δ)-Δ = s := by ring
  rw [htime] at hle
  calc
    _ ≤ ∫⁻ q, clockSurvival (ρ*C) q.1*A.indicator 1 (finishMediumFlight q)
        ∂((dampedBoundedDensityScaledEvent C b (s+Δ) ρ)^n) (Δ,(x,(v:V))) := by
      apply lintegral_mono
      intro q
      dsimp only
      gcongr
      exact fun _ hy => physicalBlockTarget_subset_lateBox hp hy
    _ ≤ ∫⁻ q, clockSurvival (ρ*C) q.1*A.indicator 1 (finishMediumFlight q)
        ∂((localizedNormalWindowEvent b ρ (ρ*C) (s+Δ) a η l s hΩ)^n) (Δ,(x,(v:V))) :=
      lintegral_mono' hle le_rfl
    _ = _ := by
      simpa only [NNReal.coe_mul] using
        localizedNormal_endpoint_characteristic b ρ (ρ*C) (s+Δ) a η l s hΩ n (Δ,(x,(v:V))) hf

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricLocalizedEntry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local density normalization cancels from the actual beam measure and frequency -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem scaled_beamDensity {θ η α γ r s K σ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (p : ℝ × Velocity) :
    (K/(4*r))*beamDensity θ η α γ r σ p =
      (K/(4*s))*beamDensity θ η α γ s σ p := by
  unfold beamDensity
  field_simp

theorem scaled_beamMeasure {θ K α γ r s : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr : 0 < r) (hs : 0 < s) (η : ℝ) (p : ℝ × Velocity) :
    ENNReal.ofReal (K/(4*r)) • beamMeasure (beamCoefficients hθ hα hγ η r) p =
      ENNReal.ofReal (K/(4*s)) • beamMeasure (beamCoefficients hθ hα hγ η s) p := by
  simp only [beamMeasure,beamCoefficients,smul_add,smul_smul]
  rw [← ENNReal.ofReal_mul (show 0 ≤ K/(4*r) by positivity),
    ← ENNReal.ofReal_mul (show 0 ≤ K/(4*r) by positivity),
    ← ENNReal.ofReal_mul (show 0 ≤ K/(4*s) by positivity),
    ← ENNReal.ofReal_mul (show 0 ≤ K/(4*s) by positivity),
    scaled_beamDensity hr hs,scaled_beamDensity hr hs]

theorem scaled_characteristicBeamFrequency {θ α γ r s K : ℝ}
    (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r) (hs : 0 < s)
    (η : ℝ) (z : EuclideanFlight.CharacteristicPhase) :
    (K/(4*r))*characteristicBeamFrequency (beamCoefficients hθ hα hγ η r) z =
      (K/(4*s))*characteristicBeamFrequency (beamCoefficients hθ hα hγ η s) z := by
  unfold characteristicBeamFrequency mediumFrequency
  simp only [beamCoefficients]
  calc
    _ = 2*Real.pi *
        (((K/(4*r))*beamDensity θ η α γ r 1 (characteristicBeamPoint z))*
            ‖z.2.2-beamVelocity θ η α γ 1 (characteristicBeamPoint z)‖+
         ((K/(4*r))*beamDensity θ η α γ r (-1) (characteristicBeamPoint z))*
            ‖z.2.2-beamVelocity θ η α γ (-1) (characteristicBeamPoint z)‖) := by ring
    _ = _ := by rw [scaled_beamDensity hr hs,scaled_beamDensity hr hs]; ring

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Actual geometric coefficients on the cone visited by a finite history -/

noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem boundedFlightCone_mem_historyCore {t₀ Δ : ℝ} {x v : V}
    {q : PhysicalFlightState} (hq : boundedFlightCone (Δ,(x,v)) q) :
    flightCharacteristicEquiv (t₀+Δ) q ∈ characteristicHistoryCore t₀ (12*Δ) x := by
  obtain ⟨_,hv,hx,_⟩ := boundedFlightCone_characteristic hq
  exact ⟨hx,hv⟩

end BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_history_cone_conditions {ε M : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1/4) (hM : 1 ≤ M) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ {θ η r α γ t₀ Δ a l : ℝ},
      (hθ : 0 < θ) → 0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 ≤ t₀ → t₀ ≤ M*r/2 → 6*Δ ≤ (ε/20)*r → a ≤ t₀ → 0 ≤ l →
      Real.exp η*l+6*Δ < r → ∀ x v : Velocity,
      ‖transverse x‖ = r → |axial x| ≤ M*r/2 →
      ∀ q : PhysicalFlightState, boundedFlightCone (Δ,(x,v)) q →
        let z := flightCharacteristicEquiv (t₀+Δ) q;
        z ∈ coldCharacteristicDomain a η l ∧
        0 ≤ (beamCoefficients hθ hα hγ η r).plusDensity (characteristicBeamPoint z) ∧
        0 ≤ (beamCoefficients hθ hα hγ η r).minusDensity (characteristicBeamPoint z) ∧
        characteristicBeamFrequency (beamCoefficients hθ hα hγ η r) z ≤ (referenceClock:ℝ) := by
  obtain ⟨γ₀,hγ₀,hnear⟩ := beam_near_on_cylinder hε (by linarith) hM
  refine ⟨γ₀,hγ₀,?_⟩
  intro θ η r α γ t₀ Δ a l hθ hη hηsmall hr hα hαsmall hγ hγsmall ht₀ ht₀M hshort ha hl hcut x v hx hax q hq
  let z := flightCharacteristicEquiv (t₀+Δ) q
  have ht := (boundedFlightCone_characteristic (t₀ := t₀) hq).1
  have hdist := (boundedFlightCone_characteristic (t₀ := t₀) hq).2.2.2
  have hpnt : characteristicBeamPoint z = (z.1,q.2.1) := by
    change (t₀+Δ-q.1,(q.2.1-(t₀+Δ-q.1) • q.2.2)+(t₀+Δ-q.1) • q.2.2) = _
    rw [sub_add_cancel]
    rfl
  have hn := hnear hθ hη hηsmall hr hα hαsmall hγ hγsmall (by norm_num : (0:ℝ)<1)
    ht₀ ht₀M (by simpa only [div_one] using hshort) x hx hax (z.1,q.2.1)
    (by simpa only [div_one] using ht) (by simpa only [div_one] using hdist)
  refine ⟨boundedFlightCone_cold_domain ha hl (hx ▸ hcut) hq,?_,?_,?_⟩
  · exact beamDensity_nonneg hθ hα hγ hr.le η 1 _
  · exact beamDensity_nonneg hθ hα hγ hr.le η (-1) _
  · have hf := hn.frequency_margin hεsmall (v := z.2.2) (by
      exact hq.2.2.1.trans (by norm_num))
    change mediumFrequency z.2.2 _ _ _ _ ≤ _
    rw [hpnt]
    exact hf.2.trans (by change 45*Real.pi ≤ 48*Real.pi; nlinarith [Real.pi_pos])

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The physical normal-angle source is independent of its reference density scale -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem scaledBeamNormalKernel_independent {θ K α γ r s : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr : 0 < r) (hs : 0 < s) (η : ℝ) :
    scaledBeamNormalKernel (beamCoefficients hθ hα hγ η r) (K/(4*r)) =
      scaledBeamNormalKernel (beamCoefficients hθ hα hγ η s) (K/(4*s)) := by
  apply Kernel.ext_fun
  intro z f hf
  rw [scaledBeamNormalKernel_apply,scaledBeamNormalKernel_apply,
    lintegral_smul_measure,lintegral_smul_measure,smul_eq_mul,smul_eq_mul,
    beamNormalCharacteristicKernel_lintegral _ z hf,
    beamNormalCharacteristicKernel_lintegral _ z hf]
  have hm : ENNReal.ofReal (K/(4*r)) •
      beamPartnerKernel (beamCoefficients hθ hα hγ η r) (characteristicBeamPoint z) =
      ENNReal.ofReal (K/(4*s)) •
      beamPartnerKernel (beamCoefficients hθ hα hγ η s) (characteristicBeamPoint z) := by
    rw [beamPartnerKernel_apply,beamPartnerKernel_apply]
    exact scaled_beamMeasure hθ hK hα hγ hr hs η _
  have h := normalGainKernel_smul_eq_of_measure_smul_eq _ _
    (characteristicBeamPoint z) (characteristicBeamPoint z) z.2.2 _ _ hm
  have H := congrArg (fun μ : Measure Velocity =>
    ∫⁻ v, f (characteristicBeamJump z v) ∂μ) h
  simpa only [lintegral_smul_measure,smul_eq_mul] using H

theorem beamNormalRetainedKernel_independent {θ K α γ r s : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr : 0 < r) (hs : 0 < s) (η C : ℝ) :
    beamNormalRetainedKernel (beamCoefficients hθ hα hγ η r) (K/(4*r)) C =
      beamNormalRetainedKernel (beamCoefficients hθ hα hγ η s) (K/(4*s)) C := by
  have hk := scaledBeamNormalKernel_independent hθ hK hα hγ hr hs η
  apply Kernel.ext_fun
  intro z f hf
  have H := congrArg (fun Q : Kernel EuclideanFlight.CharacteristicPhase EuclideanFlight.CharacteristicPhase =>
    ∫⁻ y, f y ∂Q z) hk
  simp only [scaledBeamNormalKernel_apply,lintegral_smul_measure,smul_eq_mul] at H
  rw [beamNormalRetainedKernel_lintegral _ _ _ z hf,
    beamNormalRetainedKernel_lintegral _ _ _ z hf,H,
    scaled_characteristicBeamFrequency hθ hα hγ hr hs η z]

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CommonHistoryCore
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All bounded histories in a short late-box window use one characteristic core -/

noncomputable section
open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem characteristicHistoryCore_shift {s b R : ℝ} {x c : V}
    {z : ℝ × WeakTime.Phase} (hs : b ≤ s)
    (hz : z ∈ characteristicHistoryCore s R x) :
    z ∈ characteristicHistoryCore b (R+‖x-c‖+6*(s-b)) c := by
  refine ⟨?_,hz.2⟩
  have he : z.2.1+b • z.2.2-c = (z.2.1+s • z.2.2-x)+(x-c)+(b-s) • z.2.2 := by module
  rw [he]
  calc
    _ ≤ ‖z.2.1+s • z.2.2-x‖+‖x-c‖+‖(b-s) • z.2.2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ R+‖x-c‖+6*(s-b) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
      nlinarith [hz.1,mul_le_mul_of_nonneg_left hz.2 (sub_nonneg.mpr hs)]

theorem boundedFlightCone_mem_commonCore {κ d b W s Δ : ℝ}
    (hκ : 0 < κ) (hκsmall : κ ≤ 1) (hd : d ≤ 1/32) (hb : 0 < b)
    (hW : W ≤ κ*b/200) (hs : s ∈ Icc b (b+W)) (hΔ : Δ ≤ W)
    {x v : V} (hp : (x,v) ∈ lateBox κ d s)
    {q : PhysicalFlightState} (hq : boundedFlightCone (Δ,(x,v)) q) :
    flightCharacteristicEquiv (s+Δ) q ∈
      characteristicHistoryCore b (κ*b/4) ((κ*b) • firstAxis) := by
  have hspos : 0 < s := hb.trans_le hs.1
  have hshift := characteristicHistoryCore_shift hs.1
    (c := (κ*b) • firstAxis) (boundedFlightCone_mem_historyCore (t₀ := s) hq)
  refine ⟨hshift.1.trans ?_,hshift.2⟩
  have he : x-(κ*b) • firstAxis = (x-(κ*s) • firstAxis)+(κ*(s-b)) • firstAxis := by module
  have hx : ‖x-(κ*b) • firstAxis‖ ≤ d*κ*s+κ*(s-b) := by
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_smul,axis_norms.1,mul_one,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hκ.le (sub_nonneg.mpr hs.1))]
    exact add_le_add hp.1.le le_rfl
  have hkb : κ*b ≤ b := by nlinarith [mul_le_mul_of_nonneg_right hκsmall hb.le]
  have hst : s ≤ 2*b := by linarith [hs.2]
  have hds : d*κ*s ≤ κ*b/16 := by
    have hh := mul_le_mul_of_nonneg_right hd (mul_pos hκ hspos).le
    nlinarith [mul_le_mul_of_nonneg_left hst hκ.le]
  have hkt : κ*(s-b) ≤ W := by
    have hh := mul_le_mul_of_nonneg_right hκsmall (sub_nonneg.mpr hs.1)
    nlinarith [hs.2]
  nlinarith [hs.2,mul_pos hκ hb]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalizedHotMassGrowth
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Localized normal-angle histories use one kernel for every density scale -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem localizedNormalBeamKernel_independent {θ K α γ r s : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr : 0 < r) (hs : 0 < s) (η C a l : ℝ)
    {B : Set EuclideanFlight.CharacteristicPhase} (hB : MeasurableSet B) :
    localizedNormalBeamKernel (beamCoefficients hθ hα hγ η r) (K/(4*r)) C a η l hB =
      localizedNormalBeamKernel (beamCoefficients hθ hα hγ η s) (K/(4*s)) C a η l hB := by
  classical
  exact congrArg (fun Q : Kernel EuclideanFlight.CharacteristicPhase EuclideanFlight.CharacteristicPhase =>
    Kernel.piecewise (coldCharacteristicDomain_measurable a η l) (Q.restrict hB) 0)
    (beamNormalRetainedKernel_independent hθ hK hα hγ hr hs η C)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The finite physical endpoint mass does not depend on its reference density scale -/

noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem localizedHistoryBlockMass_independent {θ K α γ r r' : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr : 0 < r) (hr' : 0 < r') (η C T a l s : ℝ)
    {Ω : Set (ℝ × WeakTime.Phase)} (hΩ : MeasurableSet Ω)
    (A : Set WeakTime.Phase) (N : ℕ) (z : ℝ × WeakTime.Phase) :
    localizedHistoryBlockMass (beamCoefficients hθ hα hγ η r) (K/(4*r)) C T a η l s hΩ A N z =
      localizedHistoryBlockMass (beamCoefficients hθ hα hγ η r') (K/(4*r')) C T a η l s hΩ A N z := by
  unfold localizedHistoryBlockMass
  rw [localizedNormalBeamKernel_independent hθ hK hα hγ hr hr' η C a l hΩ]

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricCommonBlock
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A growing angular-history block with one clock and one core for all starts -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_common_block_growth_q80_oai {d κ : ℝ}
    (hd : 0 < d) (hdsmall : d ≤ 1/32) (hκ : 0 < κ) (hκsmall : κ < 1)
    (hg : (referenceClock:ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ N : ℕ, ∃ ε γ₀ : ℝ,
      0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {θ η α γ K b W s Δ a l : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*(8*A₀) ≤ ε*K → 0 < b → W ≤ κ*b/200 →
      s ∈ Icc b (b+W) → (8*κ*A₀/K)*s ≤ Δ → Δ ≤ (16*κ*A₀/K)*s → Δ ≤ W →
      a ≤ s → 0 ≤ l →
      ∀ (x : V) (v : RetainedState), (x,(v:V)) ∈ lateBox κ d s →
      Real.exp η*l+6*Δ < ‖transverse x‖ →
      (6:ℝ≥0∞) < localizedHistoryBlockMass
        (beamCoefficients hθ hα hγ η (κ*b)) (K/(4*(κ*b)))
        (48*Real.pi*K/(κ*b)) (s+Δ) a η l s
        (characteristicHistoryCore_measurable b (κ*b/4) ((κ*b) • firstAxis))
        (lateBox κ d (s+Δ)) N
        (flightCharacteristicEquiv (s+Δ) (Δ,(x,(v:V)))) := by
  have hdhalf : d ≤ 1/2 := by linarith
  obtain ⟨A₀,hA₀,hblock⟩ := lateBox_damped_duration_growth hd hdhalf hκ hκsmall hg
  obtain ⟨N,ε,γ₁,hε,hεsmall,hγ₁,hgrowth⟩ := hblock (12*referenceClock)
  have hM : 1 ≤ 4/κ := (le_div_iff₀ hκ).mpr (by linarith)
  obtain ⟨γ₂,hγ₂,hcone⟩ := geometric_history_cone_conditions hε hεsmall hM
  refine ⟨A₀,hA₀,N,ε,min γ₁ γ₂,hε,hεsmall,lt_min hγ₁ hγ₂,?_⟩
  intro θ η α γ K b W s Δ a l hθ hη hηsmall hα hαsmall hγ hγsmall hK hKlarge hb hW hs hlo hhi hΔW ha hl x v hp hcut
  let r := ‖transverse x‖
  let D := Real.toNNReal (192*Real.pi*r/(κ*b))
  have hspos : 0 < s := hb.trans_le hs.1
  have hscale := lateBox_geometric_scale hκ hκsmall.le hdhalf hspos hp
  have hr : 0 < r := hscale.1
  have hρ : 0 < K/(4*r) := by positivity
  have hΔ : 0 ≤ Δ := by
    apply le_trans _ hlo
    positivity
  have hdrange := window_damping_range hκ hκsmall.le hb hW hs hdhalf hp
  have hD0 : 0 ≤ 192*Real.pi*r/(κ*b) := referenceClock.property.trans hdrange.1
  have hDlo : referenceClock ≤ D := by
    apply (NNReal.coe_le_coe).mp
    simpa only [D,Real.coe_toNNReal _ hD0] using hdrange.1
  have hDhi : D ≤ 12*referenceClock := by
    apply (NNReal.coe_le_coe).mp
    simpa only [D,Real.coe_toNNReal _ hD0,NNReal.coe_mul,NNReal.coe_ofNat] using hdrange.2
  have hA := lateBox_duration_window hκ hspos hdhalf hK hA₀ hp hlo hhi
  have hshort : 6*Δ ≤ (ε/20)*r := by
    calc
      6*Δ ≤ 6*(8*A₀)/(K/(4*r)) := by
        apply (le_div_iff₀ hρ).mpr
        nlinarith [hA.2]
      _ ≤ _ := cylinder_small_of_density_scale hK hr hKlarge
  have hlocal := hcone hθ hη hηsmall hr hα hαsmall hγ
    (hγsmall.trans (min_le_right _ _)) hspos.le hscale.2.1 hshort ha hl hcut x (v:V) rfl hscale.2.2
  have hcomp := physicalBlock_le_localized hDlo (beamCoefficients hθ hα hγ η r)
    (Real.toNNReal (K/(4*r))) s Δ a η l κ d
    (characteristicHistoryCore_measurable b (κ*b/4) ((κ*b) • firstAxis)) x v hΔ
    ((show ‖(v:V)‖ ≤ 5 by simpa only [referenceRegion,Metric.mem_closedBall,dist_zero_right] using v.property).trans (by norm_num)) hp
    (fun q hq => boundedFlightCone_mem_commonCore hκ hκsmall.le hdsmall hb hW hs hΔW hp hq)
    hlocal N
  have hgr := hgrowth D hDlo hDhi hθ hη hηsmall hα hαsmall hγ
    (hγsmall.trans (min_le_left _ _)) hK hKlarge hspos hlo hhi x v hp
  have hρcoe : (Real.toNNReal (K/(4*r)):ℝ) = K/(4*r) := Real.coe_toNNReal _ hρ.le
  have hDcoe : (D:ℝ) = 192*Real.pi*r/(κ*b) := Real.coe_toNNReal _ hD0
  rw [hρcoe,hDcoe,window_damping_normalization hκ hb hr] at hcomp
  have hh := hgr.trans_le hcomp
  rw [localizedHistoryBlockMass_independent hθ hK.le hα hγ hr (mul_pos hκ hb)] at hh
  exact hh

end BoltzmannNonuniqueness.GeometricBackground

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.GeometricBackground.geometric_common_block_growth_q80_oai := @OAI.BoltzmannNonuniqueness.GeometricBackground.geometric_common_block_growth_q80_oai
