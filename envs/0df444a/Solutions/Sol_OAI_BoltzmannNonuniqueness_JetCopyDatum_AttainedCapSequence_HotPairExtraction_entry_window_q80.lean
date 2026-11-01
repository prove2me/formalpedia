-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.entry_window_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:17:40.158031+00:00
-- url     : https://prove2.me/submissions/2b36837f-d9b9-453f-9f3f-2bbfb64457c7

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotPairExtraction_positive_history_transfer_q80

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.stateKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_pow_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.incomingChart_zero _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.normalChart_zero _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

/-! # Every reference velocity has a robust outgoing direction of small speed -/

noncomputable section

open MeasureTheory Set NormedSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem child_angular_distance (v w n m : V) :
    dist (child v w n) (child v w m) = (‖v-w‖/2)*dist n m := by
  rw [dist_eq_norm,dist_eq_norm]
  have he : child v w n-child v w m = (‖v-w‖/2) • (n-m) := by
    unfold child
    module
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity)]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform angular caps about collision endpoints -/

noncomputable section

open MeasureTheory Set NormedSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem sphereCapMass_pos {r : ℝ} (_hr : 0 < r) : 0 < sphereCapMass r := by
  exact div_pos (by exact_mod_cast Measure.toSphereBallBound_pos 3 r) (by norm_num)

theorem sphere_cap_lower {r : ℝ} (hr : 0 < r) (n : Sphere) :
    sphereCapMass r ≤ sphereProbability.real (Metric.ball n r) := by
  have hv : (volume : Measure V).real (Metric.ball 0 1) = 4/3*Real.pi := by
    rw [Measure.real,EuclideanSpace.volume_ball_fin_three]
    norm_num [ENNReal.toReal_ofReal,Real.pi_pos.le]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have h := Measure.toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball
    (volume : Measure V) hr n
  simp only [finrank_euclideanSpace,Fintype.card_fin,hv] at h
  change (Measure.toSphereBallBound 3 r : ℝ)*(4/3*Real.pi) ≤ sphereArea.real (Metric.ball n r) at h
  rw [Measure.real,sphereProbability,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_inv,ENNReal.toReal_ofReal (by positivity)]
  change (Measure.toSphereBallBound 3 r : ℝ)/3 ≤
    (4*Real.pi)⁻¹*sphereArea.real (Metric.ball n r)
  rw [inv_mul_eq_div,le_div_iff₀ (by positivity : 0 < 4*Real.pi)]
  nlinarith

theorem child_normalized_endpoints (v e : V) :
    child v e (normalize (v-e)) = v ∧ child v e (-normalize (v-e)) = e := by
  have hh : (‖v-e‖/2) • normalize (v-e) = (1/2 : ℝ) • (v-e) := by
    calc
      _ = (1/2 : ℝ) • (‖v-e‖ • normalize (v-e)) := by rw [smul_smul]; congr 1; ring
      _ = _ := by rw [norm_smul_normalize]
  constructor
  · rw [child,hh]
    module
  · rw [child,smul_neg,hh]
    module

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceAngularCharts
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.stateKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_pow_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Volume-preserving coordinates for the four collision angles -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem twoCollisionMap_measurable (v : V) : Measurable (twoCollisionMap v) := by
  unfold twoCollisionMap child
  fun_prop

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A collision window on which both chosen beam probabilities stay positive -/

noncomputable section

open MeasureTheory Set Metric

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem localCollisionCore_measurable : MeasurableSet localCollisionCore := measurableSet_ball

theorem norm_le_two_of_near_unit {v e : V} (he : ‖e‖ = 1) (hv : v ∈ ball e (1/4)) :
    ‖v‖ ≤ 2 := by
  have ht := dist_triangle v e (0 : V)
  rw [dist_zero_right,dist_zero_right,he] at ht
  have hd : dist v e < 1/4 := hv
  linarith

theorem localCollisionCore_distance {v : V} (hv : v ∈ localCollisionCore) :
    1 ≤ ‖v-beamAxis‖ := by
  have ht := dist_triangle firstAxis v beamAxis
  rw [dist_eq_norm,first_beam_norms.2,dist_comm firstAxis v,dist_eq_norm v beamAxis] at ht
  have hd : dist v firstAxis < 1/4 := hv
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceMinorization
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The angular window is dominated while retaining its intermediate-velocity support -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem firstAngleSet_measurable (v : V) : MeasurableSet (firstAngleSet v) := by
  apply localCollisionCore_measurable.preimage
  unfold child
  fun_prop

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_KernelInvariantPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Monotonicity of the finite positive collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace BoltzmannNonuniqueness.KernelHistoryOrder

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

theorem comp_mono {K L : Kernel X Y} {M N : Kernel Y Z} (hK : K ≤ L) (hM : M ≤ N) :
    M ∘ₖ K ≤ N ∘ₖ L := by
  intro x
  apply Measure.le_iff.mpr
  intro A hA
  rw [Kernel.comp_apply' _ _ _ hA,Kernel.comp_apply' _ _ _ hA]
  exact (lintegral_mono (fun y => hM y A)).trans (lintegral_mono' (hK x) le_rfl)

end BoltzmannNonuniqueness.KernelHistoryOrder

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteDepthKernelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite history comparison on a depth-dependent reachable region -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X]

theorem kernel_pow_le_on_depth (K L : Kernel X X) (D : ℕ → Set X) (N : ℕ)
    (hstep : ∀ n < N, ∀ x ∈ D (n+1), ∀ᵐ y ∂K x, y ∈ D n)
    (hle : ∀ n < N, ∀ x ∈ D (n+1), K x ≤ L x) :
    ∀ n ≤ N, ∀ x ∈ D n, (K^n) x ≤ (L^n) x := by
  intro n hn
  induction n with
  | zero => intro x hx; exact le_rfl
  | succ n ih =>
    intro x hx
    have hnN : n < N := Nat.lt_of_succ_le hn
    rw [show K^(n+1) = (K^n) ∘ₖ K by simpa only [pow_one] using Kernel.pow_add K n 1,
      show L^(n+1) = (L^n) ∘ₖ L by simpa only [pow_one] using Kernel.pow_add L n 1]
    apply KernelHistoryOrder.measure_comp_mono_ae _ (hle n hnN x hx)
    filter_upwards [hstep n hnN x hx] with y hy
    exact ih (Nat.le_of_lt hnN) y hy

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveAccessAngles
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed positive set of angular pairs reaching the target velocity ball -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem accessAngles_measurable (κ ρ : ℝ) : MeasurableSet (accessAngles κ ρ) :=
  ((twoCollisionMap_measurable beamAxis) measurableSet_ball).inter
    (firstAngleSet_measurable beamAxis)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AccessAngleStability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The fixed entry angles remain effective for nearby measurable partners -/

noncomputable section

open Set Metric

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem child_opposite_unit (e n : V) (he : ‖e‖ = 1) : child e (-e) n = n := by
  have hd : e-(-e) = (2:ℝ) • e := by module
  simp [child,hd,norm_smul,he]

theorem relative_distance_lower (v w u z : V) :
    ‖u-z‖-‖v-u‖-‖w-z‖ ≤ ‖v-w‖ := by
  have he : u-z = (u-v)+(v-w)+(w-z) := by module
  have hh : ‖u-z‖ ≤ ‖u-v‖+‖v-w‖+‖w-z‖ := by
    rw [he]
    have h₁ := norm_add_le (u-v) (v-w)
    have h₂ := norm_add_le ((u-v)+(v-w)) (w-z)
    linarith
  rw [norm_sub_rev u v] at hh
  linarith

theorem access_pair_stability {κ ρ ε : ℝ} (hκnonneg : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1)
    (hεsmall : ε ≤ 1/12) (hερ : 6*ε ≤ ρ)
    {e v w₁ w₂ : V} (he : ‖e‖ = 1)
    (hv : ‖v-e‖ ≤ ε) (hw₁ : ‖w₁-(-e)‖ ≤ ε) (hw₂ : ‖w₂-beamAxis‖ ≤ ε)
    {a : Sphere × Sphere} (ha : a ∈ accessAngles κ (ρ/2)) :
    let u := child v w₁ a.1.1
    let z := child u w₂ a.2.1
    1 ≤ ‖v-w₁‖ ∧ 3/4 ≤ ‖u-w₂‖ ∧ ‖u‖ ≤ 3 ∧ ‖z‖ ≤ 3 ∧
      ‖z-κ • firstAxis‖ < ρ := by
  let u₀ := child beamAxis (-beamAxis) a.1.1
  let z₀ := child u₀ beamAxis a.2.1
  let u := child v w₁ a.1.1
  let z := child u w₂ a.2.1
  have hu₀ : u₀ ∈ localCollisionCore := ha.2
  have hz₀ : ‖z₀-κ • firstAxis‖ < ρ/2 := ha.1
  have huerror : ‖u-u₀‖ ≤ 2*ε := by
    have hh := child_lipschitz v w₁ e (-e) a.1.1 (mem_sphere_zero_iff_norm.mp a.1.2)
    rw [child_opposite_unit e _ he] at hh
    have hh' : ‖u-u₀‖ ≤ ‖v-e‖+‖w₁-(-e)‖ := by
      simpa only [u,u₀,child_opposite_beam] using hh
    linarith
  have hzerror : ‖z-z₀‖ ≤ 3*ε := by
    exact (child_lipschitz u w₂ u₀ beamAxis a.2.1
      (mem_sphere_zero_iff_norm.mp a.2.2)).trans (by linarith)
  have hfirst := relative_distance_lower v w₁ e (-e)
  have hedist : ‖e-(-e)‖ = 2 := by
    rw [show e-(-e) = (2:ℝ) • e by module,norm_smul,Real.norm_ofNat,he,mul_one]
  rw [hedist] at hfirst
  have hsecond := relative_distance_lower u w₂ u₀ beamAxis
  have href := localCollisionCore_distance hu₀
  have hunorm := norm_le_two_of_near_unit axis_norms.1 hu₀
  have huupper : ‖u‖ ≤ 3 := by
    have hh := norm_sub_norm_le u u₀
    linarith
  have hzclose : ‖z-κ • firstAxis‖ < ρ := by
    have heq : z-κ • firstAxis = (z-z₀)+(z₀-κ • firstAxis) := by module
    have hh := norm_add_le (z-z₀) (z₀-κ • firstAxis)
    rw [← heq] at hh
    linarith
  have hzupper : ‖z‖ ≤ 3 := by
    have hh := norm_sub_norm_le z (κ • firstAxis)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hκnonneg,axis_norms.1,mul_one] at hh
    linarith
  exact ⟨by linarith,by linarith,huupper,hzupper,hzclose⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedPairUniformIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive two-collision entry weight with measurable beam coefficients -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem accessWeight_lower {κ ρ ε c : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε : ε ≤ 1/12) (hερ : 6*ε ≤ ρ) (hc : 0 < c)
    {e v : V} (he : ‖e‖ = 1) (hv : ‖v-e‖ ≤ ε)
    {w₁ w₂ : Sphere × Sphere → V} {b₁ b₂ : Sphere × Sphere → ℝ}
    (hpartners : ∀ a ∈ accessAngles κ (ρ/2),
      ‖w₁ a-(-e)‖ ≤ ε ∧ ‖w₂ a-beamAxis‖ ≤ ε)
    (hdensity : ∀ a ∈ accessAngles κ (ρ/2), c ≤ b₁ a ∧ c ≤ b₂ a) :
    (ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c))*
      (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)) ≤
        ∫⁻ a, accessWeight v w₁ w₂ b₁ b₂ κ ρ a ∂sphereProbability.prod sphereProbability := by
  let A := accessAngles κ (ρ/2)
  let μ := sphereProbability.prod sphereProbability
  let k := ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c)
  have hbound (a : Sphere × Sphere) (ha : a ∈ A) : k ≤ accessWeight v w₁ w₂ b₁ b₂ κ ρ a := by
    obtain ⟨hw₁,hw₂⟩ := hpartners a ha
    obtain ⟨hb₁,hb₂⟩ := hdensity a ha
    have hg := access_pair_stability hκ0 hκ hρ hε hερ he hv hw₁ hw₂ ha
    dsimp only at hg
    have hb₁0 : 0 ≤ b₁ a := hc.le.trans hb₁
    have hb₂0 : 0 ≤ b₂ a := hc.le.trans hb₂
    have h₁ : 4*Real.pi*c ≤ 4*Real.pi*b₁ a*‖v-w₁ a‖ := by
      calc
        _ ≤ 4*Real.pi*b₁ a := mul_le_mul_of_nonneg_left hb₁ (by positivity)
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hg.1
    have h₂ : 3*Real.pi*c ≤
        4*Real.pi*b₂ a*‖child v (w₁ a) a.1.1-w₂ a‖ := by
      calc
        _ = 4*Real.pi*c*(3/4) := by ring
        _ ≤ 4*Real.pi*b₂ a*(3/4) := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left hg.2.1 (by positivity)
    have hz : child (child v (w₁ a) a.1.1) (w₂ a) a.2.1 ∈ ball (κ • firstAxis) ρ := hg.2.2.2.2
    unfold accessWeight
    dsimp only
    rw [indicator_of_mem hz,mul_one]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal h₁) (ENNReal.ofReal_le_ofReal h₂)
  calc
    _ = ∫⁻ _a in A, k ∂μ := by rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]
    _ ≤ ∫⁻ a in A, accessWeight v w₁ w₂ b₁ b₂ κ ρ a ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (accessAngles_measurable κ (ρ/2))] with a ha
      exact hbound a ha
    _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceBranchingHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Cutting the first-event formula at an intermediate time -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem clockSurvival_add (rate : ℝ≥0) (s t : ℝ) :
    clockSurvival rate (s+t) = clockSurvival rate s*clockSurvival rate t := by
  rw [clockSurvival,clockSurvival,clockSurvival,← ENNReal.ofReal_mul (by positivity),← Real.exp_add]
  congr 2
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PerturbedFiniteBlock
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The loss frequency of the limiting atomic medium -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.GeometricBackground

theorem frequency_bound {θ η l K α γ t : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (ht : 0 < t)
    (x : JetPrototype.Space) (v : Velocity) :
    frequency θ η l K α γ t x v ≤
      (2*Real.pi)*(2*((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t))))*(‖v‖+1+α) := by
  classical
  have hcoef : 0 ≤ K*max 1 (α*γ)⁻¹ :=
    mul_nonneg hK (le_max_of_le_left zero_le_one)
  by_cases ha : active θ η l x.1
  · unfold frequency
    rw [background,ite_eq_left ha]
    have hc := AxialBackground.integral_cell_abs_le hK hα hγ (scale_pos hθ η x.1)
      ht.le x.2 (fun p => ‖v-p‖) (C := ‖v‖+1+α) (fun p hp => by
        rw [abs_of_nonneg (norm_nonneg _)]
        exact (norm_sub_le v p).trans (by linarith))
    have hi := (le_abs_self _).trans hc
    have hm : (K*max 1 (α*γ)⁻¹)/(scale θ η x.1+t) ≤
        (K*max 1 (α*γ)⁻¹)/(l+t) :=
      div_le_div_of_nonneg_left hcoef (by positivity) (by linarith [ha.1])
    calc
      _ ≤ (2*Real.pi)*(2*((1/4)*((K*max 1 (α*γ)⁻¹)/(scale θ η x.1+t)))*(‖v‖+1+α)) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ ≤ (2*Real.pi)*(2*((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t)))*(‖v‖+1+α)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hm (by norm_num)) (by norm_num)
      _ = _ := by ring
  · rw [frequency,background,ite_eq_right ha,integral_zero_measure,mul_zero]
    positivity

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Relative weights of the actual compressed cold beams -/

noncomputable section

open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialBackground

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

section

/-! # A quantitative positive cold weight on bounded time and scale intervals -/

noncomputable section

open Set
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.AxialBackground

theorem S_lower_of_abs_le {R x : ℝ} (hR : 0 ≤ R) (hx : |x| ≤ R) : S R ≤ S x := by
  have hc : Real.cosh x ≤ Real.cosh R :=
    Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg hR] using hx)
  have hi : (Real.cosh R)⁻¹ ≤ (Real.cosh x)⁻¹ :=
    (inv_le_inv₀ (Real.cosh_pos _) (Real.cosh_pos _)).mpr hc
  unfold S
  nlinarith [inv_nonneg.mpr (Real.cosh_pos x).le,inv_nonneg.mpr (Real.cosh_pos R).le]

theorem compactWeightLower_pos {K α γ m M T Z : ℝ}
    (hK : 0 < K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hM : 0 < M) (hT : 0 ≤ T) :
    0 < compactWeightLower K α γ m M T Z := by
  unfold compactWeightLower
  exact mul_pos (by norm_num) (div_pos (mul_pos hK (S_pos _)) (by positivity))

theorem compactWeightLower_le {K α γ m M T Z μ t σ z : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hm : 0 < m)
    (hT : 0 ≤ T) (hZ : 0 ≤ Z) (hμ : μ ∈ Icc m M) (ht : t ∈ Icc 0 T)
    (hσ : |σ| = 1) (hz : |z| ≤ Z) :
    compactWeightLower K α γ m M T Z ≤ weight K α γ μ t σ z := by
  have ht0 : 0 ≤ t := ht.1
  have hμ0 : 0 < μ := hm.trans_le hμ.1
  have hM : 0 < M := hμ0.trans_le hμ.2
  have hfoot : |AxialFlow.foot σ α γ μ t z| ≤ Z+T*(1+α) := by
    have hh := foot_abs_bound hα ht.1 σ γ μ z
    rw [hσ] at hh
    exact hh.trans (add_le_add hz (mul_le_mul_of_nonneg_right ht.2 (by positivity)))
  have harg : |γ*AxialFlow.foot σ α γ μ t z/μ| ≤ γ*(Z+T*(1+α))/m := by
    rw [abs_div,abs_mul,abs_of_nonneg hγ,abs_of_pos hμ0]
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfoot hγ) hμ0.le).trans
    exact div_le_div_of_nonneg_left (by positivity) hm hμ.1
  have hS := S_lower_of_abs_le (show 0 ≤ γ*(Z+T*(1+α))/m by positivity) harg
  have hden : μ+t*α*γ*S (γ*AxialFlow.foot σ α γ μ t z/μ) ≤ M+T*α*γ := by
    have hs : t*α*γ*S (γ*AxialFlow.foot σ α γ μ t z/μ) ≤ t*α*γ :=
      mul_le_of_le_one_right (by positivity) (S_le_one _)
    have ht' : t*α*γ ≤ T*α*γ := by gcongr; exact ht.2
    linarith [hμ.2]
  have hden0 : 0 < μ+t*α*γ*S (γ*AxialFlow.foot σ α γ μ t z/μ) := by
    have hS0 := (S_pos (γ*AxialFlow.foot σ α γ μ t z/μ)).le
    positivity
  unfold compactWeightLower weight JetCoreDensity.compressed
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS hK) (by positivity)).trans
  exact div_le_div_of_nonneg_left (mul_nonneg hK (S_pos _).le) hden0 hden

end BoltzmannNonuniqueness.AxialBackground

end

end

section

/-! # The hot cap cancels the inverse-time background loss coefficient -/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem lossCoefficient_nonneg {K : ℝ} (hK : 0 ≤ K) (α γ : ℝ) :
    0 ≤ lossCoefficient K α γ := by
  unfold lossCoefficient
  positivity

theorem frequency_slab_bound {θ η l K α γ a t : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (ha : 0 < a) (hat : a ≤ t) (x : JetPrototype.Space) (v : Velocity) :
    frequency θ η l K α γ t x v ≤
      (lossCoefficient K α γ/a)*(‖v‖+1+α) := by
  apply (frequency_bound hθ hl hK hα hγ (ha.trans_le hat) x v).trans
  have hb : (K*max 1 (α*γ)⁻¹)/(l+t) ≤ (K*max 1 (α*γ)⁻¹)/a :=
    div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha (by linarith)
  calc
    _ ≤ (2*Real.pi)*(2*((1/4)*((K*max 1 (α*γ)⁻¹)/a)))*(‖v‖+1+α) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by norm_num)) (by norm_num)
    _ = _ := by unfold lossCoefficient; ring

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricPositiveCompact
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

section

/-! # Both selected cold beams have a uniform positive density on compact annuli -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem beamDensity_compact_lower {θ η α γ r₀ R T Z : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hr₀ : 0 < r₀) (hR : 0 < R) (hT : 0 ≤ T) (hZ : 0 ≤ Z) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℝ × Velocity), p.1 ∈ Icc 0 T →
      ‖transverse p.2‖ ∈ Icc r₀ R → |axial p.2| ≤ Z →
      ∀ σ : ℝ, |σ| = 1 → c ≤ beamDensity θ η α γ 1 σ p := by
  let m := r₀/Real.exp η
  let c := 4*AxialBackground.compactWeightLower 1 α γ m R T Z
  have hm : 0 < m := div_pos hr₀ (Real.exp_pos η)
  have hc : 0 < c := mul_pos (by norm_num)
    (AxialBackground.compactWeightLower_pos (by norm_num) hα hγ hR hT)
  refine ⟨c,hc,?_⟩
  intro p ht hp hz σ hσ
  have hp0 : 0 < ‖transverse p.2‖ := hr₀.trans_le hp.1
  have hb := GeometricMesh.cell_bounds hθ hη hp0
  have hμ : scale θ η (transverse p.2) ∈ Icc m R := by
    refine ⟨?_,hb.1.trans hp.2⟩
    apply (div_le_iff₀ (Real.exp_pos η)).mpr
    exact hp.1.trans (by simpa only [mul_comm,scale] using hb.2.le)
  have hh := AxialBackground.compactWeightLower_le (by norm_num : (0:ℝ) ≤ 1)
    hα hγ hm hT hZ hμ ht hσ hz
  change 4*AxialBackground.compactWeightLower 1 α γ m R T Z ≤ _
  unfold beamDensity
  rw [max_eq_right ht.1]
  norm_num only [mul_one]
  exact mul_le_mul_of_nonneg_left hh (by norm_num)

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

/-! # Finite medium histories equal powers of the actual marked event kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finishMediumFlight_measurable : Measurable finishMediumFlight := by
  unfold finishMediumFlight
  fun_prop

end BoltzmannNonuniqueness.ReferenceGeometry

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

end BoltzmannNonuniqueness.GeometricBackground

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedMeshStep
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A positive first-collision angular cap for bounded incoming velocities -/

noncomputable section

open MeasureTheory Set NormedSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem outgoing_bounded_endpoint_cap {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (v e b : V) (he : ‖e‖ ≤ 2) (hv : ‖v‖ ≤ R) (n : Sphere)
    (hn : dist (child v e n.1) b ≤ δ/2) :
    sphereCapMass (δ/(R+2)) ≤ (outgoing (v,e)).real (Metric.ball b δ) := by
  have hRp : 0 < R+2 := by linarith
  have hsub : Metric.ball n (δ/(R+2)) ⊆
      (fun m : Sphere => child v e m.1) ⁻¹' Metric.ball b δ := by
    intro m hm
    have hd : dist (m : V) (n : V) < δ/(R+2) := hm
    have hr : ‖v-e‖ ≤ R+2 := (norm_sub_le v e).trans (add_le_add hv he)
    have ht := dist_triangle (child v e m.1) (child v e n.1) b
    rw [child_angular_distance] at ht
    have hp := mul_le_mul_of_nonneg_right hr (dist_nonneg : 0 ≤ dist (m : V) (n : V))
    have hh := (lt_div_iff₀ hRp).mp hd
    change dist (child v e m.1) b < δ
    nlinarith
  have hh := (sphere_cap_lower (div_pos hδ hRp) n).trans (measureReal_mono hsub)
  rw [Measure.real,outgoing_apply,Measure.map_apply (by unfold child; fun_prop) measurableSet_ball]
  exact hh

theorem exists_separated_beam (v : V) :
    1 ≤ ‖v-beamAxis‖ ∨ 1 ≤ ‖v-(-beamAxis)‖ := by
  have h := two_beam_distance_lower v beamAxis axis_norms.2.2
  rw [sub_neg_eq_add]
  by_cases hp : 1 ≤ ‖v-beamAxis‖
  · exact Or.inl hp
  · exact Or.inr (by linarith)

theorem nearby_partner_distance {v e b : V} {α : ℝ}
    (hvb : 1 ≤ ‖v-b‖) (heb : ‖e-b‖ ≤ α) : 1-α ≤ ‖v-e‖ := by
  have ht := norm_sub_le (v-e) (b-e)
  rw [sub_sub_sub_cancel_right,norm_sub_rev b e] at ht
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FirstEntryMass
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform positive first-collision weight into the beam neighborhood -/

noncomputable section

open MeasureTheory Set Metric NormedSpace
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem outgoing_near_partner_lower {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (v w e : V) (hw : ‖w‖ ≤ 2) (hv : ‖v‖ ≤ R) (hne : v ≠ w)
    (hwe : dist w e ≤ δ/2) :
    ENNReal.ofReal (sphereCapMass (δ/(R+2))) ≤ outgoing (v,w) (ball e δ) := by
  let n : Sphere := ⟨-normalize (v-w),mem_sphere_zero_iff_norm.mpr
    (by rw [norm_neg,norm_normalize (sub_ne_zero.mpr hne)])⟩
  have hn : child v w n.1 = w := (child_normalized_endpoints v w).2
  have hh := outgoing_bounded_endpoint_cap hR hδ v w e hw hv n (by rw [hn]; exact hwe)
  exact (ENNReal.ofReal_le_ofReal hh).trans ENNReal.ofReal_toReal_le

theorem firstEntryMass_pos {R δ c : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hc : 0 < c) :
    0 < firstEntryMass R δ c := by
  apply pos_iff_ne_zero.mpr
  exact mul_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
    (ne_of_gt (ENNReal.ofReal_pos.mpr (sphereCapMass_pos (div_pos hδ (by linarith)))))

theorem firstEntryMass_lower {R δ c b : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hc : 0 < c) (hb : c ≤ b) {v w e : V} (hw : ‖w‖ ≤ 2) (hv : ‖v‖ ≤ R)
    (hvw : 3/4 ≤ ‖v-w‖) (hwe : dist w e ≤ δ/2) :
    firstEntryMass R δ c ≤
      ENNReal.ofReal (4*Real.pi*b*‖v-w‖)*outgoing (v,w) (ball e δ) := by
  have hne : v ≠ w := by
    intro h
    rw [h,sub_self,norm_zero] at hvw
    norm_num at hvw
  have hb0 : 0 ≤ b := hc.le.trans hb
  have hrate : 3*Real.pi*c ≤ 4*Real.pi*b*‖v-w‖ := by
    calc
      _ = 4*Real.pi*c*(3/4) := by ring
      _ ≤ 4*Real.pi*b*(3/4) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hvw (by positivity)
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hrate)
    (outgoing_near_partner_lower hR hδ v w e hw hv hne hwe)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformAverageCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform three-collision access weight for integration over collision times -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem three_collision_access_lower {κ ρ ε c R b₀ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε0 : 0 < ε) (hε : ε ≤ 1/12) (hερ : 6*ε ≤ ρ)
    (hc : 0 < c) (hb₀ : c ≤ b₀) (hR : 0 ≤ R)
    {e v w₀ : V} (he : ‖e‖ = 1) (hv : ‖v‖ ≤ R) (hw₀ : ‖w₀‖ ≤ 2)
    (hve : 3/4 ≤ ‖v-w₀‖) (hnear : dist w₀ e ≤ ε/2)
    (w₁ w₂ : V → Sphere × Sphere → V) (b₁ b₂ : V → Sphere × Sphere → ℝ)
    (hpartners : ∀ u ∈ ball e ε, ∀ a ∈ accessAngles κ (ρ/2),
      ‖w₁ u a-(-e)‖ ≤ ε ∧ ‖w₂ u a-beamAxis‖ ≤ ε)
    (hdensity : ∀ u ∈ ball e ε, ∀ a ∈ accessAngles κ (ρ/2),
      c ≤ b₁ u a ∧ c ≤ b₂ u a)
    :
    firstEntryMass R ε c *
      ((ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c))*
        (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2))) ≤
      ENNReal.ofReal (4*Real.pi*b₀*‖v-w₀‖)*
      ∫⁻ u, (∫⁻ a, accessWeight u (w₁ u) (w₂ u) (b₁ u) (b₂ u) κ ρ a
        ∂sphereProbability.prod sphereProbability) ∂outgoing (v,w₀) := by
  let k := (ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c))*
    (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2))
  have hbound : k*outgoing (v,w₀) (ball e ε) ≤
      ∫⁻ u, (∫⁻ a, accessWeight u (w₁ u) (w₂ u) (b₁ u) (b₂ u) κ ρ a
        ∂sphereProbability.prod sphereProbability) ∂outgoing (v,w₀) := by
    calc
      _ = ∫⁻ _u in ball e ε, k ∂outgoing (v,w₀) := by
        rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]
      _ ≤ ∫⁻ u in ball e ε, (∫⁻ a, accessWeight u (w₁ u) (w₂ u) (b₁ u) (b₂ u) κ ρ a
          ∂sphereProbability.prod sphereProbability) ∂outgoing (v,w₀) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
        apply accessWeight_lower hκ0 hκ hρ hε hερ hc he
          (show ‖u-e‖ ≤ ε from le_of_lt hu)
        · exact hpartners u hu
        · exact hdensity u hu
      _ ≤ _ := lintegral_mono' Measure.restrict_le_self le_rfl
  have hfirst := firstEntryMass_lower hR hε0 hc hb₀ hw₀ hv hve hnear
  calc
    firstEntryMass R ε c*k ≤
        (ENNReal.ofReal (4*Real.pi*b₀*‖v-w₀‖)*outgoing (v,w₀) (ball e ε))*k := by
      exact mul_le_mul' hfirst le_rfl
    _ = ENNReal.ofReal (4*Real.pi*b₀*‖v-w₀‖)*(k*outgoing (v,w₀) (ball e ε)) := by ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl hbound

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

theorem physicalMarkedEvent_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedEvent b endTime C m p) =
      ∫⁻ s in Ioc 0 p.1, clockSurvival C s *
        (mediumMarkedRate b m (mediumPoint endTime p s,p.2.2) *
          ∫⁻ n : Sphere, F (mediumParameterState b endTime p (m,(s,n)))
            ∂sphereProbability) := by
  rw [physicalMarkedEvent,Kernel.lintegral_comp _ _ _ hF,
    physicalWaitingKernel_lintegral C p hF.lintegral_kernel]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro s _hs
  dsimp only
  rw [physicalMarkedCollision_lintegral b endTime m _ hF]
  simp only [physicalAdvance,mediumPoint,mediumParameterState]
  rw [show endTime-(p.1-s) = endTime-p.1+s by ring]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Time and angle parameters for a selected physical collision -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalParameterWeight_measurable (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) :
    Measurable (fun q : PhysicalFlightState × EventParameter =>
      physicalParameterWeight b endTime C m q.1 q.2) := by
  have ht : Measurable (fun q : PhysicalFlightState × EventParameter => (q.1,q.2.1)) := by
    fun_prop
  exact ((physicalWaitingWeight_measurable C).comp ht).mul
    ((mediumMarkedRate_measurable b m).comp
      (((mediumPoint_measurable endTime).comp ht).prodMk (by fun_prop)))

theorem physicalParameterWeight_ne_top (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) (p : PhysicalFlightState) (a : EventParameter) :
    physicalParameterWeight b endTime C m p a ≠ ⊤ := by
  unfold physicalParameterWeight
  by_cases h : 0 < a.1 ∧ a.1 ≤ p.1
  · rw [show physicalWaitingWeight C (p,a.1) = clockSurvival C a.1 by
      simp [physicalWaitingWeight,h]]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · simp [physicalWaitingWeight,h]

theorem physicalMarkedEvent_parameters (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedEvent b endTime C m p) =
      ∫⁻ a, physicalParameterWeight b endTime C m p a *
        F (mediumParameterState b endTime p (m,a)) ∂physicalEventMeasure := by
  have hs : Measurable (fun a : EventParameter => mediumParameterState b endTime p (m,a)) :=
    (mediumParameterState_measurable b endTime).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hw : Measurable (fun a : EventParameter => physicalParameterWeight b endTime C m p a) :=
    (physicalParameterWeight_measurable b endTime C m).comp
      (measurable_const.prodMk measurable_id)
  have hM : Measurable (fun a : EventParameter => physicalParameterWeight b endTime C m p a *
      F (mediumParameterState b endTime p (m,a))) := hw.mul (hF.comp hs)
  rw [physicalMarkedEvent_lintegral b endTime C m p hF,
    physicalEventMeasure,lintegral_prod _ hM.aemeasurable,
    ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro s
  by_cases hs : s ∈ Ioc 0 p.1
  · simp only [indicator_of_mem hs,physicalParameterWeight]
    rw [show physicalWaitingWeight C (p,s) = clockSurvival C s by
      simp [physicalWaitingWeight,hs.1,hs.2]]
    have hfin : clockSurvival C s * mediumMarkedRate b m (mediumPoint endTime p s,p.2.2) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    rw [lintegral_const_mul' _ _ hfin]
    exact (mul_assoc _ _ _).symm
  · simp [physicalParameterWeight,physicalWaitingWeight,hs,
      show ¬ (0 < s ∧ s ≤ p.1) from hs]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Gain-only physical histories with a chosen damping constant -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalMarkedCollision_le_beam (b : BeamCoefficients) (endTime : ℝ)
    (m : HistoryMark) (hm : m ≠ 0) :
    physicalMarkedCollision b endTime m ≤ physicalBeamCollision b endTime := by
  unfold physicalBeamCollision
  fin_cases m
  · exact False.elim (hm rfl)
  · exact le_add_of_nonneg_right bot_le
  · exact le_add_of_nonneg_left bot_le

theorem physicalMarkedEvent_le_beam (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m : HistoryMark) (hm : m ≠ 0) :
    physicalMarkedEvent b endTime C m ≤ physicalBeamEvent b endTime C :=
  KernelHistoryOrder.comp_mono le_rfl (physicalMarkedCollision_le_beam b endTime m hm)

theorem physicalMarkedWord_le_beam (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (ms : List HistoryMark) (hm : ∀ m ∈ ms, m ≠ 0) :
    physicalMarkedWord b endTime C ms ≤ (physicalBeamEvent b endTime C)^ms.length := by
  induction ms with
  | nil => exact le_rfl
  | cons m ms ih =>
    simp only [physicalMarkedWord,List.length_cons,pow_succ]
    exact KernelHistoryOrder.comp_mono
      (physicalMarkedEvent_le_beam b endTime C m (hm m (by simp)))
      (ih (fun n hn => hm n (by simp [hn])))

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

theorem physicalGainEndpoint_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) (p : PhysicalFlightState)
    {F : V × V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂physicalGainEndpoint b endTime C n p) =
      ∫⁻ q, clockSurvival C q.1 * F (finishMediumFlight q)
        ∂((physicalBeamEvent b endTime C)^n) p := by
  have hc : Measurable (Function.uncurry (fun (_ : PhysicalFlightState) (q : PhysicalFlightState) =>
      clockSurvival C q.1)) := by unfold clockSurvival; fun_prop
  have hf : Measurable (fun q : PhysicalFlightState => F (finishMediumFlight q)) :=
    hF.comp finishMediumFlight_measurable
  rw [physicalGainEndpoint,Kernel.lintegral_map _ finishMediumFlight_measurable p hF,
    Kernel.lintegral_withDensity _ hc p hf]

theorem physicalGainEndpoint_apply (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) (p : PhysicalFlightState)
    {A : Set (V × V)} (hA : MeasurableSet A) :
    physicalGainEndpoint b endTime C n p A =
      ∫⁻ q, clockSurvival C q.1 * A.indicator 1 (finishMediumFlight q)
        ∂((physicalBeamEvent b endTime C)^n) p := by
  rw [← lintegral_indicator_one hA]
  exact physicalGainEndpoint_lintegral b endTime C n p (measurable_const.indicator hA)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedEndpointHistories
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ThreeCollisionTimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A positive time window for three ordered collision waits -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem threeWaitBox_measurable (h : ℝ) : MeasurableSet (threeWaitBox h) :=
  measurableSet_Ioo.prod (measurableSet_Ioo.prod measurableSet_Ioo)

theorem threeWaitBox_volume {h : ℝ} (hh : 0 < h) :
    0 < (volume : Measure ThreeWaits) (threeWaitBox h) := by
  rw [Measure.volume_eq_prod,threeWaitBox,Measure.prod_prod,
    Measure.volume_eq_prod,Measure.prod_prod,Real.volume_Ioo,sub_zero]
  have hp : 0 < ENNReal.ofReal (h/4) := ENNReal.ofReal_pos.mpr (by positivity)
  exact pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt hp) (mul_ne_zero (ne_of_gt hp) (ne_of_gt hp)))

theorem threeWaitBox_sum {h : ℝ} (hh : 0 < h) {s : ThreeWaits}
    (hs : s ∈ threeWaitBox h) :
    0 < s.1 ∧ 0 < s.2.1 ∧ 0 < s.2.2 ∧ s.1+s.2.1+s.2.2 < h := by
  exact ⟨hs.1.1,hs.2.1.1,hs.2.2.1,by linarith [hs.1.2,hs.2.1.2,hs.2.2.2]⟩

theorem threeWaitBox_integral_pos {h : ℝ} (hh : 0 < h)
    {F : ThreeWaits → ℝ≥0∞} (hF : Measurable F)
    (hp : ∀ s ∈ threeWaitBox h, 0 < F s) :
    0 < ∫⁻ s in threeWaitBox h, F s := by
  apply (setLIntegral_pos_iff hF).mpr
  apply (threeWaitBox_volume hh).trans_le
  apply measure_mono
  intro s hs
  exact ⟨(ne_of_gt (hp s hs)),hs⟩

theorem three_wait_survival (C : ℝ≥0) (T : ℝ) (s : ThreeWaits) :
    clockSurvival C s.1*clockSurvival C s.2.1*clockSurvival C s.2.2*
      clockSurvival C (T-(s.1+s.2.1+s.2.2)) = clockSurvival C T := by
  rw [← clockSurvival_add,← clockSurvival_add,← clockSurvival_add]
  congr 1
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_EntrySites
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A short three-collision path stays in a bounded region outside the hole -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem nearby_entry_cylinder {x y : V} {L X : ℝ}
    (hx : ‖x‖ ≤ X) (hr : L+1 < ‖transverse x‖) (hd : ‖y-x‖ ≤ 1) :
    L < ‖transverse y‖ ∧ ‖y‖ ≤ X+1 := by
  have ht := norm_sub_norm_le (transverse x) (transverse y)
  have he : ‖transverse x-transverse y‖ ≤ 1 := by
    rw [← PlaneChart.transverse_sub]
    exact (LargeOutput.transverse_norm_le (x-y)).trans (by rwa [norm_sub_rev])
  have hn := norm_sub_norm_le y x
  exact ⟨by linarith,by linarith⟩

theorem short_three_flights {R h s₀ s₁ s₂ : ℝ} {x v₀ v₁ v₂ : V}
    (hR : 0 ≤ R) (hsmall : (R+6)*h ≤ 1)
    (hs₀ : s₀ ∈ Icc 0 h) (hs₁ : s₁ ∈ Icc 0 h) (hs₂ : s₂ ∈ Icc 0 h)
    (hv₀ : ‖v₀‖ ≤ R) (hv₁ : ‖v₁‖ ≤ 3) (hv₂ : ‖v₂‖ ≤ 3) :
    ‖(x+s₀ • v₀+s₁ • v₁+s₂ • v₂)-x‖ ≤ 1 := by
  have ht₀ : ‖s₀ • v₀‖ ≤ h*R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs₀.1]
    exact (mul_le_mul_of_nonneg_left hv₀ hs₀.1).trans
      (mul_le_mul_of_nonneg_right hs₀.2 hR)
  have ht₁ : ‖s₁ • v₁‖ ≤ h*3 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs₁.1]
    exact (mul_le_mul_of_nonneg_left hv₁ hs₁.1).trans
      (mul_le_mul_of_nonneg_right hs₁.2 (by norm_num))
  have ht₂ : ‖s₂ • v₂‖ ≤ h*3 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs₂.1]
    exact (mul_le_mul_of_nonneg_left hv₂ hs₂.1).trans
      (mul_le_mul_of_nonneg_right hs₂.2 (by norm_num))
  have he : (x+s₀ • v₀+s₁ • v₁+s₂ • v₂)-x =
      (s₀ • v₀+s₁ • v₁)+s₂ • v₂ := by module
  rw [he]
  have h₁ := norm_add_le (s₀ • v₀) (s₁ • v₁)
  have h₂ := norm_add_le (s₀ • v₀+s₁ • v₁) (s₂ • v₂)
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem nearby_beamDensity_lower {θ η α γ L X T : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hL : 0 < L) (hX : 0 ≤ X) (hT : 0 ≤ T) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : Velocity), ‖x‖ ≤ X → L+1 < ‖transverse x‖ →
      ∀ (y : Velocity), ‖y-x‖ ≤ 1 → ∀ t ∈ Icc 0 T, ∀ σ : ℝ, |σ| = 1 →
        c ≤ beamDensity θ η α γ 1 σ (t,y) := by
  obtain ⟨c,hc,hbound⟩ := beamDensity_compact_lower hθ hη hα hγ hL
    (show 0 < X+1 by linarith) hT (show 0 ≤ X+1 by linarith)
  refine ⟨c,hc,?_⟩
  intro x hx hr y hxy t ht σ hσ
  obtain ⟨hyl,hyn⟩ := ReferenceGeometry.nearby_entry_cylinder hx hr hxy
  exact hbound (t,y) ht ⟨hyl.le,(LargeOutput.transverse_norm_le y).trans hyn⟩
    ((SmallInputGeometry.abs_axial_le_norm y).trans hyn) σ hσ

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The three physical collision sites in the entry path -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem entrySites_bounded {R h t T : ℝ} {x v u z : V} {s : ThreeWaits}
    (hR : 0 ≤ R) (hsmall : (R+6)*h ≤ 1) (ht : 0 ≤ t) (hT : t+3*h ≤ T)
    (hs₀ : s.1 ∈ Icc 0 h) (hs₁ : s.2.1 ∈ Icc 0 h) (hs₂ : s.2.2 ∈ Icc 0 h)
    (hv : ‖v‖ ≤ R) (hu : ‖u‖ ≤ 3) (hz : ‖z‖ ≤ 3) :
    ((entrySite₀ t x v s).1 ∈ Icc 0 T ∧ ‖(entrySite₀ t x v s).2-x‖ ≤ 1) ∧
    ((entrySite₁ t x v s u).1 ∈ Icc 0 T ∧ ‖(entrySite₁ t x v s u).2-x‖ ≤ 1) ∧
    ((entrySite₂ t x v s u z).1 ∈ Icc 0 T ∧ ‖(entrySite₂ t x v s u z).2-x‖ ≤ 1) := by
  have hh : 0 ≤ h := hs₀.1.trans hs₀.2
  have hs0 : (0:ℝ) ∈ Icc 0 h := ⟨le_rfl,hh⟩
  have hzero : ‖(0:V)‖ ≤ 3 := by norm_num
  have hd₀ := short_three_flights (x := x) hR hsmall hs₀ hs0 hs0 hv hzero hzero
  have hd₁ := short_three_flights (x := x) hR hsmall hs₀ hs₁ hs0 hv hu hzero
  have hd₂ := short_three_flights (x := x) hR hsmall hs₀ hs₁ hs₂ hv hu hz
  simp only [zero_smul,add_zero] at hd₀ hd₁
  refine ⟨⟨⟨?_,?_⟩,hd₀⟩,⟨⟨?_,?_⟩,hd₁⟩,⟨⟨?_,?_⟩,hd₂⟩⟩ <;>
    dsimp [entrySite₀,entrySite₁,entrySite₂] <;>
    linarith [hs₀.1,hs₀.2,hs₁.1,hs₁.2,hs₂.1,hs₂.2]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_OutgoingPairIntegral
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalGainEndpoint_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.stateKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_pow_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One outgoing collision followed by a fixed angular pair -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem outgoing_pair_lintegral (r : ℝ≥0∞) (hr : r ≠ ⊤) (v w : V)
    {F : V × (Sphere × Sphere) → ℝ≥0∞} (hF : Measurable F) :
    r * (∫⁻ u, (∫⁻ a, F (u,a) ∂sphereProbability.prod sphereProbability) ∂outgoing (v,w)) =
      ∫⁻ q : Sphere × (Sphere × Sphere), r * F (child v w q.1.1,q.2)
        ∂sphereProbability.prod (sphereProbability.prod sphereProbability) := by
  have hu : Measurable (fun n : Sphere => child v w n.1) := by unfold child; fun_prop
  have hm : Measurable (fun q : Sphere × (Sphere × Sphere) => r*F (child v w q.1.1,q.2)) :=
    measurable_const.mul (hF.comp ((hu.comp measurable_fst).prodMk measurable_snd))
  have hi : Measurable (fun u : V => ∫⁻ a, F (u,a) ∂sphereProbability.prod sphereProbability) :=
    hF.lintegral_prod_right'
  rw [outgoing_apply,lintegral_map hi hu,lintegral_prod _ hm.aemeasurable,
    ← lintegral_const_mul' _ _ hr]
  apply lintegral_congr
  intro n
  exact (lintegral_const_mul' _ _ hr).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionParameterShuffle
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Regrouping collision times and outgoing angles preserves their product law -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

private theorem pair_shuffle_preserving {A B D E : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace D] [MeasurableSpace E]
    (μ : Measure A) (ν : Measure B) (κ : Measure D) (τ : Measure E)
    [SFinite μ] [SFinite ν] [SFinite κ] [SFinite τ] :
    MeasurePreserving (fun q : (A × B) × (D × E) => ((q.1.1,q.2.1),(q.1.2,q.2.2)))
      ((μ.prod ν).prod (κ.prod τ)) ((μ.prod κ).prod (ν.prod τ)) := by
  have h₁ := measurePreserving_prodAssoc μ ν (κ.prod τ)
  have h₂ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc ν κ τ)
  have h₃ := (Measure.measurePreserving_swap (μ := ν) (ν := κ)).prod
    (MeasurePreserving.id τ)
  have h₄ := measurePreserving_prodAssoc κ ν τ
  have h₅ := (MeasurePreserving.id μ).prod (h₄.comp (h₃.comp h₂))
  have h₆ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ κ (ν.prod τ))
  exact h₆.comp (h₅.comp h₁)

theorem splitThreeEvents_preserving : MeasurePreserving splitThreeEvents
    (physicalEventMeasure.prod (physicalEventMeasure.prod physicalEventMeasure))
    ((volume : Measure ThreeWaits).prod
      (sphereProbability.prod (sphereProbability.prod sphereProbability))) := by
  have hi : MeasurePreserving
      (fun q : EventParameter × EventParameter => ((q.1.1,q.2.1),(q.1.2,q.2.2)))
      (physicalEventMeasure.prod physicalEventMeasure)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).prod
        (sphereProbability.prod sphereProbability)) :=
    pair_shuffle_preserving (volume : Measure ℝ) sphereProbability (volume : Measure ℝ) sphereProbability
  have h₁ := (MeasurePreserving.id physicalEventMeasure).prod hi
  have h₂ := pair_shuffle_preserving (volume : Measure ℝ) sphereProbability
    ((volume : Measure ℝ).prod (volume : Measure ℝ)) (sphereProbability.prod sphereProbability)
  convert h₂.comp h₁ using 1
  all_goals try with_reducible_and_instances rfl
  rfl

theorem three_events_lintegral {F : ThreeEvents → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalEventMeasure.prod (physicalEventMeasure.prod physicalEventMeasure)) =
      ∫⁻ s : ThreeWaits, ∫⁻ a : ThreeAngles, F (joinThreeEvents s a)
        ∂sphereProbability.prod (sphereProbability.prod sphereProbability) := by
  let : SFinite (sphereProbability.prod sphereProbability) := Measure.prod.instSFinite
  let : SFinite (sphereProbability.prod (sphereProbability.prod sphereProbability)) :=
    Measure.prod.instSFinite
  have hm : Measurable (fun q : ThreeWaits × ThreeAngles => F (joinThreeEvents q.1 q.2)) :=
    hF.comp (by unfold joinThreeEvents; fun_prop)
  rw [← lintegral_prod _ hm.aemeasurable]
  exact splitThreeEvents_preserving.lintegral_comp hm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_SelectedOriginDeletion
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Fixed products for selected physical collision words -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

attribute [instance] collisionWordMeasurable

theorem selectedWordState_measurable (b : BeamCoefficients) (endTime : ℝ)
    (ms : List HistoryMark) : Measurable (fun q : PhysicalFlightState × CollisionWord ms.length =>
      selectedWordState b endTime ms q.1 q.2) := by
  induction ms with
  | nil => exact measurable_fst
  | cons m ms ih =>
    have hs : Measurable (fun q : PhysicalFlightState × CollisionWord (m::ms).length =>
        (mediumParameterState b endTime q.1 (m,q.2.1),q.2.2)) :=
      ((mediumParameterState_measurable b endTime).comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd.fst))).prodMk
          measurable_snd.snd
    exact ih.comp hs

theorem selectedWordDensity_measurable (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (ms : List HistoryMark) : Measurable (fun q : PhysicalFlightState × CollisionWord ms.length =>
      selectedWordDensity b endTime C ms q.1 q.2) := by
  induction ms with
  | nil => exact measurable_const
  | cons m ms ih =>
    have hs : Measurable (fun q : PhysicalFlightState × CollisionWord (m::ms).length =>
        (mediumParameterState b endTime q.1 (m,q.2.1),q.2.2)) :=
      ((mediumParameterState_measurable b endTime).comp
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd.fst))).prodMk
          measurable_snd.snd
    exact ((physicalParameterWeight_measurable b endTime C m).comp
      (measurable_fst.prodMk measurable_snd.fst)).mul (ih.comp hs)

theorem selectedWord_integral (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (ms : List HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ a, selectedWordDensity b endTime C ms p a * F (selectedWordState b endTime ms p a)
      ∂collisionWordMeasure ms.length) = ∫⁻ q, F q ∂physicalMarkedWord b endTime C ms p := by
  induction ms generalizing p with
  | nil =>
    change (∫⁻ _ : PUnit, 1 * F p ∂Measure.dirac PUnit.unit) = ∫⁻ q, F q ∂Kernel.id p
    simp [Kernel.id_apply]
  | cons m ms ih =>
    have hm : Measurable (fun a : CollisionWord (m::ms).length =>
        selectedWordDensity b endTime C (m::ms) p a *
          F (selectedWordState b endTime (m::ms) p a)) :=
      ((selectedWordDensity_measurable b endTime C (m::ms)).comp
        (measurable_const.prodMk measurable_id)).mul
      (hF.comp ((selectedWordState_measurable b endTime (m::ms)).comp
        (measurable_const.prodMk measurable_id)))
    simp only [List.length_cons]
    rw [collisionWordMeasure,lintegral_prod _ hm.aemeasurable,physicalMarkedWord,
      Kernel.lintegral_comp _ _ _ hF,
      physicalMarkedEvent_parameters b endTime C m p hF.lintegral_kernel]
    apply lintegral_congr
    intro a
    change (∫⁻ w, (physicalParameterWeight b endTime C m p a *
      selectedWordDensity b endTime C ms (mediumParameterState b endTime p (m,a)) w) *
      F (selectedWordState b endTime ms (mediumParameterState b endTime p (m,a)) w)
        ∂collisionWordMeasure ms.length) = _
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (physicalParameterWeight_ne_top b endTime C m p a),ih]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ThreeSelectedIntegral
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Three selected collisions as one time and angle integral -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem threeSelectedIntegrand_measurable (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m₀ m₁ m₂ : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    Measurable (threeSelectedIntegrand b endTime C m₀ m₁ m₂ p F) := by
  have hm : Measurable (fun q : ThreeEvents =>
      (p,((q.1,(q.2.1,(q.2.2,PUnit.unit))) : CollisionWord 3))) := by fun_prop
  exact ((selectedWordDensity_measurable b endTime C [m₀,m₁,m₂]).comp hm).mul
    (hF.comp ((selectedWordState_measurable b endTime [m₀,m₁,m₂]).comp hm))

theorem threeSelected_integral (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m₀ m₁ m₂ : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, threeSelectedIntegrand b endTime C m₀ m₁ m₂ p F q
      ∂physicalEventMeasure.prod (physicalEventMeasure.prod physicalEventMeasure)) =
      ∫⁻ q, F q ∂physicalMarkedWord b endTime C [m₀,m₁,m₂] p := by
  have hd := (MeasurePreserving.id physicalEventMeasure).prod
    ((MeasurePreserving.id physicalEventMeasure).prod
      (measurePreserving_fst (μ := physicalEventMeasure) (ν := Measure.dirac PUnit.unit)))
  rw [← hd.lintegral_comp (threeSelectedIntegrand_measurable b endTime C m₀ m₁ m₂ p hF)]
  rw [← selectedWord_integral b endTime C [m₀,m₁,m₂] p hF]
  apply lintegral_congr
  intro a
  rcases a with ⟨a₀,a₁,a₂,u⟩
  cases u
  rfl

theorem threeSelected_time_angles (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m₀ m₁ m₂ : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedWord b endTime C [m₀,m₁,m₂] p) =
      ∫⁻ s : ThreeWaits, ∫⁻ a : ThreeAngles,
        threeSelectedIntegrand b endTime C m₀ m₁ m₂ p F (joinThreeEvents s a)
          ∂sphereProbability.prod (sphereProbability.prod sphereProbability) := by
  rw [← threeSelected_integral b endTime C m₀ m₁ m₂ p hF]
  exact three_events_lintegral (threeSelectedIntegrand_measurable b endTime C m₀ m₁ m₂ p hF)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricEntry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual cold partners and densities at the three entry collisions -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryPartner₀_error {α : ℝ} (hα : 0 ≤ α) (θ η γ σ t : ℝ)
    (x v : V) (s : ThreeWaits) :
    ‖entryPartner₀ θ η α γ σ t x v s-σ • beamAxis‖ ≤ α :=
  beamVelocity_error hα θ η γ σ _

theorem entryPartner₁_error {α : ℝ} (hα : 0 ≤ α) (θ η γ σ t : ℝ)
    (x v : V) (s : ThreeWaits) (u : V) :
    ‖entryPartner₁ θ η α γ σ t x v s u-(-(σ • beamAxis))‖ ≤ α := by
  simpa only [entryPartner₁,neg_smul] using beamVelocity_error hα θ η γ (-σ) (entrySite₁ t x v s u)

theorem entryPartner₂_error {α : ℝ} (hα : 0 ≤ α) (θ η γ σ t : ℝ)
    (x v : V) (s : ThreeWaits) (u : V) (a : Sphere × Sphere) :
    ‖entryPartner₂ θ η α γ σ t x v s u a-beamAxis‖ ≤ α := by
  simpa only [entryPartner₂,one_smul] using beamVelocity_error hα θ η γ 1
    (entrySite₂ t x v s u (child u (entryPartner₁ θ η α γ σ t x v s u) a.1.1))

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The entry signs are the two physical beam marks -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryMark_ne_zero (σ : ℝ) : entryMark σ ≠ 0 := by
  unfold entryMark
  split <;> norm_num

theorem entryMark_child {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η : ℝ) (p : ℝ × V) (v : V) (n : Sphere) :
    markedChild (entryMark σ) v ((beamCoefficients hθ hα hγ η 1).plusPartner p)
      ((beamCoefficients hθ hα hγ η 1).minusPartner p) n.1 =
      child v (beamVelocity θ η α γ σ p) n.1 := by
  rcases (abs_eq (show (0:ℝ) ≤ 1 by norm_num)).mp hσ with h | h
  · subst σ
    norm_num [entryMark,markedChild,beamCoefficients]
  · subst σ
    norm_num [entryMark,markedChild,beamCoefficients]

theorem entryMark_rate {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η : ℝ) (p : ℝ × V) (v : V) :
    mediumMarkedRate (beamCoefficients hθ hα hγ η 1) (entryMark σ) (p,v) =
      ENNReal.ofReal (4*Real.pi*beamDensity θ η α γ 1 σ p*
        ‖v-beamVelocity θ η α γ σ p‖) := by
  rcases (abs_eq (show (0:ℝ) ≤ 1 by norm_num)).mp hσ with h | h
  · subst σ
    norm_num [entryMark,mediumMarkedRate,markedRate,beamCoefficients]
  · subst σ
    norm_num [entryMark,mediumMarkedRate,markedRate,beamCoefficients]

theorem mediumPoint_entry₀ (t h : ℝ) (x v : V) (s : ThreeWaits) :
    mediumPoint (t+h) (h,(x,v)) s.1 = entrySite₀ t x v s := by
  simp [mediumPoint,entrySite₀]

theorem mediumPoint_entry₁ (t h : ℝ) (x v u : V) (s : ThreeWaits) :
    mediumPoint (t+h) (h-s.1,((entrySite₀ t x v s).2,u)) s.2.1 =
      entrySite₁ t x v s u := by
  apply Prod.ext
  · simp only [mediumPoint,entrySite₁]
    ring
  · rfl

theorem mediumPoint_entry₂ (t h : ℝ) (x v u z : V) (s : ThreeWaits) :
    mediumPoint (t+h) (h-s.1-s.2.1,((entrySite₁ t x v s u).2,z)) s.2.2 =
      entrySite₂ t x v s u z := by
  apply Prod.ext
  · simp only [mediumPoint,entrySite₂]
    ring
  · rfl

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A uniform three-collision entry lower bound for the actual cold field -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_entry_lower {θ η α γ κ ρ ε L X R h t T σ : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hL : 0 < L) (hX : 0 ≤ X) (hR : 0 ≤ R) (hT0 : 0 ≤ T)
    (ht : 0 ≤ t) (hT : t+3*h ≤ T) (hsmall : (R+6)*h ≤ 1)
    (hσ : |σ| = 1) (x v : V) (hx : ‖x‖ ≤ X) (hxr : L+1 < ‖VelocityWeight.transverse x‖)
    (hv : ‖v‖ ≤ R) (hvfar : 1 ≤ ‖v-σ • beamAxis‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ThreeWaits,
      s.1 ∈ Icc 0 h → s.2.1 ∈ Icc 0 h → s.2.2 ∈ Icc 0 h →
      firstEntryMass R ε c *
        ((ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c))*
          (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2))) ≤
        entryAngularMass θ η α γ σ t x v s κ ρ := by
  obtain ⟨c,hc,hcold⟩ := nearby_beamDensity_lower hθ hη hα hγ hL hX hT0
  have he : ‖σ • beamAxis‖ = 1 := by
    rw [norm_smul,Real.norm_eq_abs,hσ,axis_norms.2.2,mul_one]
  have hαsmall : α ≤ 1/4 := by linarith
  have hαε' : α ≤ ε := by linarith
  refine ⟨c,hc,?_⟩
  intro s hs₀ hs₁ hs₂
  have hzero : ‖(0:V)‖ ≤ 3 := by norm_num
  have hsites₀ := entrySites_bounded (x := x) hR hsmall ht hT hs₀ hs₁ hs₂ hv hzero hzero
  have hbc₀ : c ≤ entryDensity₀ θ η α γ σ t x v s :=
    hcold x hx hxr _ hsites₀.1.2 _ hsites₀.1.1 σ hσ
  have hw₀ := entryPartner₀_error hα θ η γ σ t x v s
  have hw₀norm : ‖entryPartner₀ θ η α γ σ t x v s‖ ≤ 2 := by
    have hn := norm_sub_norm_le (entryPartner₀ θ η α γ σ t x v s) (σ • beamAxis)
    rw [he] at hn
    linarith
  have hfar : 3/4 ≤ ‖v-entryPartner₀ θ η α γ σ t x v s‖ := by
    have hh := nearby_partner_distance hvfar hw₀
    linarith
  have hnear : dist (entryPartner₀ θ η α γ σ t x v s) (σ • beamAxis) ≤ ε/2 := by
    rw [dist_eq_norm]
    exact hw₀.trans hαε
  have hpartners (u : V) (_hu : u ∈ ball (σ • beamAxis) ε)
      (a : Sphere × Sphere) (_ha : a ∈ accessAngles κ (ρ/2)) :
      ‖entryPartner₁ θ η α γ σ t x v s u-(-(σ • beamAxis))‖ ≤ ε ∧
        ‖entryPartner₂ θ η α γ σ t x v s u a-beamAxis‖ ≤ ε :=
    ⟨(entryPartner₁_error hα θ η γ σ t x v s u).trans hαε',
      (entryPartner₂_error hα θ η γ σ t x v s u a).trans hαε'⟩
  have hdensities (u : V) (hu : u ∈ ball (σ • beamAxis) ε)
      (a : Sphere × Sphere) (ha : a ∈ accessAngles κ (ρ/2)) :
      c ≤ entryDensity₁ θ η α γ σ t x v s u ∧
        c ≤ entryDensity₂ θ η α γ σ t x v s u a := by
    have hule : ‖u-σ • beamAxis‖ ≤ ε := le_of_lt hu
    have hu3 : ‖u‖ ≤ 3 := by
      have hh := norm_sub_norm_le u (σ • beamAxis)
      rw [he] at hh
      linarith
    obtain ⟨hw₁,hw₂⟩ := hpartners u hu a ha
    have hg := access_pair_stability hκ0 hκ hρ hε hερ he hule hw₁ hw₂ ha
    dsimp only at hg
    have hsites := entrySites_bounded (x := x) hR hsmall ht hT hs₀ hs₁ hs₂ hv hu3 hg.2.2.1
    exact ⟨hcold x hx hxr _ hsites.2.1.2 _ hsites.2.1.1 (-σ) (by simpa using hσ),
      hcold x hx hxr _ hsites.2.2.2 _ hsites.2.2.1 1 (by norm_num)⟩
  exact three_collision_access_lower hκ0 hκ hρ hε0 hε hερ hc hbc₀ hR he hv hw₀norm hfar hnear
    (fun u _ => entryPartner₁ θ η α γ σ t x v s u)
    (entryPartner₂ θ η α γ σ t x v s)
    (fun u _ => entryDensity₁ θ η α γ σ t x v s u)
    (entryDensity₂ θ η α γ σ t x v s) hpartners hdensities

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Measurability of the actual three-collision entry integral -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryAccess_measurable {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (η σ t κ ρ : ℝ) (x v : V) :
    Measurable (fun q : (ThreeWaits × V) × (Sphere × Sphere) => accessWeight q.1.2
      (fun _ => entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2)
      (entryPartner₂ θ η α γ σ t x v q.1.1 q.1.2)
      (fun _ => entryDensity₁ θ η α γ σ t x v q.1.1 q.1.2)
      (entryDensity₂ θ η α γ σ t x v q.1.1 q.1.2) κ ρ q.2) := by
  have h₁v : Measurable (fun q : ThreeWaits × V => entryPartner₁ θ η α γ σ t x v q.1 q.2) :=
    (beamVelocity_measurable hθ hα hγ η (-σ)).comp (by unfold entrySite₁; fun_prop)
  have h₁b : Measurable (fun q : ThreeWaits × V => entryDensity₁ θ η α γ σ t x v q.1 q.2) :=
    (beamDensity_measurable hθ hα hγ η 1 (-σ)).comp (by unfold entrySite₁; fun_prop)
  let P := (ThreeWaits × V) × (Sphere × Sphere)
  have h₁v' : Measurable (fun q : P => entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2) :=
    h₁v.comp measurable_fst
  have hu : Measurable (fun q : P => child q.1.2
      (entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2) q.2.1.1) := by
    unfold child
    fun_prop
  have hsite : Measurable (fun q : P => entrySite₂ t x v q.1.1 q.1.2
      (child q.1.2 (entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2) q.2.1.1)) := by
    unfold entrySite₂
    fun_prop
  have h₂v : Measurable (fun q : P => entryPartner₂ θ η α γ σ t x v q.1.1 q.1.2 q.2) :=
    (beamVelocity_measurable hθ hα hγ η 1).comp hsite
  have h₂b : Measurable (fun q : P => entryDensity₂ θ η α γ σ t x v q.1.1 q.1.2 q.2) :=
    (beamDensity_measurable hθ hα hγ η 1 1).comp hsite
  have hz : Measurable (fun q : P => child (child q.1.2
      (entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2) q.2.1.1)
      (entryPartner₂ θ η α γ σ t x v q.1.1 q.1.2 q.2) q.2.2.1) := by
    unfold child
    fun_prop
  have h₁b' := h₁b.comp (measurable_fst : Measurable (Prod.fst : P → ThreeWaits × V))
  have hm : Measurable (fun q : P => accessWeight q.1.2
      (fun _ => entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2)
      (entryPartner₂ θ η α γ σ t x v q.1.1 q.1.2)
      (fun _ => entryDensity₁ θ η α γ σ t x v q.1.1 q.1.2)
      (entryDensity₂ θ η α γ σ t x v q.1.1 q.1.2) κ ρ q.2) := by
    have hr₁ : Measurable (fun q : P => ENNReal.ofReal (4*Real.pi*
        entryDensity₁ θ η α γ σ t x v q.1.1 q.1.2*
          ‖q.1.2-entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2‖)) := by fun_prop
    have hr₂ : Measurable (fun q : P => ENNReal.ofReal (4*Real.pi*
        entryDensity₂ θ η α γ σ t x v q.1.1 q.1.2 q.2*
          ‖child q.1.2 (entryPartner₁ θ η α γ σ t x v q.1.1 q.1.2) q.2.1.1-
            entryPartner₂ θ η α γ σ t x v q.1.1 q.1.2 q.2‖)) := by fun_prop
    exact (hr₁.mul hr₂).mul ((measurable_const.indicator measurableSet_ball).comp hz)
  exact hm

theorem entryAngularMass_measurable {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (η σ t κ ρ : ℝ) (x v : V) :
    Measurable (fun s : ThreeWaits => entryAngularMass θ η α γ σ t x v s κ ρ) := by
  have h₀v : Measurable (entryPartner₀ θ η α γ σ t x v) :=
    (beamVelocity_measurable hθ hα hγ η σ).comp (by unfold entrySite₀; fun_prop)
  have h₀b : Measurable (entryDensity₀ θ η α γ σ t x v) :=
    (beamDensity_measurable hθ hα hγ η 1 σ).comp (by unfold entrySite₀; fun_prop)
  have hm := entryAccess_measurable hθ hα hγ η σ t κ ρ x v
  have hi := hm.lintegral_prod_right' (ν := sphereProbability.prod sphereProbability)
  let J : Kernel ThreeWaits V := outgoing.comap
    (fun s => (v,entryPartner₀ θ η α γ σ t x v s)) (measurable_const.prodMk h₀v)
  have hj := hi.lintegral_kernel_prod_right' (κ := J)
  exact ((measurable_const.mul h₀b).mul (measurable_const.sub h₀v).norm).ennreal_ofReal.mul hj

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The three physical state transitions follow the geometric entry path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryState_first {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    mediumParameterState (beamCoefficients hθ hα hγ η 1) (t+h)
      (h,(x,v)) (entryMark σ,(s.1,a.1)) = entryState₁ θ η α γ σ t h x v s a := by
  dsimp only [mediumParameterState]
  rw [mediumPoint_entry₀,entryMark_child hθ hα hγ hσ]
  rfl

theorem entryState_second {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    mediumParameterState (beamCoefficients hθ hα hγ η 1) (t+h)
      (entryState₁ θ η α γ σ t h x v s a) (entryMark (-σ),(s.2.1,a.2.1)) =
        entryState₂ θ η α γ σ t h x v s a := by
  dsimp only [mediumParameterState,entryState₁]
  rw [mediumPoint_entry₁,entryMark_child hθ hα hγ (by simpa only [abs_neg] using hσ)]
  rfl

theorem entryState_third {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) :
    mediumParameterState (beamCoefficients hθ hα hγ η 1) (t+h)
      (entryState₂ θ η α γ σ t h x v s a) (entryMark 1,(s.2.2,a.2.2)) =
        entryState₃ θ η α γ σ t h x v s a := by
  dsimp only [mediumParameterState,entryState₂]
  rw [mediumPoint_entry₂,entryMark_child hθ hα hγ (by norm_num : |(1:ℝ)| = 1)]
  rfl

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Physical collision weights along the three entry transitions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalParameterWeight_wait_eq (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m : HistoryMark) (p : PhysicalFlightState) (a : EventParameter)
    (hs : a.1 ∈ Ioc 0 p.1) :
    physicalParameterWeight b endTime C m p a =
      clockSurvival C a.1 * mediumMarkedRate b m (mediumPoint endTime p a.1,p.2.2) := by
  unfold physicalParameterWeight
  rw [show physicalWaitingWeight C (p,a.1) = clockSurvival C a.1 by
    simp [physicalWaitingWeight,hs.1,hs.2]]

end BoltzmannNonuniqueness.ReferenceGeometry

open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryRate_first {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) (C : ℝ≥0)
    (hs : s.1 ∈ Ioc 0 h) :
    physicalParameterWeight (beamCoefficients hθ hα hγ η 1) (t+h) C
      (entryMark σ) (h,(x,v)) (s.1,a.1) =
      clockSurvival C s.1 * ENNReal.ofReal (4*Real.pi*entryDensity₀ θ η α γ σ t x v s*
        ‖v-entryPartner₀ θ η α γ σ t x v s‖) := by
  rw [physicalParameterWeight_wait_eq _ _ _ _ _ _ hs,mediumPoint_entry₀,
    entryMark_rate hθ hα hγ hσ]
  rfl

theorem entryRate_second {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) (C : ℝ≥0)
    (hs : s.2.1 ∈ Ioc 0 (h-s.1)) :
    physicalParameterWeight (beamCoefficients hθ hα hγ η 1) (t+h) C
      (entryMark (-σ)) (entryState₁ θ η α γ σ t h x v s a) (s.2.1,a.2.1) =
      clockSurvival C s.2.1 * ENNReal.ofReal (4*Real.pi*
        entryDensity₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a)*
        ‖entryVelocity₀ θ η α γ σ t x v s a-
          entryPartner₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a)‖) := by
  rw [physicalParameterWeight_wait_eq _ _ _ _ _ _ hs]
  simp only [entryState₁]
  rw [mediumPoint_entry₁,entryMark_rate hθ hα hγ (by simpa only [abs_neg] using hσ)]
  rfl

theorem entryRate_third {θ α γ σ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (η t h : ℝ) (x v : V) (s : ThreeWaits) (a : ThreeAngles) (C : ℝ≥0)
    (hs : s.2.2 ∈ Ioc 0 (h-s.1-s.2.1)) :
    physicalParameterWeight (beamCoefficients hθ hα hγ η 1) (t+h) C
      (entryMark 1) (entryState₂ θ η α γ σ t h x v s a) (s.2.2,a.2.2) =
      clockSurvival C s.2.2 * ENNReal.ofReal (4*Real.pi*
        entryDensity₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a) a.2*
        ‖entryVelocity₁ θ η α γ σ t x v s a-
          entryPartner₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a) a.2‖) := by
  rw [physicalParameterWeight_wait_eq _ _ _ _ _ _ hs]
  simp only [entryState₂]
  rw [mediumPoint_entry₂,entryMark_rate hθ hα hγ (by norm_num : |(1:ℝ)| = 1)]
  rfl

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Exact retained weight of the three physical entry collisions -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryTerminal_measurable (C : ℝ≥0) (κ ρ : ℝ) : Measurable (entryTerminal C κ ρ) := by
  exact (show Measurable (fun p : PhysicalFlightState => clockSurvival C p.1) by
    unfold clockSurvival; fun_prop).mul
      ((measurable_const.indicator measurableSet_ball).comp (by fun_prop))

theorem entry_integrand_eq {θ α γ σ h : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hσ : |σ| = 1) (hh : 0 < h) (η t κ ρ : ℝ) (x v : V)
    (s : ThreeWaits) (hs : s ∈ threeWaitBox h) (a : ThreeAngles) (C : ℝ≥0) :
    threeSelectedIntegrand (beamCoefficients hθ hα hγ η 1) (t+h) C
      (entryMark σ) (entryMark (-σ)) (entryMark 1) (h,(x,v)) (entryTerminal C κ ρ)
        (joinThreeEvents s a) =
      clockSurvival C h * (ENNReal.ofReal (4*Real.pi*entryDensity₀ θ η α γ σ t x v s*
        ‖v-entryPartner₀ θ η α γ σ t x v s‖) *
        accessWeight (entryVelocity₀ θ η α γ σ t x v s a)
          (fun _ => entryPartner₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (entryPartner₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (fun _ => entryDensity₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (entryDensity₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a)) κ ρ a.2) := by
  obtain ⟨hs₀,hs₁,hs₂,hsum⟩ := threeWaitBox_sum hh hs
  have hw₀ : s.1 ∈ Ioc 0 h := ⟨hs₀,by linarith⟩
  have hw₁ : s.2.1 ∈ Ioc 0 (h-s.1) := ⟨hs₁,by linarith⟩
  have hw₂ : s.2.2 ∈ Ioc 0 (h-s.1-s.2.1) := ⟨hs₂,by linarith⟩
  simp only [threeSelectedIntegrand,selectedWordDensity,selectedWordState,joinThreeEvents]
  simp only [entryState_first hθ hα hγ hσ,entryState_second hθ hα hγ hσ,
    entryState_third hθ hα hγ]
  rw [entryRate_first hθ hα hγ hσ _ _ _ _ _ _ _ _ hw₀,
    entryRate_second hθ hα hγ hσ _ _ _ _ _ _ _ _ hw₁,
    entryRate_third hθ hα hγ _ _ _ _ _ _ _ _ hw₂]
  have hc : clockSurvival C s.1*clockSurvival C s.2.1*clockSurvival C s.2.2*
      clockSurvival C (h-s.1-s.2.1-s.2.2) = clockSurvival C h := by
    rw [show h-s.1-s.2.1-s.2.2 = h-(s.1+s.2.1+s.2.2) by ring]
    exact three_wait_survival C h s
  rw [← hc]
  simp only [entryTerminal,entryState₃,accessWeight,entryVelocity₁,entryVelocity₂]
  ac_rfl

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Positive collision-time mass for entry in the actual cold field -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryTimeMass_pos {θ η α γ κ ρ ε L X R h t T σ : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hh : 0 < h) (hL : 0 < L) (hX : 0 ≤ X) (hR : 0 ≤ R) (hT0 : 0 ≤ T)
    (ht : 0 ≤ t) (hT : t+3*h ≤ T) (hsmall : (R+6)*h ≤ 1)
    (hσ : |σ| = 1) (x v : V) (hx : ‖x‖ ≤ X) (hxr : L+1 < ‖VelocityWeight.transverse x‖)
    (hv : ‖v‖ ≤ R) (hvfar : 1 ≤ ‖v-σ • beamAxis‖)
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (C : ℝ≥0) :
    0 < entryTimeMass θ η α γ σ t x v κ ρ h C := by
  obtain ⟨c,hc,hbound⟩ := geometric_entry_lower hθ hη hα hγ hαε hε0 hε
    hκ0 hκ hρ hερ hL hX hR hT0 ht hT hsmall hσ x v hx hxr hv hvfar
  have hfirst : 0 < firstEntryMass R ε c := firstEntryMass_pos hR hε0 hc
  have hpair : 0 < (ENNReal.ofReal (4*Real.pi*c)*ENNReal.ofReal (3*Real.pi*c))*
      (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)) := by
    apply pos_iff_ne_zero.mpr
    exact mul_ne_zero (mul_ne_zero
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))) (ne_of_gt hA)
  have hpositive : ∀ s ∈ threeWaitBox h, 0 < entryAngularMass θ η α γ σ t x v s κ ρ := by
    intro s hs
    have hwait : h/4 ≤ h := by linarith
    have h₀ : s.1 ∈ Icc 0 h := ⟨hs.1.1.le,hs.1.2.le.trans hwait⟩
    have h₁ : s.2.1 ∈ Icc 0 h := ⟨hs.2.1.1.le,hs.2.1.2.le.trans hwait⟩
    have h₂ : s.2.2 ∈ Icc 0 h := ⟨hs.2.2.1.le,hs.2.2.2.le.trans hwait⟩
    exact (pos_iff_ne_zero.mpr (mul_ne_zero (ne_of_gt hfirst) (ne_of_gt hpair))).trans_le
      (hbound s h₀ h₁ h₂)
  have hi := threeWaitBox_integral_pos hh
    (entryAngularMass_measurable hθ hα hγ η σ t κ ρ x v) hpositive
  exact pos_iff_ne_zero.mpr (mul_ne_zero
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) (ne_of_gt hi))

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # The three outgoing sphere integral is the actual entry mass -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryAngularMass_sphere {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (η σ t κ ρ : ℝ) (x v : V) (s : ThreeWaits) :
    entryAngularMass θ η α γ σ t x v s κ ρ =
      ∫⁻ a : ThreeAngles, ENNReal.ofReal (4*Real.pi*entryDensity₀ θ η α γ σ t x v s*
        ‖v-entryPartner₀ θ η α γ σ t x v s‖) *
        accessWeight (entryVelocity₀ θ η α γ σ t x v s a)
          (fun _ => entryPartner₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (entryPartner₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (fun _ => entryDensity₁ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a))
          (entryDensity₂ θ η α γ σ t x v s (entryVelocity₀ θ η α γ σ t x v s a)) κ ρ a.2
        ∂sphereProbability.prod (sphereProbability.prod sphereProbability) := by
  have hjmap : Measurable (fun q : V × (Sphere × Sphere) => ((s,q.1),q.2)) := by
    fun_prop
  have hm := (entryAccess_measurable hθ hα hγ η σ t κ ρ x v).comp hjmap
  exact outgoing_pair_lintegral _ ENNReal.ofReal_ne_top v
    (entryPartner₀ θ η α γ σ t x v s) hm

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Positive entry mass is carried by the actual physical gain histories -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem entryTimeMass_le_history {θ α γ σ h : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hσ : |σ| = 1) (hh : 0 < h) (η t κ ρ : ℝ)
    (x v : V) (C : ℝ≥0) :
    entryTimeMass θ η α γ σ t x v κ ρ h C ≤
      ∫⁻ q, entryTerminal C κ ρ q ∂physicalMarkedWord (beamCoefficients hθ hα hγ η 1)
        (t+h) C [entryMark σ,entryMark (-σ),entryMark 1] (h,(x,v)) := by
  rw [threeSelected_time_angles _ _ _ _ _ _ _ (entryTerminal_measurable C κ ρ)]
  unfold entryTimeMass
  have hc : clockSurvival C h ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [← lintegral_const_mul' _ _ hc]
  refine le_trans (le_of_eq ?_) (setLIntegral_le_lintegral (threeWaitBox h) _)
  apply setLIntegral_congr_fun (threeWaitBox_measurable h)
  intro s hs
  dsimp only
  rw [entryAngularMass_sphere hθ hα hγ,← lintegral_const_mul' _ _ hc]
  apply lintegral_congr
  intro a
  exact (entry_integrand_eq hθ hα hγ hσ hh η t κ ρ x v s hs a C).symm

theorem entryTimeMass_le_beam_history {θ α γ σ h : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hσ : |σ| = 1) (hh : 0 < h) (η t κ ρ : ℝ)
    (x v : V) (C : ℝ≥0) :
    entryTimeMass θ η α γ σ t x v κ ρ h C ≤
      ∫⁻ q, entryTerminal C κ ρ q ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η 1)
        (t+h) C)^3) (h,(x,v)) := by
  apply (entryTimeMass_le_history hθ hα hγ hσ hh η t κ ρ x v C).trans
  apply lintegral_mono' _ le_rfl
  have hm : ∀ m ∈ [entryMark σ,entryMark (-σ),entryMark 1], m ≠ 0 := by
    intro m hm
    simp at hm
    rcases hm with rfl | rfl | rfl <;> exact entryMark_ne_zero _
  exact physicalMarkedWord_le_beam _ _ _ _ hm _

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Every bounded incoming velocity has positive entry through the two beams -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_beam_entry_positive {θ η α γ κ ρ ε L R h t : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hh : 0 < h) (hL : 0 < L) (hR : 0 ≤ R) (ht : 0 ≤ t) (hsmall : (R+6)*h ≤ 1)
    (x v : V) (hxr : L+1 < ‖VelocityWeight.transverse x‖) (hv : ‖v‖ ≤ R)
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (C : ℝ≥0) :
    0 < ∫⁻ q, entryTerminal C κ ρ q ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η 1)
      (t+h) C)^3) (h,(x,v)) := by
  have H (σ : ℝ) (hσ : |σ| = 1) (hfar : 1 ≤ ‖v-σ • beamAxis‖) :
      0 < ∫⁻ q, entryTerminal C κ ρ q ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η 1)
        (t+h) C)^3) (h,(x,v)) :=
    (entryTimeMass_pos hθ hη hα hγ hαε hε0 hε hκ0 hκ hρ hερ hh hL
      (norm_nonneg x) hR (by linarith : 0 ≤ t+3*h) ht le_rfl hsmall hσ x v le_rfl hxr hv hfar hA C).trans_le
        (entryTimeMass_le_beam_history hθ hα hγ hσ hh η t κ ρ x v C)
  rcases exists_separated_beam v with hplus | hminus
  · exact H 1 (by norm_num) (by simpa only [one_smul] using hplus)
  · exact H (-1) (by norm_num) (by simpa only [neg_one_smul,sub_neg_eq_add] using hminus)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Changing the cold density scales each physical gain intensity -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem beamDensity_mul_unit (θ η α γ r σ : ℝ) (p : ℝ × V) :
    beamDensity θ η α γ r σ p = r*beamDensity θ η α γ 1 σ p := by
  unfold beamDensity
  ring

theorem beam_gain_rate_scaling {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η : ℝ) (m : HistoryMark) (hm : m ≠ 0)
    (p : ℝ × V) (v : V) :
    mediumMarkedRate (beamCoefficients hθ hα hγ η r) m (p,v) =
      ENNReal.ofReal r * mediumMarkedRate (beamCoefficients hθ hα hγ η 1) m (p,v) := by
  fin_cases m
  · exact False.elim (hm rfl)
  · change ENNReal.ofReal (4*Real.pi*beamDensity θ η α γ r 1 p*
        ‖v-beamVelocity θ η α γ 1 p‖) =
      ENNReal.ofReal r * ENNReal.ofReal (4*Real.pi*beamDensity θ η α γ 1 1 p*
        ‖v-beamVelocity θ η α γ 1 p‖)
    rw [beamDensity_mul_unit,show 4*Real.pi*(r*beamDensity θ η α γ 1 1 p)*
      ‖v-beamVelocity θ η α γ 1 p‖ = r*(4*Real.pi*beamDensity θ η α γ 1 1 p*
        ‖v-beamVelocity θ η α γ 1 p‖) by ring,ENNReal.ofReal_mul hr]
  · change ENNReal.ofReal (4*Real.pi*beamDensity θ η α γ r (-1) p*
        ‖v-beamVelocity θ η α γ (-1) p‖) =
      ENNReal.ofReal r * ENNReal.ofReal (4*Real.pi*beamDensity θ η α γ 1 (-1) p*
        ‖v-beamVelocity θ η α γ (-1) p‖)
    rw [beamDensity_mul_unit,show 4*Real.pi*(r*beamDensity θ η α γ 1 (-1) p)*
      ‖v-beamVelocity θ η α γ (-1) p‖ = r*(4*Real.pi*beamDensity θ η α γ 1 (-1) p*
        ‖v-beamVelocity θ η α γ (-1) p‖) by ring,ENNReal.ofReal_mul hr]

theorem beam_marked_collision_scaling {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η endTime : ℝ) (m : HistoryMark) (hm : m ≠ 0)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedCollision (beamCoefficients hθ hα hγ η r) endTime m p) =
      ENNReal.ofReal r * ∫⁻ q, F q ∂physicalMarkedCollision
        (beamCoefficients hθ hα hγ η 1) endTime m p := by
  rw [physicalMarkedCollision_lintegral _ _ _ _ hF,
    physicalMarkedCollision_lintegral _ _ _ _ hF,beam_gain_rate_scaling hθ hα hγ hr η m hm]
  exact mul_assoc _ _ _

theorem beam_collision_scaling {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η endTime : ℝ) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalBeamCollision (beamCoefficients hθ hα hγ η r) endTime p) =
      ENNReal.ofReal r * ∫⁻ q, F q ∂physicalBeamCollision
        (beamCoefficients hθ hα hγ η 1) endTime p := by
  rw [physicalBeamCollision_lintegral,physicalBeamCollision_lintegral,
    beam_marked_collision_scaling hθ hα hγ hr η endTime 1 (by decide) p hF,
    beam_marked_collision_scaling hθ hα hγ hr η endTime 2 (by decide) p hF,mul_add]

theorem beam_event_scaling {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η endTime : ℝ) (C : ℝ≥0) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalBeamEvent (beamCoefficients hθ hα hγ η r) endTime C p) =
      ENNReal.ofReal r * ∫⁻ q, F q ∂physicalBeamEvent
        (beamCoefficients hθ hα hγ η 1) endTime C p := by
  rw [physicalBeamEvent,physicalBeamEvent,Kernel.lintegral_comp _ _ _ hF,
    Kernel.lintegral_comp _ _ _ hF]
  simp_rw [beam_collision_scaling hθ hα hγ hr η endTime _ hF]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # A finite physical gain history has one density factor per collision -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

theorem beam_history_scaling {θ α γ r : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hr : 0 ≤ r) (η endTime : ℝ) (C : ℝ≥0) (n : ℕ)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η r) endTime C)^n) p) =
      (ENNReal.ofReal r)^n * ∫⁻ q, F q
        ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η 1) endTime C)^n) p := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    change (∫⁻ q, F q ∂(((physicalBeamEvent (beamCoefficients hθ hα hγ η r) endTime C)^n) ∘ₖ
      physicalBeamEvent (beamCoefficients hθ hα hγ η r) endTime C) p) =
      (ENNReal.ofReal r)^(n+1) * ∫⁻ q, F q
        ∂(((physicalBeamEvent (beamCoefficients hθ hα hγ η 1) endTime C)^n) ∘ₖ
          physicalBeamEvent (beamCoefficients hθ hα hγ η 1) endTime C) p
    rw [Kernel.lintegral_comp _ _ _ hF,Kernel.lintegral_comp _ _ _ hF]
    simp_rw [ih]
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
      beam_event_scaling hθ hα hγ hr η endTime C p hF.lintegral_kernel,pow_succ]
    exact (mul_assoc _ _ _).symm

theorem geometric_density_entry_positive {θ η α γ κ ρ ε L R h t r : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hh : 0 < h) (hL : 0 < L) (hR : 0 ≤ R) (ht : 0 ≤ t) (hsmall : (R+6)*h ≤ 1)
    (x v : V) (hxr : L+1 < ‖VelocityWeight.transverse x‖) (hv : ‖v‖ ≤ R)
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (C : ℝ≥0) :
    0 < ∫⁻ q, entryTerminal C κ ρ q ∂((physicalBeamEvent (beamCoefficients hθ hα hγ η r)
      (t+h) C)^3) (h,(x,v)) := by
  rw [beam_history_scaling hθ hα hγ hr.le η (t+h) C 3 _ (entryTerminal_measurable C κ ρ)]
  apply pos_iff_ne_zero.mpr
  exact mul_ne_zero (pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr hr)))
    (ne_of_gt (geometric_beam_entry_positive hθ hη hα hγ hαε hε0 hε hκ0 hκ hρ hερ
      hh hL hR ht hsmall x v hxr hv hA C))

end BoltzmannNonuniqueness.GeometricBackground

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

/-! # The positive physical entry histories reach the late growth box -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem velocityPhaseBall_measurable (κ ρ : ℝ) : MeasurableSet (velocityPhaseBall κ ρ) :=
  measurable_snd measurableSet_ball

theorem physicalGainEndpoint_velocity_ball (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) (p : PhysicalFlightState) (κ ρ : ℝ) :
    physicalGainEndpoint b endTime C n p (velocityPhaseBall κ ρ) =
      ∫⁻ q, GeometricBackground.entryTerminal C κ ρ q ∂((physicalBeamEvent b endTime C)^n) p := by
  rw [physicalGainEndpoint_apply _ _ _ _ _ (velocityPhaseBall_measurable κ ρ)]
  apply lintegral_congr
  intro q
  rfl

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_NormalOutgoingSymmetry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalGainEndpoint_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.stateKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_pow_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DampedBoundedEndpointTransport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end BoltzmannNonuniqueness.ReferenceGeometry

end

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

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SeedEscapeMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Countably many compact phase cutoffs preserving the positive seed -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem seedPhaseCutoff_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (seedPhaseCutoff n) :=
  (seedPhaseBump n).contDiff

theorem seedPhaseCutoff_compact (n : ℕ) : HasCompactSupport (seedPhaseCutoff n) :=
  (seedPhaseBump n).hasCompactSupport

theorem seedPhaseCutoff_mem (n : ℕ) (p : WeakTime.Phase) :
    seedPhaseCutoff n p ∈ Icc (0:ℝ) 1 :=
  ⟨(seedPhaseBump n).nonneg,(seedPhaseBump n).le_one⟩

end BoltzmannNonuniqueness

end

end

section

/-! # The surviving seed gives positive physical mass outside any fixed hole -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness

theorem seedEscapeRegion_measurable (n : ℕ) (L t : ℝ) :
    MeasurableSet (seedEscapeRegion n L t) := by
  unfold seedEscapeRegion
  measurability

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteEntryPhaseBound
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Reachable regions for a fixed finite number of physical gain collisions -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finiteFlightCone_measurable (N n : ℕ) (h R : ℝ) (x : V) :
    MeasurableSet {p | finiteFlightCone N n h R x p} := by
  unfold finiteFlightCone
  measurability

theorem finiteFlightCone_initial {N : ℕ} {h R : ℝ} (hh : 0 ≤ h)
    (x v : V) (hv : ‖v‖ ≤ R) : finiteFlightCone N N h R x (h,(x,v)) := by
  exact ⟨hh,le_rfl,by simpa using hv,by simp⟩

theorem markedChild_norm_le (m : HistoryMark) (v wp wm : V) (n : Sphere)
    (hp : ‖wp‖ ≤ 2) (hm : ‖wm‖ ≤ 2) :
    ‖markedChild m v wp wm n.1‖ ≤ ‖v‖+2 := by
  have hc (w : V) (hw : ‖w‖ ≤ 2) : ‖child v w n.1‖ ≤ ‖v‖+2 := by
    have hb := child_lipschitz v w 0 0 n.1 (mem_sphere_zero_iff_norm.mp n.2)
    have hz : child 0 0 n.1 = 0 := by simp [child]
    rw [hz,sub_zero,sub_zero,sub_zero] at hb
    exact hb.trans (add_le_add le_rfl hw)
  fin_cases m
  · change ‖v‖ ≤ ‖v‖+2; linarith
  · exact hc wp hp
  · exact hc wm hm

theorem finiteFlightCone_parameter_step {N n : ℕ} {h R : ℝ} {x : V}
    (b : BeamCoefficients) (T : ℝ) {p : PhysicalFlightState}
    (hq : finiteFlightCone N (n+1) h R x p) (m : HistoryMark)
    {s : ℝ} (hs : s ∈ Icc 0 p.1) (z : Sphere)
    (hp : ‖b.plusPartner (mediumPoint T p s)‖ ≤ 2)
    (hm : ‖b.minusPartner (mediumPoint T p s)‖ ≤ 2) :
    finiteFlightCone N n h R x (mediumParameterState b T p (m,(s,z))) := by
  rcases hq with ⟨ht₀,ht,hvel,hpos⟩
  push_cast at hvel
  have hv : ‖p.2.2‖ ≤ R+2*N := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hd : ‖p.2.1+s • p.2.2-x‖ ≤ (h-(p.1-s))*(R+2*N) := by
    calc
      _ = ‖(p.2.1-x)+s • p.2.2‖ := by congr 1; module
      _ ≤ ‖p.2.1-x‖+‖s • p.2.2‖ := norm_add_le _ _
      _ = ‖p.2.1-x‖+s*‖p.2.2‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
      _ ≤ (h-p.1)*(R+2*N)+s*(R+2*N) :=
        add_le_add hpos (mul_le_mul_of_nonneg_left hv hs.1)
      _ = _ := by ring
  refine ⟨sub_nonneg.mpr hs.2,?_,?_,hd⟩
  · change p.1-s ≤ h
    linarith [hs.1]
  · change ‖markedChild m p.2.2 (b.plusPartner (mediumPoint T p s))
      (b.minusPartner (mediumPoint T p s)) z.1‖ ≤ _
    have hc := markedChild_norm_le m p.2.2 _ _ z hp hm
    linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A bounded finite collision cone stays above the cold cutoff and in a compact phase set -/
noncomputable section
open Set
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finiteFlightCone_displacement {N n : ℕ} {h R : ℝ} {x : V}
    {q : PhysicalFlightState} (hq : finiteFlightCone N n h R x q) :
    ‖q.2.1-x‖ ≤ h*(R+2*N) := by
  have hB : 0 ≤ R+2*N := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith [hq.2.2.1,norm_nonneg q.2.2]
  exact hq.2.2.2.trans (mul_le_mul_of_nonneg_right (by linarith [hq.1]) hB)

theorem finiteFlightCone_cold_domain {N n : ℕ} {t h R a η l : ℝ} {x : V}
    (ha : a ≤ t) (hl : 0 ≤ l) (hshort : h*(R+2*N) ≤ 1)
    (hx : Real.exp η*l+1 < ‖transverse x‖)
    {q : PhysicalFlightState} (hq : finiteFlightCone N n h R x q) :
    flightCharacteristicEquiv (t+h) q ∈ coldCharacteristicDomain a η l := by
  have hd := (finiteFlightCone_displacement hq).trans hshort
  have ht := norm_sub_norm_le (transverse x) (transverse q.2.1)
  have he : ‖transverse x-transverse q.2.1‖ ≤ 1 := by
    rw [← PlaneChart.transverse_sub]
    exact (LargeOutput.transverse_norm_le (x-q.2.1)).trans (by rwa [norm_sub_rev])
  have hy : Real.exp η*l < ‖transverse q.2.1‖ := by linarith
  change a ≤ t+h-q.1 ∧ 0 < ‖transverse (q.2.1-(t+h-q.1) • q.2.2+
    (t+h-q.1) • q.2.2)‖ ∧ Real.exp η*l < ‖transverse (q.2.1-(t+h-q.1) • q.2.2+
    (t+h-q.1) • q.2.2)‖
  rw [sub_add_cancel]
  exact ⟨by linarith [hq.2.1],(mul_nonneg (Real.exp_pos η).le hl).trans_lt hy,hy⟩

theorem finiteFlightCone_phase_bound {N n : ℕ} {t h R X : ℝ} {x : V}
    (ht : 0 ≤ t) (hR : 0 ≤ R) (hX : 0 ≤ X) (hx : ‖x‖ ≤ X)
    {q : PhysicalFlightState} (hq : finiteFlightCone N n h R x q) :
    ‖(flightCharacteristicEquiv (t+h) q).2‖ ≤ X+(t+2*h+1)*(R+2*N) := by
  have hh : 0 ≤ h := hq.1.trans hq.2.1
  have hB : 0 ≤ R+2*N := by positivity
  have hv : ‖q.2.2‖ ≤ R+2*N := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith [hq.2.2.1]
  have hpos : ‖q.2.1‖ ≤ X+h*(R+2*N) := by
    calc
      _ ≤ ‖q.2.1-x‖+‖x‖ := by simpa only [sub_add_cancel] using norm_add_le (q.2.1-x) x
      _ ≤ _ := by simpa only [add_comm] using add_le_add (finiteFlightCone_displacement hq) hx
  have htime : 0 ≤ t+h-q.1 := by linarith [hq.2.1]
  have hphase : ‖q.2.1-(t+h-q.1) • q.2.2‖ ≤ X+(t+2*h)*(R+2*N) := by
    apply (norm_sub_le _ _).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg htime]
    have hm := mul_le_mul_of_nonneg_left hv htime
    have hm' := mul_le_mul_of_nonneg_right (show t+h-q.1 ≤ t+h by linarith [hq.1]) hB
    nlinarith
  rw [Prod.norm_def,max_le_iff]
  exact ⟨by change ‖q.2.1-(t+h-q.1) • q.2.2‖ ≤ _; nlinarith,
    hv.trans (by nlinarith [mul_nonneg (show 0 ≤ t+2*h by positivity) hB])⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # One compact phase cutoff contains all short entry histories in a fixed time window -/
noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem phaseBallCore_measurable (M : ℝ) : MeasurableSet (phaseBallCore M) :=
  measurableSet_le measurable_snd.norm measurable_const

theorem finiteFlightCone_window_core {N n : ℕ} {s t U R X : ℝ} {x : V}
    (hs : 0 ≤ s) (ht : t ≤ U) (hR : 0 ≤ R) (hX : 0 ≤ X) (hx : ‖x‖ ≤ X)
    {q : PhysicalFlightState} (hq : finiteFlightCone N n (t-s) R x q) :
    flightCharacteristicEquiv t q ∈ phaseBallCore (X+(2*U+1)*(R+2*N)) := by
  have hb := finiteFlightCone_phase_bound hs hR hX hx hq
  have he : s+(t-s) = t := by ring
  rw [he] at hb
  change ‖(flightCharacteristicEquiv t q).2‖ ≤ _
  apply hb.trans
  have hB : 0 ≤ R+2*N := by positivity
  nlinarith [mul_le_mul_of_nonneg_right ht hB,mul_nonneg hs hB]

theorem exists_phaseBall_cutoff (M : ℝ) :
    ∃ β : WeakTime.Phase → ℝ, ContDiff ℝ (⊤ : ℕ∞) β ∧ HasCompactSupport β ∧
      (∀ p, 0 ≤ β p) ∧ (∀ p, β p ≤ 1) ∧ (∀ p, ‖p‖ ≤ M → β p = 1) := by
  obtain ⟨n,hn⟩ := exists_nat_gt M
  refine ⟨seedPhaseCutoff n,seedPhaseCutoff_smooth n,seedPhaseCutoff_compact n,
    (fun p => (seedPhaseCutoff_mem n p).1),(fun p => (seedPhaseCutoff_mem n p).2),?_⟩
  intro p hp
  apply (seedPhaseBump n).one_of_mem_closedBall
  rw [Metric.mem_closedBall,dist_zero_right]
  dsimp [seedPhaseBump]
  linarith

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

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapEscapingSeed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Concrete damping constants on compact characteristic phase sets -/

noncomputable section

open Set
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristic_frequency_compact_bound (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    {β : Velocity × Velocity → ℝ} (hc : HasCompactSupport β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : CharacteristicPhase,
      a ≤ u.1 → u.2 ∈ tsupport β → E.characteristicFrequency u ≤ C := by
  obtain ⟨V,hV,hb⟩ := hc.isCompact.isBounded.exists_pos_norm_le
  let C := (GeometricBackground.lossCoefficient K α γ/a)*(V+1+α)
  have hcoef : 0 ≤ GeometricBackground.lossCoefficient K α γ/a :=
    div_nonneg (GeometricBackground.lossCoefficient_nonneg hK α γ) ha.le
  refine ⟨C,mul_nonneg hcoef (by positivity),?_⟩
  intro u ht hu
  have hv : ‖(hotCharacteristicEquiv u).2‖ ≤ V := (norm_snd_le u.2).trans (hb _ hu)
  have hf := GeometricBackground.frequency_slab_bound (η := η)
    (zero_lt_one.trans_le E.phase_mem.1) E.fraction_mem.1 hK hα hγ ha ht
    (hotCharacteristicEquiv u).1.2 (hotCharacteristicEquiv u).2
  exact hf.trans (mul_le_mul_of_nonneg_left (by linarith only [hv]) hcoef)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalGainStrictTime
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Almost every finite physical history stays in its explicit reachable region -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finiteFlightCone_wait {N n : ℕ} {h R : ℝ} {x : V}
    {p : PhysicalFlightState} (hq : finiteFlightCone N n h R x p)
    {s : ℝ} (hs : s ∈ Icc 0 p.1) :
    finiteFlightCone N n h R x (physicalAdvance p s) := by
  have hv : ‖p.2.2‖ ≤ R+2*N := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith [hq.2.2.1]
  refine ⟨sub_nonneg.mpr hs.2,by dsimp [physicalAdvance] <;> linarith [hq.2.1,hs.1],hq.2.2.1,?_⟩
  change ‖p.2.1+s • p.2.2-x‖ ≤ (h-(p.1-s))*(R+2*N)
  calc
    _ = ‖(p.2.1-x)+s • p.2.2‖ := by congr 1; module
    _ ≤ ‖p.2.1-x‖+‖s • p.2.2‖ := norm_add_le _ _
    _ = ‖p.2.1-x‖+s*‖p.2.2‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1]
    _ ≤ (h-p.1)*(R+2*N)+s*(R+2*N) :=
      add_le_add hq.2.2.2 (mul_le_mul_of_nonneg_left hv hs.1)
    _ = _ := by ring

theorem physicalWaitingKernel_ae_finiteCone {N n : ℕ} {h R : ℝ} {x : V}
    (C : ℝ≥0) {p : PhysicalFlightState} (hq : finiteFlightCone N n h R x p) :
    ∀ᵐ q ∂physicalWaitingKernel C p, finiteFlightCone N n h R x q := by
  let A := {q | ¬finiteFlightCone N n h R x q}
  have hA : MeasurableSet A := (finiteFlightCone_measurable N n h R x).compl
  rw [ae_iff]
  change physicalWaitingKernel C p A = 0
  rw [← lintegral_indicator_one hA,physicalWaitingKernel_lintegral C p (F := A.indicator 1)
    (measurable_const.indicator hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hz : A.indicator (1 : PhysicalFlightState → ℝ≥0∞) (physicalAdvance p s) = 0 := by
    apply indicator_of_notMem
    exact fun h => h (finiteFlightCone_wait hq ⟨hs.1.le,hs.2⟩)
  simp only [hz,mul_zero,Pi.zero_apply]

theorem physicalBeamCollision_ae_finiteCone {N n : ℕ} {h R : ℝ} {x : V}
    (b : BeamCoefficients) (T : ℝ) {p : PhysicalFlightState}
    (hq : finiteFlightCone N (n+1) h R x p)
    (hp : ‖b.plusPartner (T-p.1,p.2.1)‖ ≤ 2)
    (hm : ‖b.minusPartner (T-p.1,p.2.1)‖ ≤ 2) :
    ∀ᵐ q ∂physicalBeamCollision b T p, finiteFlightCone N n h R x q := by
  let A := {q | ¬finiteFlightCone N n h R x q}
  have hA : MeasurableSet A := (finiteFlightCone_measurable N n h R x).compl
  have hz (m : HistoryMark) (z : Sphere) :
      A.indicator (1 : PhysicalFlightState → ℝ≥0∞)
        (p.1,(p.2.1,markedChild m p.2.2 (b.plusPartner (T-p.1,p.2.1))
          (b.minusPartner (T-p.1,p.2.1)) z.1)) = 0 := by
    apply indicator_of_notMem
    intro hnot
    apply hnot
    simpa only [mediumParameterState,mediumPoint,sub_zero,add_zero,zero_smul] using
      finiteFlightCone_parameter_step b T hq m ⟨le_rfl,hq.1⟩ z
        (by simpa only [mediumPoint,add_zero,zero_smul] using hp)
        (by simpa only [mediumPoint,add_zero,zero_smul] using hm)
  rw [ae_iff]
  change physicalBeamCollision b T p A = 0
  rw [← lintegral_indicator_one hA,physicalBeamCollision_lintegral,
    physicalMarkedCollision_lintegral b T 1 p (F := A.indicator 1) (measurable_const.indicator hA),
    physicalMarkedCollision_lintegral b T 2 p (F := A.indicator 1) (measurable_const.indicator hA)]
  simp only [hz,lintegral_zero,mul_zero,add_zero]

theorem physicalBeamEvent_ae_finiteCone {N n : ℕ} {h R : ℝ} {x : V}
    (b : BeamCoefficients) (T : ℝ) (C : ℝ≥0) {p : PhysicalFlightState}
    (hq : finiteFlightCone N (n+1) h R x p)
    (hp : ∀ q, finiteFlightCone N (n+1) h R x q → ‖b.plusPartner (T-q.1,q.2.1)‖ ≤ 2)
    (hm : ∀ q, finiteFlightCone N (n+1) h R x q → ‖b.minusPartner (T-q.1,q.2.1)‖ ≤ 2) :
    ∀ᵐ q ∂physicalBeamEvent b T C p, finiteFlightCone N n h R x q := by
  apply Kernel.ae_comp_of_ae_ae (finiteFlightCone_measurable N n h R x)
  filter_upwards [physicalWaitingKernel_ae_finiteCone C hq] with q hq'
  exact physicalBeamCollision_ae_finiteCone b T hq' (hp q hq') (hm q hq')

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive physical gain histories use the open-left collision-time window -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem physicalBeamCollision_ae_fixed (b : BeamCoefficients) (T : ℝ)
    (p : PhysicalFlightState) :
    ∀ᵐ q ∂physicalBeamCollision b T p, q.1 = p.1 ∧ q.2.1 = p.2.1 := by
  let A := {q : PhysicalFlightState | ¬(q.1 = p.1 ∧ q.2.1 = p.2.1)}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hz (v : V) : A.indicator (1 : PhysicalFlightState → ℝ≥0∞) (p.1,(p.2.1,v)) = 0 := by
    apply indicator_of_notMem
    simp [A]
  rw [ae_iff]
  change physicalBeamCollision b T p A = 0
  rw [← lintegral_indicator_one hA,physicalBeamCollision_lintegral,
    physicalMarkedCollision_lintegral b T 1 p (F := A.indicator 1) (measurable_const.indicator hA),
    physicalMarkedCollision_lintegral b T 2 p (F := A.indicator 1) (measurable_const.indicator hA)]
  simp only [hz,lintegral_zero,mul_zero,add_zero]

theorem physicalWaitingKernel_ae_remaining (C : ℝ≥0) (p : PhysicalFlightState) :
    ∀ᵐ q ∂physicalWaitingKernel C p, 0 ≤ q.1 ∧ q.1 < p.1 := by
  let A := {q : PhysicalFlightState | ¬(0 ≤ q.1 ∧ q.1 < p.1)}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  rw [ae_iff]
  change physicalWaitingKernel C p A = 0
  rw [← lintegral_indicator_one hA,physicalWaitingKernel_lintegral C p (F := A.indicator 1)
    (measurable_const.indicator hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hz : A.indicator (1 : PhysicalFlightState → ℝ≥0∞) (physicalAdvance p s) = 0 := by
    apply indicator_of_notMem
    change ¬¬(0 ≤ p.1-s ∧ p.1-s < p.1)
    exact not_not.mpr ⟨sub_nonneg.mpr hs.2,by linarith [hs.1]⟩
  simp only [hz,mul_zero,Pi.zero_apply]

theorem physicalBeamEvent_ae_time_window (b : BeamCoefficients) (T h : ℝ)
    (C : ℝ≥0) {p : PhysicalFlightState} (hp : p.1 ≤ h) :
    ∀ᵐ q ∂physicalBeamEvent b T C p, q ∈ physicalCollisionWindow (T-h) T := by
  apply Kernel.ae_comp_of_ae_ae (physicalCollisionWindow_measurable (T-h) T)
  filter_upwards [physicalWaitingKernel_ae_remaining C p] with q hq
  filter_upwards [physicalBeamCollision_ae_fixed b T q] with r hr
  rw [hr.1]
  exact ⟨by linarith [hq.2],by linarith [hq.1]⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_BeamGainNormalOrder
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The physical gain law lies below the localized positive normal-angle source -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem beamCharacteristic_le_retained (b : BeamCoefficients) (T C : ℝ)
    (z : CharacteristicPhase)
    (hp : 0 ≤ b.plusDensity (characteristicBeamPoint z))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint z)) :
    beamCharacteristicKernel b T z ≤ beamNormalRetainedKernel b 1 C z := by
  apply Measure.le_iff.mpr
  intro A hA
  have hf : Measurable (A.indicator (1 : CharacteristicPhase → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [← lintegral_indicator_one hA,← lintegral_indicator_one hA,
    beamNormalRetainedKernel_lintegral b 1 C z hf,
    beamNormalCharacteristicKernel_eq b T z hp hm,ENNReal.ofReal_one,one_mul]
  exact le_add_of_nonneg_right bot_le

theorem physicalBeamCollision_le_localized (b : BeamCoefficients) (T C a η l : ℝ)
    {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω) (p : PhysicalFlightState)
    (hz : flightCharacteristicEquiv T p ∈ coldCharacteristicDomain a η l)
    (hp : 0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T p)))
    (hm : 0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T p)))
    (houtput : ∀ᵐ q ∂physicalBeamCollision b T p, flightCharacteristicEquiv T q ∈ Ω) :
    physicalBeamCollision b T p ≤ localizedNormalCollision b 1 C T a η l hΩ p := by
  classical
  let e := flightCharacteristicEquiv T
  have he : transportedKernel e (beamCharacteristicKernel b T) = physicalBeamCollision b T := by
    unfold beamCharacteristicKernel
    exact transportedKernel_symm e _
  have hre : (physicalBeamCollision b T p).restrict (e ⁻¹' Ω) = physicalBeamCollision b T p :=
    Measure.restrict_eq_self_of_ae_mem houtput
  have hrestricted : (transportedKernel e ((beamCharacteristicKernel b T).restrict hΩ)) p =
      physicalBeamCollision b T p := by
    rw [transportedKernel_restrict,he,Kernel.restrict_apply,hre]
  rw [← hrestricted]
  apply Measure.le_iff.mpr
  intro A hA
  have hf : Measurable (A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [← lintegral_indicator_one hA,← lintegral_indicator_one hA,
    transportedKernel_lintegral e _ p hf,localizedNormalCollision,
    transportedKernel_lintegral e _ p hf]
  rw [localizedNormalBeamKernel,Kernel.piecewise_apply,ite_eq_left hz]
  apply lintegral_mono'
  · exact Measure.restrict_mono subset_rfl (beamCharacteristic_le_retained b T C (e p) hp hm)
  · exact le_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteGainHistoryComparison
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Every fixed finite physical gain history is dominated by the actual localized histories -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem finite_gain_history_le_localized_window
    (b : BeamCoefficients) (C : ℝ≥0) (T a η l h R : ℝ) (N : ℕ) (x v : V)
    (hh : 0 ≤ h) (hv : ‖v‖ ≤ R)
    {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω)
    (hΩcone : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q → flightCharacteristicEquiv T q ∈ Ω)
    (hpartner : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q →
      ‖b.plusPartner (T-q.1,q.2.1)‖ ≤ 2 ∧ ‖b.minusPartner (T-q.1,q.2.1)‖ ≤ 2)
    (hlocal : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q →
      flightCharacteristicEquiv T q ∈ coldCharacteristicDomain a η l ∧
      0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)) ∧
      0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q))) :
    ((physicalBeamEvent b T C)^N) (h,(x,v)) ≤
      ((localizedNormalWindowEvent b 1 C T a η l (T-h) hΩ)^N) (h,(x,v)) := by
  let D := fun n q => finiteFlightCone N n h R x q
  apply kernel_pow_le_on_depth (physicalBeamEvent b T C)
    (localizedNormalWindowEvent b 1 C T a η l (T-h) hΩ) D N _ _ N le_rfl
      (h,(x,v)) (finiteFlightCone_initial hh x v hv)
  · intro n hn p hp
    exact physicalBeamEvent_ae_finiteCone b T C hp
      (fun q hq => (hpartner (n+1) hn q hq).1)
      (fun q hq => (hpartner (n+1) hn q hq).2)
  · intro n hn p hp
    have hle : physicalBeamEvent b T C p ≤
        localizedNormalPhysicalEvent b 1 C T a η l hΩ p := by
      change (physicalBeamCollision b T ∘ₖ physicalWaitingKernel C) p ≤
        (localizedNormalCollision b 1 C T a η l hΩ ∘ₖ physicalWaitingKernel (Real.toNNReal C)) p
      rw [Real.toNNReal_coe]
      apply KernelHistoryOrder.measure_comp_mono_ae _ le_rfl
      filter_upwards [physicalWaitingKernel_ae_finiteCone C hp] with q hq
      obtain ⟨hz,hdp,hdm⟩ := hlocal (n+1) hn q hq
      apply physicalBeamCollision_le_localized b T C a η l hΩ q hz hdp hdm
      filter_upwards [physicalBeamCollision_ae_finiteCone b T hq
        (hpartner (n+1) hn q hq).1 (hpartner (n+1) hn q hq).2] with r hr
      exact hΩcone n (Nat.le_of_lt hn) r hr
    calc
      _ = (physicalBeamEvent b T C p).restrict (physicalCollisionWindow (T-h) T) :=
        (Measure.restrict_eq_self_of_ae_mem (physicalBeamEvent_ae_time_window b T h C hp.2.1)).symm
      _ ≤ _ := Measure.restrict_mono_measure hle _

theorem finite_gain_endpoint_le_localized
    (b : BeamCoefficients) (C : ℝ≥0) (T a η l h R : ℝ) (N : ℕ) (x v : V)
    (hh : 0 ≤ h) (hv : ‖v‖ ≤ R)
    {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω)
    (hΩcone : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q → flightCharacteristicEquiv T q ∈ Ω)
    (hpartner : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q →
      ‖b.plusPartner (T-q.1,q.2.1)‖ ≤ 2 ∧ ‖b.minusPartner (T-q.1,q.2.1)‖ ≤ 2)
    (hlocal : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q →
      flightCharacteristicEquiv T q ∈ coldCharacteristicDomain a η l ∧
      0 ≤ b.plusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)) ∧
      0 ≤ b.minusDensity (characteristicBeamPoint (flightCharacteristicEquiv T q)))
    {A : Set (V × V)} (hA : MeasurableSet A) :
    physicalGainEndpoint b T C N (h,(x,v)) A ≤
      (WeakTime.phaseEndpointKernel C T ∘ₖ
        ((((localizedNormalBeamKernel b 1 C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc (T-h) T))) ∘ₖ
            WeakTime.residenceKernel C T)^N))
        (flightCharacteristicEquiv T (h,(x,v))) (flight T ⁻¹' A) := by
  rw [physicalGainEndpoint_apply b T C N _ hA]
  have hle := lintegral_mono' (finite_gain_history_le_localized_window b C T a η l h R N x v
    hh hv hΩ hΩcone hpartner hlocal) (le_refl
      (fun q : PhysicalFlightState => clockSurvival C q.1*A.indicator 1 (finishMediumFlight q)))
  have heq := localizedNormal_endpoint_characteristic b 1 C T a η l (T-h) hΩ N
    (h,(x,v)) (f := A.indicator (1 : V × V → ℝ≥0∞))
    (measurable_const.indicator hA)
  apply hle.trans_eq
  rw [heq,← lintegral_indicator_one ((flight_measurePreserving T).measurable hA)]
  apply lintegral_congr
  intro q
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

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

/-! # Actual geometric gain histories enter the localized normal-angle comparison -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.GeometricBackground

theorem beamPartner_norm_le_two {θ α γ : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hαsmall : α ≤ 1) (η r : ℝ) (p : ℝ × Velocity) :
    ‖(beamCoefficients hθ hα hγ η r).plusPartner p‖ ≤ 2 ∧
    ‖(beamCoefficients hθ hα hγ η r).minusPartner p‖ ≤ 2 := by
  have hb (σ : ℝ) (hσ : |σ| = 1) : ‖beamVelocity θ η α γ σ p‖ ≤ 2 := by
    have he := beamVelocity_error hα θ η γ σ p
    have ht := norm_sub_norm_le (beamVelocity θ η α γ σ p) (σ • beamAxis)
    rw [norm_smul,Real.norm_eq_abs,hσ,axis_norms.2.2,mul_one] at ht
    linarith
  exact ⟨hb 1 (by norm_num),hb (-1) (by norm_num)⟩

theorem geometric_finite_gain_endpoint_le
    {θ η α γ r t h R a l : ℝ} (hθ : 0 < θ) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hαsmall : α ≤ 1) (hr : 0 ≤ r) (hh : 0 ≤ h) (ha : a ≤ t) (hl : 0 ≤ l)
    (N : ℕ) (hshort : h*(R+2*N) ≤ 1) (x v : Velocity)
    (hx : Real.exp η*l+1 < ‖VelocityWeight.transverse x‖) (hv : ‖v‖ ≤ R)
    (C : ℝ≥0) {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω)
    (hΩcone : ∀ n ≤ N, ∀ q, finiteFlightCone N n h R x q →
      flightCharacteristicEquiv (t+h) q ∈ Ω)
    {A : Set (Velocity × Velocity)} (hA : MeasurableSet A) :
    physicalGainEndpoint (beamCoefficients hθ hα hγ η r) (t+h) C N (h,(x,v)) A ≤
      (WeakTime.phaseEndpointKernel C (t+h) ∘ₖ
        ((((localizedNormalBeamKernel (beamCoefficients hθ hα hγ η r) 1 C a η l hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc t (t+h)))) ∘ₖ
            WeakTime.residenceKernel C (t+h))^N))
        (flightCharacteristicEquiv (t+h) (h,(x,v))) (flight (t+h) ⁻¹' A) := by
  have he : t+h-h = t := by ring
  simpa only [he] using finite_gain_endpoint_le_localized
    (beamCoefficients hθ hα hγ η r) C (t+h) a η l h R N x v hh hv hΩ hΩcone
    (fun _ _ q _ => beamPartner_norm_le_two hθ hα hγ hαsmall η r (t+h-q.1,q.2.1))
    (fun _ _ q hq => ⟨finiteFlightCone_cold_domain ha hl hshort hx hq,
      beamDensity_nonneg hθ hα hγ hr η 1 _,beamDensity_nonneg hθ hα hγ hr η (-1) _⟩) hA

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Positive three-collision entry in the localized normal-angle history law -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.GeometricBackground

theorem localized_three_entry_positive {θ η α γ κ ρ ε L R h t r a l : ℝ}
    (hθ : 0 < θ) (hη : 0 < η) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (hαε : α ≤ ε/2) (hε0 : 0 < ε) (hε : ε ≤ 1/12)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1) (hερ : 6*ε ≤ ρ)
    (hh : 0 < h) (hL : 0 < L) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (hsmall : (R+6)*h ≤ 1) (ha : a ≤ t) (hl : 0 ≤ l)
    (hcut : Real.exp η*l ≤ L) (x v : Velocity)
    (hxr : L+1 < ‖VelocityWeight.transverse x‖) (hv : ‖v‖ ≤ R)
    (hA : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (C : ℝ≥0) {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω)
    (hΩcone : ∀ n ≤ 3, ∀ q, finiteFlightCone 3 n h R x q →
      flightCharacteristicEquiv (t+h) q ∈ Ω) :
    0 < (WeakTime.phaseEndpointKernel C (t+h) ∘ₖ
      ((((localizedNormalBeamKernel (beamCoefficients hθ hα hγ η r) 1 C a η l hΩ).restrict
        (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc t (t+h)))) ∘ₖ
          WeakTime.residenceKernel C (t+h))^3))
      (flightCharacteristicEquiv (t+h) (h,(x,v)))
      (flight (t+h) ⁻¹' velocityPhaseBall κ ρ) := by
  have hp : 0 < physicalGainEndpoint (beamCoefficients hθ hα hγ η r) (t+h) C 3
      (h,(x,v)) (velocityPhaseBall κ ρ) := by
    rw [physicalGainEndpoint_velocity_ball]
    exact geometric_density_entry_positive hθ hη hα hγ hr hαε hε0 hε hκ0 hκ hρ hερ
      hh hL hR ht hsmall x v hxr hv hA C
  apply hp.trans_le
  apply geometric_finite_gain_endpoint_le hθ hα hγ (by linarith) hr.le hh.le ha hl 3
    (by convert hsmall using 1; ring) x v
    (by linarith) hv C hΩ hΩcone (velocityPhaseBall_measurable κ ρ)

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CommonStartGeometry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The common finite block written at an arbitrary characteristic starting phase -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightCharacteristic_from_phase (s Δ : ℝ) (p : WeakTime.Phase) :
    flightCharacteristicEquiv (s+Δ) (Δ,flight s p) = (s,p) := by
  change (s+Δ-Δ,((p.1+s • p.2)-(s+Δ-Δ) • p.2,p.2)) = (s,p)
  simp only [add_sub_cancel_right,add_sub_cancel_right]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapAnnularMassGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Three actual collisions transfer any escaped hot seed into the entry velocities -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.entry_window_q80_oai
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {κ ρ ε a U V : ℝ} (hκ : 0 ≤ κ) (hκmax : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1/12) (hαε : α ≤ ε/2) (hερ : 6*ε ≤ ρ)
    (haccess : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (ha : 0 < a) (haU : a < U) (hUV : U < V) (hV : ENNReal.ofReal V < E.horizon)
    (n : ℕ) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a U → t ∈ Ioo a U →
      0 < t-s → ((n:ℝ)+6)*(t-s) ≤ 1 →
      0 < hotPhaseSlice E.hotLimit s
        (flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s) →
      0 < hotPhaseSlice E.hotLimit t (flight t ⁻¹' velocityPhaseBall κ ρ) := by
  have hU : 0 < U := ha.trans haU
  have hl : 0 ≤ E.fraction := E.fraction_mem.1
  let X := (n:ℝ)*(1+U)
  let M := X+(2*U+1)*((n:ℝ)+6)
  obtain ⟨β,hβ,hβc,hβn,hβ₁,hβone⟩ := exists_phaseBall_cutoff M
  let Ω := phaseBallCore M
  have hΩ : MeasurableSet Ω := phaseBallCore_measurable M
  obtain ⟨C,hC,hfreq⟩ := E.toHotLimitExtraction.characteristic_frequency_compact_bound
    ha hK.le hα hγ hβc
  have hX : 0 ≤ X := by dsimp [X] <;> positivity
  have hxbound (s : ℝ) (hs : s ∈ Ioo a U) (p : WeakTime.Phase)
      (hp : p ∈ flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s) :
      ‖(flight s p).1‖ ≤ X := by
    apply hp.2.1.trans
    exact mul_le_mul_of_nonneg_left (by linarith [hs.2] : 1+s ≤ 1+U) (Nat.cast_nonneg n)
  have hstart (s : ℝ) (hs : s ∈ Ioo a U) (p : WeakTime.Phase)
      (hp : p ∈ flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s) : β p = 1 := by
    apply hβone
    have hb := finiteFlightCone_window_core (N := 3) (n := 3) (s := s) (t := s) (U := U)
      (ha.le.trans hs.1.le) hs.2.le (Nat.cast_nonneg n) hX (hxbound s hs p hp)
      (finiteFlightCone_initial (N := 3) (h := s-s) (by linarith)
        (flight s p).1 (flight s p).2 hp.2.2)
    norm_num only [Nat.cast_ofNat,sub_self,show (2:ℝ)*3=6 by norm_num] at hb
    have he := flightCharacteristic_from_phase s 0 p
    simp only [add_zero] at he
    change flightCharacteristicEquiv s (0,p.1+s • p.2,p.2) = (s,p) at he
    change flightCharacteristicEquiv s (0,p.1+s • p.2,p.2) ∈ phaseBallCore M at hb
    rw [he] at hb
    exact hb
  have hscale : K/(4*(K/4)) = (1:ℝ) := by field_simp
  have hCeq : ((Real.toNNReal C : ℝ≥0) : ℝ) = C := Real.coe_toNNReal C hC
  have hh := E.positive_history_transfer_q80 hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK.le
    hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haU hUV hV hC
    (r := K/4) (by positivity) hβ hβc hβn hβ₁
    (fun u hu hp => hfreq u hu.1.le hp) hΩ (fun z hz => hβone z.2 hz)
    (fun t => flight t ⁻¹' velocityPhaseBall κ ρ)
    (fun s => flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s)
    (fun t => (flight_measurePreserving t).measurable (velocityPhaseBall_measurable κ ρ))
    (fun s => (flight_measurePreserving s).measurable (seedEscapeRegion_measurable n _ s))
    hstart 3 (fun s t => 0 < t-s ∧ ((n:ℝ)+6)*(t-s) ≤ 1)
    (fun s _ t _ h => by linarith [h.1]) (by
      intro s hs t ht hst p hp
      rw [hscale]
      have hcore : ∀ j ≤ 3, ∀ z, finiteFlightCone 3 j (t-s) (n:ℝ) (flight s p).1 z →
          flightCharacteristicEquiv (s+(t-s)) z ∈ Ω := by
        intro j _hj z hz
        have he : s+(t-s) = t := by ring
        rw [he]
        simpa only [Nat.cast_ofNat,show (2:ℝ)*3=6 by norm_num] using
          finiteFlightCone_window_core (ha.le.trans hs.1.le) ht.2.le
            (Nat.cast_nonneg n) hX (hxbound s hs p hp) hz
      have hl := GeometricBackground.localized_three_entry_positive
        (zero_lt_one.trans_le E.phase_mem.1) hη hα.le hγ.le (by positivity : 0 < K/4)
        hαε hε hεmax hκ hκmax hρ hερ hst.1
        (by positivity : 0 < Real.exp η*E.fraction+1) (Nat.cast_nonneg n)
        (ha.le.trans hs.1.le) hst.2 hs.1.le E.fraction_mem.1 (by linarith)
        (flight s p).1 (flight s p).2 (by linarith [hp.1]) hp.2.2 haccess
        (Real.toNNReal C) hΩ hcore
      have he : s+(t-s) = t := by ring
      rw [hCeq,he] at hl
      have hep := flightCharacteristic_from_phase s (t-s) p
      rw [he] at hep
      change flightCharacteristicEquiv t (t-s,(flight s p).1,(flight s p).2) = (s,p) at hep
      rw [hep] at hl
      exact hl)
  filter_upwards [hh] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst hshort hm
  exact ht hsa hta ⟨hst,hshort⟩ hm

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.entry_window_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.entry_window_q80_oai
