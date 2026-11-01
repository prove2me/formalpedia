-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniform_damped_finite_block_growth_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:28:28.356594+00:00
-- url     : https://prove2.me/submissions/88859338-91f1-4dd7-ab39-43587cf7fb97

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceCollisionGeometry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.stateKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_pow_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.incomingChart_zero _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.normalChart_zero _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# The hard-sphere offspring sphere and reference collision rate

The one-child sphere law gives geometric identities for conservation of
momentum and energy, and bounds for the two-beam collision frequency.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem child_pair_energy (v w n : V) (hn : ‖n‖ = 1) :
    ‖child v w n‖ ^ 2 + ‖child v w (-n)‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  rw [child_energy v w n hn, child_energy v w (-n) (by simpa using hn), inner_neg_right]
  ring

theorem child_energy_le_total (v w n : V) (hn : ‖n‖ = 1) :
    ‖child v w n‖ ^ 2 ≤ ‖v‖ ^ 2 + ‖w‖ ^ 2 := by
  have h := child_pair_energy v w n hn
  nlinarith only [h, sq_nonneg ‖child v w (-n)‖]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Stability of the finite collision paths used in the branching block -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem child_neg (v w n : V) : child (-v) (-w) (-n) = -child v w n := by
  have he : -v - -w = -(v-w) := by abel
  simp only [child,he,norm_neg,← neg_add,smul_neg]

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

/-! # The normalized outgoing-sphere kernel for reference collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem outgoing_energy_support (p : V × V) :
    outgoing p {v | ‖v‖^2 ≤ ‖p.1‖^2+‖p.2‖^2} = 1 := by
  have hm : Measurable (fun n : Sphere => child p.1 p.2 n.1) := by unfold child; fun_prop
  rw [outgoing_apply,Measure.map_apply hm (measurableSet_le (by fun_prop) measurable_const)]
  have he : (fun n : Sphere => child p.1 p.2 n.1) ⁻¹' {v | ‖v‖^2 ≤ ‖p.1‖^2+‖p.2‖^2} = univ := by
    ext n
    simp only [mem_preimage,mem_ofPred_eq,mem_univ,iff_true]
    apply child_energy_le_total
    simpa only [Metric.mem_sphere,dist_zero_right] using n.2
  rw [he,measure_univ]

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

theorem outgoing_small_region (v e : V) (hv : ‖v‖ ≤ 4) (he : ‖e‖ = 1) :
    outgoing (v,e) referenceRegion = 1 := by
  have hsub : {w : V | ‖w‖^2 ≤ ‖v‖^2+‖e‖^2} ⊆ referenceRegion := by
    intro w hw
    change ‖w‖^2 ≤ ‖v‖^2+‖e‖^2 at hw
    change dist w 0 ≤ 5
    rw [dist_zero_right]
    rw [he] at hw
    nlinarith [norm_nonneg v,norm_nonneg w]
  apply le_antisymm prob_le_one
  rw [← outgoing_energy_support (v,e)]
  exact measure_mono hsub

theorem retention_small (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 4) : retention e v = 1 := by
  rw [retention,referenceJump_measure,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    outgoing_small_region v e hv he,outgoing_small_region v (-e) hv (by simpa using he)]
  simp only [smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_add (plusProbability_mem e v).1
    (sub_nonneg.mpr (plusProbability_mem e v).2)]
  simp

theorem retainedJump_small (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 4) :
    retainedJump e v = referenceJump e v := by
  have hr : referenceRegion ∈ ae (referenceJump e v) :=
    (mem_ae_iff_prob_eq_one referenceRegion_measurable).mpr (retention_small e v he hv)
  rw [retainedJump_apply,retention_small e v he hv,inv_one,one_smul]
  exact Measure.restrict_eq_self_of_ae_mem hr

theorem two_beam_distance_upper_small (v e : V) (hv : ‖v‖ ≤ 2) (he : ‖e‖ = 1) :
    ‖v-e‖+‖v+e‖ ≤ 6 := by
  have hm := norm_sub_le v e
  have hp := norm_add_le v e
  rw [he] at hm hp
  linarith

theorem plusProbability_lower_small (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 2)
    (hr : 1 ≤ ‖v-e‖) : (1/6 : ℝ) ≤ plusProbability e v := by
  have hpos : 0 < ‖v-e‖+‖v+e‖ :=
    lt_of_lt_of_le (by norm_num) (two_beam_distance_lower v e he)
  rw [plusProbability,le_div_iff₀ hpos]
  have hb := two_beam_distance_upper_small v e hv he
  linarith

theorem minusProbability_lower_small (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 2)
    (hr : 1 ≤ ‖v+e‖) : (1/6 : ℝ) ≤ 1-plusProbability e v := by
  have hpos : 0 < ‖v-e‖+‖v+e‖ :=
    lt_of_lt_of_le (by norm_num) (two_beam_distance_lower v e he)
  rw [minusProbability_eq e v he,le_div_iff₀ hpos]
  have hb := two_beam_distance_upper_small v e hv he
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Velocity reversal symmetry of the actual retained reference law -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem sphereProbability_neg : sphereProbability.map (Neg.neg : Sphere → Sphere) = sphereProbability := by
  rw [sphereProbability,Measure.map_smul, sphereArea_antipodal.map_eq]

theorem outgoing_neg (v e : V) :
    (outgoing (v,e)).map (Neg.neg : V → V) = outgoing (-v,-e) := by
  have hm (a b : V) : Measurable (fun n : Sphere => child a b n.1) := by unfold child; fun_prop
  rw [outgoing_apply,outgoing_apply,Measure.map_map measurable_neg (hm v e)]
  conv_rhs => rw [← sphereProbability_neg,Measure.map_map (hm (-v) (-e)) measurable_neg]
  congr 1
  funext n
  exact (child_neg v e n.1).symm

theorem plusProbability_neg (e v : V) (he : ‖e‖ = 1) :
    plusProbability e (-v) = 1-plusProbability e v := by
  rw [minusProbability_eq e v he,plusProbability]
  have hm : ‖-v-e‖ = ‖v+e‖ := by rw [show -v-e = -(v+e) by module,norm_neg]
  have hp : ‖-v+e‖ = ‖v-e‖ := by rw [show -v+e = -(v-e) by module,norm_neg]
  rw [hm,hp]
  congr 1
  exact add_comm _ _

theorem referenceJump_neg (e v : V) (he : ‖e‖ = 1) :
    (referenceJump e v).map (Neg.neg : V → V) = referenceJump e (-v) := by
  rw [referenceJump_measure,referenceJump_measure,Measure.map_add,Measure.map_smul,
    Measure.map_smul,outgoing_neg,outgoing_neg,neg_neg,plusProbability_neg e v he]
  · have hh : 1-(1-plusProbability e v) = plusProbability e v := by ring
    rw [hh,add_comm]
  all_goals first
    | exact (measurable_neg : Measurable (Neg.neg : V → V))
    | exact (measurable_neg : Measurable (Neg.neg : V → V)).aemeasurable

theorem referenceRegion_neg_preimage : (Neg.neg : V → V) ⁻¹' referenceRegion = referenceRegion := by
  ext v
  simp [referenceRegion,Metric.mem_closedBall,dist_zero_right]

theorem retention_neg (e v : V) (he : ‖e‖ = 1) : retention e (-v) = retention e v := by
  have h := congrArg (fun μ : Measure V => μ referenceRegion) (referenceJump_neg e v he)
  rw [Measure.map_apply measurable_neg referenceRegion_measurable,referenceRegion_neg_preimage] at h
  exact h.symm

theorem retainedJump_neg (e v : V) (he : ‖e‖ = 1) :
    (retainedJump e v).map (Neg.neg : V → V) = retainedJump e (-v) := by
  have hr : ((referenceJump e v).restrict referenceRegion).map (Neg.neg : V → V) =
      (referenceJump e (-v)).restrict referenceRegion := by
    rw [← referenceRegion_neg_preimage,← Measure.restrict_map measurable_neg referenceRegion_measurable,
      referenceJump_neg e v he,referenceRegion_neg_preimage]
  rw [retainedJump_apply,retainedJump_apply,Measure.map_smul,hr,retention_neg e v he]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Sphere probability is invariant under velocity isometries -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem sphereRotation_cone (e : V ≃ₗᵢ[ℝ] V) (A : Set Sphere) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' ((sphereRotation e) ⁻¹' A)) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' A)) := by
  ext x
  constructor
  · rintro ⟨r,hr,n,⟨m,hm,rfl⟩,rfl⟩
    exact ⟨r,hr,e m,⟨sphereRotation e m,hm,rfl⟩,by simp⟩
  · rintro ⟨r,hr,n,⟨m,hm,rfl⟩,he⟩
    refine ⟨r,hr,e.symm m,⟨(sphereRotation e).symm m,?_,rfl⟩,?_⟩
    · change sphereRotation e ((sphereRotation e).symm m) ∈ A
      simpa using hm
    · calc
        r • e.symm (m : V) = e.symm (r • (m : V)) := by simp
        _ = x := (congrArg e.symm he).trans (e.symm_apply_apply x)

theorem sphereRotation_area (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) sphereArea sphereArea := by
  refine ⟨(sphereRotation e).measurable,Measure.ext fun A hA => ?_⟩
  rw [Measure.map_apply (sphereRotation e).measurable hA]
  rw [sphereArea,(volume : Measure V).toSphere_apply' ((sphereRotation e).measurable hA),
    (volume : Measure V).toSphere_apply' hA,sphereRotation_cone]
  rw [e.measurePreserving.measure_preimage_emb e.toHomeomorph.measurableEmbedding]

theorem sphereRotation_probability (e : V ≃ₗᵢ[ℝ] V) :
    MeasurePreserving (sphereRotation e) sphereProbability sphereProbability := by
  refine ⟨(sphereRotation e).measurable,?_⟩
  rw [sphereProbability,Measure.map_smul,(sphereRotation_area e).map_eq]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The transverse collision point used in the three-collision minorization -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem minorization_child_zero : child firstAxis beamAxis minorizationNormal = 0 := by
  rw [child,first_beam_norms.2,minorizationNormal,smul_smul]
  have hs : (Real.sqrt 2/2)*(-(Real.sqrt 2)⁻¹) = -(1/2 : ℝ) := by
    field_simp
  rw [hs]
  module

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

theorem outgoing_endpoint_cap {δ : ℝ} (hδ : 0 < δ) (v e b : V)
    (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 5) (n : Sphere)
    (hn : dist (child v e n.1) b ≤ δ/2) :
    sphereCapMass (δ/12) ≤ (outgoing (v,e)).real (Metric.ball b δ) := by
  have hsub : Metric.ball n (δ/12) ⊆
      (fun m : Sphere => child v e m.1) ⁻¹' Metric.ball b δ := by
    intro m hm
    have hd : dist (m : V) (n : V) < δ/12 := hm
    have hr : ‖v-e‖ ≤ 6 := (norm_sub_le v e).trans (by rw [he]; linarith)
    have ht := dist_triangle (child v e m.1) (child v e n.1) b
    rw [child_angular_distance] at ht
    have hp := mul_le_mul_of_nonneg_right hr (dist_nonneg : 0 ≤ dist (m : V) (n : V))
    change dist (child v e m.1) b < δ
    nlinarith
  have hh := (sphere_cap_lower (by positivity : 0 < δ/12) n).trans (measureReal_mono hsub)
  rw [Measure.real,outgoing_apply,Measure.map_apply (by unfold child; fun_prop) measurableSet_ball]
  exact hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Volume distortion needed for the reference collision chart -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lipschitz_volume_image_le {f : V → V} {s : Set V} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) :
    volume (f '' s) ≤ (K : ℝ≥0∞)^3 * volume s := by
  let μ : Measure V := Measure.hausdorffMeasure (Module.finrank ℝ V)
  let c := Measure.addHaarScalarFactor μ volume
  have hm : μ = c • volume := isAddLeftInvariant_eq_smul μ volume
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume
  have hh := hf.hausdorffMeasure_image_le
    (show 0 ≤ (Module.finrank ℝ V : ℝ) from Nat.cast_nonneg _)
  change μ (f '' s) ≤ (K : ℝ≥0∞) ^ (Module.finrank ℝ V : ℝ) * μ s at hh
  rw [hm] at hh
  have hd : Module.finrank ℝ V = 3 := by simp
  rw [hd,ENNReal.rpow_natCast] at hh
  simp only [Measure.smul_apply,ENNReal.smul_def,smul_eq_mul] at hh
  apply (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp
  simpa only [mul_comm,mul_left_comm,mul_assoc] using hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lower volume distortion on a chart with a controlled inverse -/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem antilipschitzOn_volume_image_le {f : V → V} {S T : Set V} {K : ℝ≥0}
    (hf : AntilipschitzWith K (S.domRestrict f)) (hT : T ⊆ S) :
    volume T ≤ (K : ℝ≥0∞)^3 * volume (f '' T) := by
  have hinj : InjOn f S := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hf.injective (show S.domRestrict f ⟨x,hx⟩ =
      S.domRestrict f ⟨y,hy⟩ from hxy))
  have hm : MapsTo (invFunOn f S) (f '' S) S := fun _ hy => invFunOn_mem hy
  have hr : RightInvOn (invFunOn f S) f (f '' S) := fun _ hy => invFunOn_eq hy
  have hL : LipschitzOnWith K (invFunOn f S) (f '' S) := by
    intro x hx y hy
    exact (hf.to_rightInvOn' hm hr) ⟨x,hx⟩ ⟨y,hy⟩
  calc
    volume T = volume (invFunOn f S '' (f '' T)) :=
      congrArg volume (hinj.invFunOn_image hT).symm
    _ ≤ (K : ℝ≥0∞)^3 * volume (f '' T) :=
      lipschitz_volume_image_le (hL.mono (image_mono hT))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceAngularCharts
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.stateKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniformizedKernel_pow_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local unit-sphere coordinates at the minorization collision -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

@[simp] theorem minorizationChart_zero : minorizationChart 0 = 0 := by
  simp [minorizationChart,minorization_child_zero]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A radial extension of the outgoing angular chart -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem normalRadialChart_hasFDerivAt :
    HasFDerivAt normalRadialChart normalRadialDerivative 0 := by
  have h := ((EuclideanSpace.proj 0 : V →L[ℝ] ℝ).hasFDerivAt.const_add (1/2 : ℝ)).smul
    normalChart_hasFDerivAt
  refine h.congr_fderiv (Eq.symm ?_)
  · ext1 z
    simp [normalRadialDerivative,add_comm]

theorem normalRadialChart_contDiffAt : ContDiffAt ℝ 1 normalRadialChart 0 := by
  exact (contDiffAt_const.add (EuclideanSpace.proj 0 : V →L[ℝ] ℝ).contDiff.contDiffAt).smul
    normalChart_contDiffAt

theorem normalRadialChart_hasStrictFDerivAt :
    HasStrictFDerivAt normalRadialChart (normalRadialEquiv : V →L[ℝ] V) 0 := by
  apply normalRadialChart_contDiffAt.hasStrictFDerivAt' _ (by norm_num)
  exact normalRadialChart_hasFDerivAt

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Radial volume estimates for the outgoing angular chart -/

noncomputable section

open MeasureTheory Set Metric
open scoped Topology ENNReal NNReal RealInnerProductSpace Pointwise

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem angularSphere_measurable : Measurable angularSphere := by
  apply Measurable.subtype_mk
  unfold normalChart NormedSpace.normalize
  fun_prop

theorem normalRadialChart_volume_lower :
    ∃ (r : ℝ) (K : ℝ≥0), 0 < r ∧ r ≤ 1/4 ∧ 0 < K ∧
      ∀ T : Set V, T ⊆ ball (0 : V) r →
        volume T ≤ (K : ℝ≥0∞)^3 * volume (normalRadialChart '' T) := by
  obtain ⟨S,hS0,hS,happrox⟩ := normalRadialChart_hasStrictFDerivAt.approximates_deriv_on_open_nhds
  have hN : 0 < ‖(normalRadialEquiv.symm : V →L[ℝ] V)‖₊ :=
    normalRadialEquiv.nnnorm_symm_pos
  have hc : ‖(normalRadialEquiv.symm : V →L[ℝ] V)‖₊⁻¹/2 <
      ‖(normalRadialEquiv.symm : V →L[ℝ] V)‖₊⁻¹ :=
    NNReal.half_lt_self (ne_of_gt (inv_pos.mpr hN))
  let K := (‖(normalRadialEquiv.symm : V →L[ℝ] V)‖₊⁻¹-
    ‖(normalRadialEquiv.symm : V →L[ℝ] V)‖₊⁻¹/2)⁻¹
  have hK : 0 < K := inv_pos.mpr (tsub_pos_iff_lt.mpr hc)
  obtain ⟨r,hr,hrS⟩ := Metric.isOpen_iff.mp hS 0 hS0
  refine ⟨min r (1/4),K,lt_min hr (by norm_num),min_le_right _ _,hK,?_⟩
  intro T hT
  exact antilipschitzOn_volume_image_le (happrox.antilipschitz (Or.inr hc))
    (hT.trans ((ball_subset_ball (min_le_left _ _)).trans hrS))

theorem normalRadialChart_mem_cone {r : ℝ} (hr : r ≤ 1/4) {A : Set Sphere}
    {z : V} (hz : z ∈ ball (0 : V) r) (hA : angularSphere z ∈ A) :
    normalRadialChart z ∈ Ioo (0 : ℝ) 1 • (Subtype.val '' A) := by
  have hn : ‖z‖ < r := by simpa only [mem_ball,dist_zero_right] using hz
  have hcoord : |z 0| ≤ ‖z‖ := PiLp.norm_apply_le z 0
  have hlo := neg_abs_le (z 0)
  have hup := le_abs_self (z 0)
  refine ⟨(1/2 : ℝ)+z 0,⟨by linarith,by linarith⟩,normalChart z,?_,rfl⟩
  exact ⟨angularSphere z,hA,rfl⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Parameter volume is controlled by actual outgoing sphere area -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal Pointwise

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem sphere_cone_volume_le {A : Set Sphere} (hA : MeasurableSet A) :
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' A)) ≤ sphereArea A := by
  have he : sphereArea A = (3 : ℝ≥0∞) *
      volume (Ioo (0 : ℝ) 1 • (Subtype.val '' A)) := by
    simpa only [sphereArea,finrank_euclideanSpace,Fintype.card_fin,Nat.cast_ofNat] using
      (volume : Measure V).toSphere_apply' hA
  rw [he]
  calc
    volume (Ioo (0 : ℝ) 1 • (Subtype.val '' A)) =
        (1 : ℝ≥0∞) * volume (Ioo (0 : ℝ) 1 • (Subtype.val '' A)) := (one_mul _).symm
    _ ≤ _ := by gcongr; norm_num

theorem angularSphere_measure_bound :
    ∃ (r : ℝ) (K : ℝ≥0), 0 < r ∧ 0 < K ∧
      (volume.restrict (ball (0 : V) r)).map angularSphere ≤
        (K : ℝ≥0∞)^3 • sphereArea := by
  obtain ⟨r,K,hr,hrq,hK,hbound⟩ := normalRadialChart_volume_lower
  refine ⟨r,K,hr,hK,Measure.le_iff.mpr ?_⟩
  intro A hA
  rw [Measure.map_apply angularSphere_measurable hA,
    Measure.restrict_apply (angularSphere_measurable hA),Measure.smul_apply,smul_eq_mul]
  let T := angularSphere ⁻¹' A ∩ ball (0 : V) r
  have hT : T ⊆ ball (0 : V) r := inter_subset_right
  have hcone : normalRadialChart '' T ⊆ Ioo (0 : ℝ) 1 • (Subtype.val '' A) := by
    rintro _ ⟨z,hz,rfl⟩
    exact normalRadialChart_mem_cone hrq hz.2 hz.1
  refine (hbound T hT).trans ?_
  gcongr 1
  exact (measure_mono hcone).trans (sphere_cone_volume_le hA)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Splitting the inactive radial coordinate from angular parameters -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem angularSplit_measurePreserving : MeasurePreserving angularSplit :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).trans
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurePreserving.id volume).prod (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))))

theorem parameterSphere_measurable : Measurable parameterSphere := by
  apply angularSphere_measurable.comp
  fun_prop

theorem angularSphere_factor (z : V) : angularSphere z = parameterSphere (z 1,z 2) := by
  apply Subtype.ext
  change normalChart z = normalChart (WithLp.toLp 2 ![0,z 1,z 2])
  simp [normalChart,normalTangent]

theorem angularSplit_map_restrict {I : Set ℝ} {B : Set (ℝ × ℝ)}
    (hI : MeasurableSet I) (hB : MeasurableSet B) :
    (volume.restrict (angularSplit ⁻¹' (I ×ˢ B))).map angularSphere =
      volume I • (volume.restrict B).map parameterSphere := by
  have hm : (volume.restrict (angularSplit ⁻¹' (I ×ˢ B))).map angularSplit =
      (volume.restrict I).prod (volume.restrict B) := by
    rw [(angularSplit_measurePreserving.restrict_preimage (hI.prod hB)).map_eq,
      Measure.prod_restrict]
    rfl
  have hf : angularSphere = (parameterSphere ∘ Prod.snd) ∘ angularSplit := by
    funext z
    exact angularSphere_factor z
  rw [hf,← Measure.map_map (parameterSphere_measurable.comp measurable_snd) angularSplit.measurable,hm,
    ← Measure.map_map parameterSphere_measurable measurable_snd,Measure.map_snd_prod,
    Measure.map_smul,Measure.restrict_apply_univ]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Two-dimensional angular parameter patches and sphere area -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem angular_box_subset_ball {d : ℝ} (hd : 0 < d) :
    angularSplit ⁻¹' (angularInterval d ×ˢ angularSquare d) ⊆ ball (0 : V) (4*d) := by
  intro z hz
  change (-d < z 0 ∧ z 0 < d) ∧ (-d < z 1 ∧ z 1 < d) ∧ (-d < z 2 ∧ z 2 < d) at hz
  have hs {x : ℝ} (hx : -d < x ∧ x < d) : x^2 < d^2 := by
    nlinarith [mul_pos (sub_pos.mpr hx.2) (show 0 < d+x by linarith [hx.1])]
  have hnorm : ‖z‖^2 = z 0^2+z 1^2+z 2^2 := by
    simp [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
  rw [mem_ball,dist_zero_right]
  nlinarith [hs hz.1,hs hz.2.1,hs hz.2.2,norm_nonneg z]

theorem angularSquare_weighted_measure_bound :
    ∃ (d : ℝ) (K : ℝ≥0), 0 < d ∧ 0 < K ∧
      volume (angularInterval d) • (volume.restrict (angularSquare d)).map parameterSphere ≤
        (K : ℝ≥0∞)^3 • sphereArea := by
  obtain ⟨r,K,hr,hK,hbound⟩ := angularSphere_measure_bound
  have hd : 0 < r/4 := div_pos hr (by norm_num)
  refine ⟨r/4,K,hd,hK,?_⟩
  rw [← angularSplit_map_restrict (I := angularInterval (r/4)) (B := angularSquare (r/4))
    measurableSet_Ioo (measurableSet_Ioo.prod measurableSet_Ioo)]
  apply le_trans (Measure.map_mono ?_ angularSphere_measurable) hbound
  apply Measure.restrict_mono
  · simpa only [mul_div_cancel₀ r (by norm_num : (4 : ℝ) ≠ 0)] using angular_box_subset_ball hd
  · exact le_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A finite positive domination constant for the angular probability law -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem angularInterval_volume (d : ℝ) :
    volume (angularInterval d) = ENNReal.ofReal (2*d) := by
  rw [angularInterval,Real.volume_Ioo]
  congr 1
  ring

theorem sphereProbability_rescale :
    ENNReal.ofReal (4*Real.pi) • sphereProbability = sphereArea := by
  rw [sphereProbability,smul_smul,ENNReal.mul_inv_cancel (by positivity) ENNReal.ofReal_ne_top,
    one_smul]

theorem parameterSphere_dominated :
    ∃ (d : ℝ) (C : ℝ≥0∞), 0 < d ∧ C ≠ 0 ∧ C ≠ ⊤ ∧
      (volume.restrict (angularSquare d)).map parameterSphere ≤ C • sphereProbability := by
  obtain ⟨d,K,hd,hK,hbound⟩ := angularSquare_weighted_measure_bound
  let I := volume (angularInterval d)
  let P := ENNReal.ofReal (4*Real.pi)
  let C := I⁻¹ * (K : ℝ≥0∞)^3 * P
  have hI0 : I ≠ 0 := by dsimp [I]; rw [angularInterval_volume d]; positivity
  have hIt : I ≠ ⊤ := by dsimp [I]; rw [angularInterval_volume d]; exact ENNReal.ofReal_ne_top
  have hP0 : P ≠ 0 := by dsimp [P] <;> positivity
  have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKn : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
  have hC0 : C ≠ 0 := mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr hIt)
    (pow_ne_zero 3 hKn)) hP0
  have hCt : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hI0)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)) hPt
  refine ⟨d,C,hd,hC0,hCt,Measure.le_iff.mpr ?_⟩
  intro A hA
  have hb := hbound A
  simp only [Measure.smul_apply,smul_eq_mul] at hb ⊢
  have hrescale := congrArg (fun μ : Measure Sphere => μ A) sphereProbability_rescale
  simp only [Measure.smul_apply,smul_eq_mul] at hrescale
  calc
    ((volume.restrict (angularSquare d)).map parameterSphere) A =
        I⁻¹ * (I * ((volume.restrict (angularSquare d)).map parameterSphere) A) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hI0 hIt,one_mul]
    _ ≤ I⁻¹ * ((K : ℝ≥0∞)^3 * sphereArea A) := by gcongr
    _ = C * sphereProbability A := by
      rw [← hrescale]
      simp only [C,P,mul_assoc]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Rotating the outgoing chart to the incoming transverse direction -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem angularRotation_normal : angularRotation minorizationNormal = firstAxis := by
  change angularRotationLinear minorizationNormal = firstAxis
  ext i
  fin_cases i <;> simp [angularRotationLinear,minorizationNormal,firstAxis,secondAxis,
    beamAxis,EuclideanSpace.single]
  all_goals
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    nlinarith

theorem angularRotation_second : angularRotation secondAxis = secondAxis := by
  change angularRotationLinear secondAxis = secondAxis
  simp [angularRotationLinear,firstAxis,secondAxis,beamAxis,EuclideanSpace.single]

theorem angularRotation_tangent :
    angularRotation ((Real.sqrt 2)⁻¹ • (firstAxis-beamAxis)) = beamAxis := by
  change angularRotationLinear ((Real.sqrt 2)⁻¹ • (firstAxis-beamAxis)) = beamAxis
  ext i
  fin_cases i <;> simp [angularRotationLinear,firstAxis,secondAxis,beamAxis,EuclideanSpace.single]
  all_goals
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The incoming angular patch uses the same probability measure bound -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem angularRotation_normalize (v : V) :
    angularRotation (NormedSpace.normalize v) = NormedSpace.normalize (angularRotation v) := by
  simp [NormedSpace.normalize]

theorem incomingParameterSphere_measurable : Measurable incomingParameterSphere :=
  (sphereRotation angularRotation).measurable.comp parameterSphere_measurable

theorem incomingPatch_tangent (z : V) :
    angularRotation (normalTangent z) = z 1 • secondAxis+z 2 • beamAxis := by
  have hv : normalTangent z = z 1 • secondAxis+
      z 2 • ((Real.sqrt 2)⁻¹ • (firstAxis-beamAxis)) := by
    simp [normalTangent,smul_smul,div_eq_mul_inv,mul_comm]
  rw [hv,map_add,map_smul,map_smul,angularRotation_second,angularRotation_tangent]

theorem incomingParameterSphere_value (p : ℝ × ℝ) :
    (incomingParameterSphere p : V) =
      NormedSpace.normalize (firstAxis+p.1 • secondAxis+p.2 • beamAxis) := by
  change angularRotation (normalChart (WithLp.toLp 2 ![0,p.1,p.2])) = _
  rw [normalChart,angularRotation_normalize,map_add,angularRotation_normal,incomingPatch_tangent]
  simp only [Matrix.cons_val_one,Matrix.cons_val_zero,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  congr 1
  abel

theorem paired_parameterSphere_dominated :
    ∃ (d : ℝ) (C : ℝ≥0∞), 0 < d ∧ C ≠ 0 ∧ C ≠ ⊤ ∧
      (volume.restrict (angularSquare d)).map parameterSphere ≤ C • sphereProbability ∧
      (volume.restrict (angularSquare d)).map incomingParameterSphere ≤ C • sphereProbability := by
  obtain ⟨d,C,hd,hC0,hCt,hbound⟩ := parameterSphere_dominated
  refine ⟨d,C,hd,hC0,hCt,hbound,?_⟩
  have h := Measure.map_mono hbound (sphereRotation angularRotation).measurable
  rw [Measure.map_map (sphereRotation angularRotation).measurable parameterSphere_measurable,
    Measure.map_smul,(sphereRotation_probability angularRotation).map_eq] at h
  exact h

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The collision chart with preceding velocity and unused angle as parameters -/

noncomputable section

open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem collisionFamily_at_base : collisionFamily collisionParameterBase 0 = 0 := by
  rw [collisionFamily_slice,minorizationChart_zero]

theorem collisionFamilyExtension_at_base :
    collisionFamilyExtension collisionFamilyBase = collisionFamilyBase := by
  simp only [collisionFamilyExtension,collisionFamilyBase,collisionFamily_at_base]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The collision family has an invertible derivative including its parameters -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem collisionFamilyLocalEquiv_source : collisionFamilyBase ∈ collisionFamilyLocalEquiv.source :=
  collisionFamilyExtension_hasStrictFDerivAt.mem_toOpenPartialHomeomorph_source

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform local coverage for nearby preceding velocities -/

noncomputable section

open MeasureTheory Set Metric Filter
open scoped Topology NNReal ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem collisionFamily_uniform {ε : ℝ} (hε : 0 < ε) :
    ∃ (a δ : ℝ) (K : ℝ≥0), 0 < a ∧ a ≤ ε ∧ 0 < δ ∧ δ ≤ a ∧ 0 < K ∧
      ∀ p ∈ ball collisionParameterBase δ,
        LipschitzOnWith K (collisionFamily p) (ball (0 : V) a) ∧
        ball (0 : V) δ ⊆ collisionFamily p '' ball (0 : V) a := by
  obtain ⟨S,hS,happrox⟩ := collisionFamilyExtension_hasStrictFDerivAt.approximates_deriv_on_nhds
    (c := 1) (Or.inr zero_lt_one)
  have hsource : collisionFamilyLocalEquiv.source ∈ 𝓝 collisionFamilyBase :=
    collisionFamilyLocalEquiv.open_source.mem_nhds collisionFamilyLocalEquiv_source
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp (inter_mem hS hsource)
  let a := min r ε
  have ha : 0 < a := lt_min hr hε
  have hU : ball collisionFamilyBase a ⊆ S ∩ collisionFamilyLocalEquiv.source :=
    (ball_subset_ball (min_le_left _ _)).trans hrS
  have hopen : IsOpen (collisionFamilyExtension '' ball collisionFamilyBase a) :=
    collisionFamilyLocalEquiv.isOpen_image_of_subset_source isOpen_ball
      (hU.trans inter_subset_right)
  have hbase : collisionFamilyBase ∈ collisionFamilyExtension '' ball collisionFamilyBase a :=
    ⟨collisionFamilyBase,mem_ball_self ha,collisionFamilyExtension_at_base⟩
  obtain ⟨b,hb,hbI⟩ := Metric.isOpen_iff.mp hopen collisionFamilyBase hbase
  let δ := min b a
  let K := ‖(collisionFamilyLinearEquiv : CollisionFamilySpace →L[ℝ] CollisionFamilySpace)‖₊+1
  have hK : 0 < K := by dsimp [K] <;> positivity
  have hL : LipschitzOnWith K collisionFamilyExtension (ball collisionFamilyBase a) := by
    intro x hx y hy
    exact (happrox.mono_set (hU.trans inter_subset_left)).lipschitz ⟨x,hx⟩ ⟨y,hy⟩
  refine ⟨a,δ,K,ha,min_le_right _ _,lt_min hb ha,min_le_right _ _,hK,?_⟩
  intro p hp
  have hpa : p ∈ ball collisionParameterBase a := ball_subset_ball (min_le_right b a) hp
  have hpair {z : V} (hz : z ∈ ball (0 : V) a) : (p,z) ∈ ball collisionFamilyBase a := by
    change (p,z) ∈ ball (collisionParameterBase,0) a
    rw [← ball_prod_same]
    exact ⟨hpa,hz⟩
  constructor
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [collisionFamilyExtension,dist_prod_same_left] using
      hL.dist_le_mul (p,x) (hpair hx) (p,y) (hpair hy)
  · intro y hy
    have hpy : (p,y) ∈ ball collisionFamilyBase δ := by
      change (p,y) ∈ ball (collisionParameterBase,0) δ
      rw [← ball_prod_same]
      exact ⟨hp,hy⟩
    obtain ⟨⟨q,z⟩,hz,he⟩ := hbI (ball_subset_ball (min_le_left b a) hpy)
    have hq : q = p := congrArg Prod.fst he
    subst q
    refine ⟨z,?_,congrArg Prod.snd he⟩
    change (p,z) ∈ ball (collisionParameterBase,0) a at hz
    rw [← ball_prod_same] at hz
    exact hz.2

theorem collisionFamily_uniform_volume {ε : ℝ} (hε : 0 < ε) :
    ∃ (a δ : ℝ) (K : ℝ≥0), 0 < a ∧ a ≤ ε ∧ 0 < δ ∧ δ ≤ a ∧ 0 < K ∧
      ∀ p ∈ ball collisionParameterBase δ, ∀ A : Set V, A ⊆ ball (0 : V) δ →
        volume A ≤ (K : ℝ≥0∞)^3 * volume (ball (0 : V) a ∩ collisionFamily p ⁻¹' A) := by
  obtain ⟨a,δ,K,ha,haε,hδ,hδa,hK,hfamily⟩ := collisionFamily_uniform hε
  refine ⟨a,δ,K,ha,haε,hδ,hδa,hK,?_⟩
  intro p hp A hA
  have hcover : A ⊆ collisionFamily p '' (ball (0 : V) a ∩ collisionFamily p ⁻¹' A) := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := (hfamily p hp).2 (hA hy)
    exact ⟨z,⟨hz,hy⟩,rfl⟩
  exact (measure_mono hcover).trans
    (lipschitz_volume_image_le ((hfamily p hp).1.mono inter_subset_left))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Volume-preserving coordinates for the four collision angles -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem familyCoordinates_measurePreserving : MeasurePreserving familyCoordinates :=
  ((MeasurePreserving.id volume).prod angularSplit_measurePreserving).trans
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc volume_preserving_prodAssoc)

theorem twoCollisionMap_measurable (v : V) : Measurable (twoCollisionMap v) := by
  unfold twoCollisionMap child
  fun_prop

theorem familyChart_coordinates (v : V) (t : ℝ) (z : V) :
    familyChart v (familyCoordinates (t,z)) = collisionFamily (v,t) z := by
  change child (child v (-beamAxis) (incomingParameterSphere (t,z 0) : V)) beamAxis
    (parameterSphere (z 1,z 2) : V) = _
  rw [incomingParameterSphere_value]
  have hn : (parameterSphere (z 1,z 2) : V) = normalChart z :=
    (congrArg Subtype.val (angularSphere_factor z)).symm
  rw [hn]
  rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Averaging the uniform collision-chart volume estimate over the unused angle -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem familyWindowMap_measurable (v : V) : Measurable (familyWindowMap v) := by
  unfold familyWindowMap collisionFamily incidentDirection normalChart NormedSpace.normalize child
  fun_prop

theorem familyWindowMeasure_preimage (v : V) (a δ : ℝ) {A : Set V} (hA : MeasurableSet A) :
    familyWindowMeasure a δ (familyWindowMap v ⁻¹' A) =
      ∫⁻ t in Ioo (-δ) δ, volume (ball (0 : V) a ∩ collisionFamily (v,t) ⁻¹' A) := by
  rw [familyWindowMeasure,Measure.prod_apply ((familyWindowMap_measurable v) hA)]
  apply lintegral_congr
  intro t
  have hs : MeasurableSet (Prod.mk t ⁻¹' (familyWindowMap v ⁻¹' A)) :=
    measurable_prodMk_left ((familyWindowMap_measurable v) hA)
  rw [Measure.restrict_apply hs]
  change volume (collisionFamily (v,t) ⁻¹' A ∩ ball (0 : V) a) = _
  rw [inter_comm]

theorem uniform_family_window_volume {ε : ℝ} (hε : 0 < ε) :
    ∃ (a δ : ℝ) (K : ℝ≥0), 0 < a ∧ a ≤ ε ∧ 0 < δ ∧ δ ≤ a ∧ 0 < K ∧
      ∀ v ∈ ball beamAxis δ, ∀ A : Set V, MeasurableSet A → A ⊆ ball (0 : V) δ →
        ENNReal.ofReal (2*δ) * volume A ≤ (K : ℝ≥0∞)^3 *
          ((familyWindowMeasure a δ).map (familyWindowMap v)) A := by
  obtain ⟨a,δ,K,ha,haε,hδ,hδa,hK,hbound⟩ := collisionFamily_uniform_volume hε
  refine ⟨a,δ,K,ha,haε,hδ,hδa,hK,?_⟩
  intro v hv A hA hAsub
  have hp (t : ℝ) (ht : t ∈ Ioo (-δ) δ) : (v,t) ∈ ball collisionParameterBase δ := by
    change (v,t) ∈ ball (beamAxis,(0 : ℝ)) δ
    rw [← ball_prod_same]
    refine ⟨hv,?_⟩
    simpa only [mem_ball,Real.dist_eq,sub_zero,abs_lt,mem_Ioo] using ht
  rw [Measure.map_apply (familyWindowMap_measurable v) hA,
    familyWindowMeasure_preimage v a δ hA]
  calc
    ENNReal.ofReal (2*δ) * volume A = ∫⁻ _t in Ioo (-δ) δ, volume A := by
      rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo]
      rw [show δ- -δ = 2*δ by ring,mul_comm]
    _ ≤ ∫⁻ t in Ioo (-δ) δ,
        (K : ℝ≥0∞)^3 * volume (ball (0 : V) a ∩ collisionFamily (v,t) ⁻¹' A) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact hbound (v,t) (hp t ht) A hAsub
    _ = _ := lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A collision window on which both chosen beam probabilities stay positive -/

noncomputable section

open MeasureTheory Set Metric

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem firstCollisionFamily_at_base : firstCollisionFamily collisionFamilyBase = firstAxis := by
  rw [firstCollisionFamily]
  change child beamAxis (-beamAxis) (incidentDirection 0 0) = firstAxis
  rw [child_opposite_beam]
  simp [incidentDirection,NormedSpace.normalize_eq_self_of_norm_eq_one axis_norms.1]

theorem firstCollisionFamily_continuousAt :
    ContinuousAt firstCollisionFamily collisionFamilyBase := by
  have hn := incidentDirection_contDiffAt.continuousAt
  have hv : ContinuousAt (fun w : CollisionFamilySpace => w.1.1) collisionFamilyBase := by
    fun_prop
  change ContinuousAt (fun w : CollisionFamilySpace =>
    (1/2 : ℝ) • (w.1.1 + -beamAxis) + (‖w.1.1 - -beamAxis‖/2) •
      incidentDirection w.1.2 w.2) collisionFamilyBase
  exact ((hv.add continuousAt_const).const_smul (1/2 : ℝ)).add
    (((hv.sub continuousAt_const).norm.div_const 2).smul hn)

theorem localCollisionCore_measurable : MeasurableSet localCollisionCore := measurableSet_ball

theorem norm_le_two_of_near_unit {v e : V} (he : ‖e‖ = 1) (hv : v ∈ ball e (1/4)) :
    ‖v‖ ≤ 2 := by
  have ht := dist_triangle v e (0 : V)
  rw [dist_zero_right,dist_zero_right,he] at ht
  have hd : dist v e < 1/4 := hv
  linarith

theorem localCollisionCore_norm {v : V} (hv : v ∈ localCollisionCore) : ‖v‖ ≤ 2 :=
  norm_le_two_of_near_unit axis_norms.1 hv

theorem localCollisionCore_distance {v : V} (hv : v ∈ localCollisionCore) :
    1 ≤ ‖v-beamAxis‖ := by
  have ht := dist_triangle firstAxis v beamAxis
  rw [dist_eq_norm,first_beam_norms.2,dist_comm firstAxis v,dist_eq_norm v beamAxis] at ht
  have hd : dist v firstAxis < 1/4 := hv
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem beam_neighborhood_distance {v : V} (hv : v ∈ ball beamAxis (1/4)) :
    1 ≤ ‖v+beamAxis‖ := by
  have ht := dist_triangle beamAxis v (-beamAxis)
  have hb : dist beamAxis (-beamAxis) = 2 := by
    rw [dist_eq_norm,show beamAxis-(-beamAxis) = (2 : ℝ) • beamAxis by module,
      norm_smul,Real.norm_ofNat,axis_norms.2.2,mul_one]
  rw [hb,dist_comm beamAxis v,dist_eq_norm v (-beamAxis),sub_neg_eq_add] at ht
  have hd : dist v beamAxis < 1/4 := hv
  linarith

theorem collision_window_good : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧
    ∀ w ∈ ball collisionFamilyBase ε, firstCollisionFamily w ∈ localCollisionCore := by
  obtain ⟨r,hr,h⟩ := Metric.continuousAt_iff.mp firstCollisionFamily_continuousAt
    (1/4) (by norm_num)
  refine ⟨min r (1/4),lt_min hr (by norm_num),min_le_right _ _,?_⟩
  intro w hw
  have hd : dist w collisionFamilyBase < r := lt_of_lt_of_le hw (min_le_left _ _)
  have hh := h hd
  change dist (firstCollisionFamily w) firstAxis < 1/4
  simpa only [firstCollisionFamily_at_base] using hh

theorem familyWindow_good {ε a δ : ℝ} (ha : a ≤ ε) (hδ : δ ≤ a)
    (hgood : ∀ w ∈ ball collisionFamilyBase ε, firstCollisionFamily w ∈ localCollisionCore)
    {v : V} (hv : v ∈ ball beamAxis δ) {t : ℝ} (ht : t ∈ Ioo (-δ) δ)
    {z : V} (hz : z ∈ ball (0 : V) a) :
    firstCollisionFamily ((v,t),z) ∈ localCollisionCore := by
  apply hgood
  change ((v,t),z) ∈ ball ((beamAxis,(0 : ℝ)),(0 : V)) ε
  rw [← ball_prod_same,← ball_prod_same]
  refine ⟨⟨(ball_subset_ball (hδ.trans ha)) hv,?_⟩,(ball_subset_ball ha) hz⟩
  have hh : dist t (0 : ℝ) < δ := by
    simpa only [Real.dist_eq,sub_zero,abs_lt,mem_Ioo] using ht
  exact hh.trans_le (hδ.trans ha)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceMinorization
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The physical two-collision law bounds the small four-angle window -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem familyWindow_subset {a δ d : ℝ} (hδ : δ ≤ a) (ha : a ≤ d) :
    Ioo (-δ) δ ×ˢ ball (0 : V) a ⊆ familyCoordinates ⁻¹' (angularSquare d ×ˢ angularSquare d) := by
  rintro ⟨t,z⟩ ⟨ht,hz⟩
  have hn : ‖z‖ < a := by simpa only [mem_ball,dist_zero_right] using hz
  have hi (i : Fin 3) : -d < z i ∧ z i < d :=
    abs_lt.mp ((PiLp.norm_apply_le z i).trans_lt (hn.trans_le ha))
  change ((-d < t ∧ t < d) ∧ (-d < z 0 ∧ z 0 < d)) ∧
    (-d < z 1 ∧ z 1 < d) ∧ (-d < z 2 ∧ z 2 < d)
  exact ⟨⟨⟨by linarith [ht.1],by linarith [ht.2]⟩,hi 0⟩,hi 1,hi 2⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The angular window is dominated while retaining its intermediate-velocity support -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem familyWindowAngles_measurable : Measurable familyWindowAngles := by
  exact (incomingParameterSphere_measurable.comp (by fun_prop)).prodMk
    (parameterSphere_measurable.comp (by fun_prop))

theorem firstAngleSet_measurable (v : V) : MeasurableSet (firstAngleSet v) := by
  apply localCollisionCore_measurable.preimage
  unfold child
  fun_prop

theorem familyWindowAngles_le {a δ d : ℝ} {C : ℝ≥0∞} (hδ : δ ≤ a) (ha : a ≤ d)
    (hCt : C ≠ ⊤)
    (hout : (volume.restrict (angularSquare d)).map parameterSphere ≤ C • sphereProbability)
    (hin : (volume.restrict (angularSquare d)).map incomingParameterSphere ≤ C • sphereProbability) :
    (familyWindowMeasure a δ).map familyWindowAngles ≤ C^2 • sphereProbability.prod sphereProbability := by
  let B := angularSquare d ×ˢ angularSquare d
  have hB : MeasurableSet B :=
    (measurableSet_Ioo.prod measurableSet_Ioo).prod (measurableSet_Ioo.prod measurableSet_Ioo)
  have hmap : (volume.restrict (familyCoordinates ⁻¹' B)).map familyCoordinates =
      (volume.restrict (angularSquare d)).prod (volume.restrict (angularSquare d)) := by
    rw [(familyCoordinates_measurePreserving.restrict_preimage hB).map_eq,Measure.prod_restrict]
    rfl
  have hle : familyWindowMeasure a δ ≤ volume.restrict (familyCoordinates ⁻¹' B) := by
    rw [familyWindowMeasure,Measure.prod_restrict]
    exact Measure.restrict_mono (familyWindow_subset hδ ha) le_rfl
  have hf : familyWindowAngles =
      (fun p => (incomingParameterSphere p.1,parameterSphere p.2)) ∘ familyCoordinates := rfl
  have hm : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) =>
      (incomingParameterSphere p.1,parameterSphere p.2)) :=
    incomingParameterSphere_measurable.prodMap parameterSphere_measurable
  apply (Measure.map_mono hle familyWindowAngles_measurable).trans
  rw [hf,← Measure.map_map hm familyCoordinates.measurable,hmap]
  change ((volume.restrict (angularSquare d)).prod (volume.restrict (angularSquare d))).map
    (Prod.map incomingParameterSphere parameterSphere) ≤ _
  rw [← Measure.map_prod_map _ _ incomingParameterSphere_measurable parameterSphere_measurable]
  have : IsFiniteMeasure (C • sphereProbability) := ⟨by
    rw [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    exact hCt.lt_top⟩
  have hh := Measure.prod_mono hin hout
  rwa [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul,← pow_two] at hh

theorem familyWindowAngles_mem {ε a δ : ℝ} (ha : a ≤ ε) (hδ : δ ≤ a)
    (hgood : ∀ w ∈ ball collisionFamilyBase ε, firstCollisionFamily w ∈ localCollisionCore)
    {v : V} (hv : v ∈ ball beamAxis δ) :
    ∀ᵐ p ∂(familyWindowMeasure a δ).map familyWindowAngles, p ∈ firstAngleSet v := by
  apply (ae_map_iff familyWindowAngles_measurable.aemeasurable (firstAngleSet_measurable v)).mpr
  have hmem : ∀ᵐ w ∂familyWindowMeasure a δ, w ∈ Ioo (-δ) δ ×ˢ ball (0 : V) a := by
    rw [familyWindowMeasure,Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_ball)
  filter_upwards [hmem] with w hw
  have hh := familyWindow_good ha hδ hgood hv hw.1 hw.2
  change child v (-beamAxis) (incomingParameterSphere (w.1,w.2 0) : V) ∈ localCollisionCore
  rw [incomingParameterSphere_value]
  exact hh

theorem familyWindowMap_local_le {ε a δ d : ℝ} {C : ℝ≥0∞}
    (haε : a ≤ ε) (hδ : δ ≤ a) (ha : a ≤ d) (hCt : C ≠ ⊤)
    (hgood : ∀ w ∈ ball collisionFamilyBase ε, firstCollisionFamily w ∈ localCollisionCore)
    (hout : (volume.restrict (angularSquare d)).map parameterSphere ≤ C • sphereProbability)
    (hin : (volume.restrict (angularSquare d)).map incomingParameterSphere ≤ C • sphereProbability)
    {v : V} (hv : v ∈ ball beamAxis δ) :
    (familyWindowMeasure a δ).map (familyWindowMap v) ≤ C^2 • localTwoCollisionLaw v := by
  have hmem := familyWindowAngles_mem haε hδ hgood hv
  have hre : ((familyWindowMeasure a δ).map familyWindowAngles).restrict (firstAngleSet v) =
      (familyWindowMeasure a δ).map familyWindowAngles := Measure.restrict_eq_self_of_ae_mem hmem
  have hle : (familyWindowMeasure a δ).map familyWindowAngles ≤
      C^2 • (sphereProbability.prod sphereProbability).restrict (firstAngleSet v) := by
    conv_lhs => rw [← hre]
    exact (Measure.restrict_mono (Subset.rfl) (familyWindowAngles_le hδ ha hCt hout hin)).trans_eq
      (Measure.restrict_smul _ _ _)
  have hh := Measure.map_mono hle (twoCollisionMap_measurable v)
  rw [Measure.map_map (twoCollisionMap_measurable v) familyWindowAngles_measurable,
    Measure.map_smul] at hh
  · have heq : twoCollisionMap v ∘ familyWindowAngles = familyWindowMap v := by
      funext w
      exact familyChart_coordinates v w.1 w.2
    simpa only [heq,localTwoCollisionLaw] using hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform entry into an arbitrarily small neighborhood of the positive beam -/

noncomputable section

open MeasureTheory Set NormedSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem beamEntryMass_pos {δ : ℝ} (hδ : 0 < δ) : 0 < beamEntryMass δ :=
  mul_pos (div_pos hδ (by norm_num)) (sphereCapMass_pos (by positivity))

theorem reference_beam_entry {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/4)
    (v : V) (hv : ‖v‖ ≤ 5) :
    beamEntryMass δ ≤ (referenceJump beamAxis v).real (Metric.ball beamAxis δ) := by
  have he := axis_norms.2.2
  have hden : ‖v-beamAxis‖+‖v+beamAxis‖ ≤ 12 := by
    have hm := norm_sub_le v beamAxis
    have hp := norm_add_le v beamAxis
    rw [he] at hm hp
    linarith
  have hpos : 0 < ‖v-beamAxis‖+‖v+beamAxis‖ :=
    lt_of_lt_of_le (by norm_num) (two_beam_distance_lower v beamAxis he)
  have hcap : 0 ≤ sphereCapMass (δ/12) := (sphereCapMass_pos (by positivity)).le
  rw [referenceJump_real]
  by_cases hd : δ/2 ≤ ‖v-beamAxis‖
  · have hne : v-beamAxis ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith))
    let n : Sphere := ⟨-normalize (v-beamAxis),mem_sphere_zero_iff_norm.mpr
      (by rw [norm_neg,norm_normalize hne])⟩
    have hn : child v beamAxis n.1 = beamAxis := (child_normalized_endpoints v beamAxis).2
    have hout := outgoing_endpoint_cap hδ v beamAxis beamAxis he hv n (by rw [hn,dist_self]; positivity)
    have hp : δ/24 ≤ plusProbability beamAxis v := by
      rw [plusProbability,le_div_iff₀ hpos]
      nlinarith
    have hh := mul_le_mul hp hout hcap (plusProbability_mem beamAxis v).1
    exact hh.trans (le_add_of_nonneg_right (mul_nonneg
      (sub_nonneg.mpr (plusProbability_mem beamAxis v).2) measureReal_nonneg))
  · have hnear : v ∈ Metric.ball beamAxis (1/4) := by
      change dist v beamAxis < 1/4
      rw [dist_eq_norm]
      have hd' := lt_of_not_ge hd
      linarith
    have hdist := beam_neighborhood_distance hnear
    have hne : v-(-beamAxis) ≠ 0 := by
      rw [sub_neg_eq_add]
      exact norm_ne_zero_iff.mp (ne_of_gt (by linarith))
    let n : Sphere := ⟨normalize (v-(-beamAxis)),mem_sphere_zero_iff_norm.mpr (norm_normalize hne)⟩
    have hn : child v (-beamAxis) n.1 = v := (child_normalized_endpoints v (-beamAxis)).1
    have hout := outgoing_endpoint_cap hδ v (-beamAxis) beamAxis (by simpa using he) hv n (by
      rw [hn,dist_eq_norm]
      exact le_of_lt (lt_of_not_ge hd))
    have hp : δ/24 ≤ 1-plusProbability beamAxis v := by
      rw [minusProbability_eq beamAxis v he,le_div_iff₀ hpos]
      nlinarith
    have hh := mul_le_mul hp hout hcap (sub_nonneg.mpr (plusProbability_mem beamAxis v).2)
    exact hh.trans (le_add_of_nonneg_left (mul_nonneg (plusProbability_mem beamAxis v).1
      measureReal_nonneg))

theorem retained_beam_entry {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/4)
    (v : V) (hv : ‖v‖ ≤ 5) :
    beamEntryMass δ ≤ (retainedJump beamAxis v).real (Metric.ball beamAxis δ) := by
  have he := axis_norms.2.2
  have hp0 : 0 < (retention beamAxis v).toReal :=
    ENNReal.toReal_pos (retention_ne_zero_coarse beamAxis v he hv) (retention_ne_top beamAxis v)
  have hp1 := (retention_toReal_mem beamAxis v).2
  have hsub : Metric.ball beamAxis δ ⊆ referenceRegion := by
    intro w hw
    have ht := dist_triangle w beamAxis (0 : V)
    rw [dist_zero_right,dist_zero_right,he] at ht
    change dist w 0 ≤ 5
    rw [dist_zero_right]
    have hd : dist w beamAxis < δ := hw
    linarith
  rw [Measure.real,retainedJump_apply,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_inv,Measure.restrict_apply measurableSet_ball,inter_eq_left.mpr hsub]
  change beamEntryMass δ ≤ (retention beamAxis v).toReal⁻¹*
    (referenceJump beamAxis v).real (Metric.ball beamAxis δ)
  rw [inv_mul_eq_div]
  apply (reference_beam_entry hδ hδsmall v hv).trans
  apply (le_div_iff₀ hp0).mpr
  exact mul_le_of_le_one_right measureReal_nonneg hp1

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Two retained jumps enter a transverse velocity ball uniformly -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem retained_transverse_entry_local {ζ δ : ℝ} (hζ : 0 < ζ) (hδζ : δ ≤ ζ/2)
    (hδ : δ ≤ 1/4) {v : V} (hv : v ∈ ball beamAxis δ) :
    sphereCapMass (ζ/12)/6 ≤ (retainedJump beamAxis v).real (ball firstAxis ζ) := by
  have hv' : v ∈ ball beamAxis (1/4) := ball_subset_ball hδ hv
  have hv2 := norm_le_two_of_near_unit axis_norms.2.2 hv'
  have hp := minusProbability_lower_small beamAxis v axis_norms.2.2 hv2 (beam_neighborhood_distance hv')
  let n : Sphere := ⟨firstAxis,mem_sphere_zero_iff_norm.mpr axis_norms.1⟩
  have hn : dist (child v (-beamAxis) n.1) firstAxis ≤ ζ/2 := by
    have hh := child_lipschitz v (-beamAxis) beamAxis (-beamAxis) firstAxis axis_norms.1
    rw [child_opposite_beam,sub_self,norm_zero,add_zero] at hh
    exact (show dist (child v (-beamAxis) n.1) firstAxis ≤ dist v beamAxis from hh).trans
      (le_trans (le_of_lt hv) hδζ)
  have ho := outgoing_endpoint_cap hζ v (-beamAxis) firstAxis
    (by simpa using axis_norms.2.2) (by linarith : ‖v‖ ≤ 5) n hn
  rw [retainedJump_small beamAxis v axis_norms.2.2 (by linarith),referenceJump_real]
  have hc := (sphereCapMass_pos (by positivity : 0 < ζ/12)).le
  have hh := mul_le_mul hp ho hc (sub_nonneg.mpr (plusProbability_mem beamAxis v).2)
  have hn' := mul_nonneg (plusProbability_mem beamAxis v).1
    (measureReal_nonneg (μ := outgoing (v,beamAxis)) (s := ball firstAxis ζ))
  linarith

theorem retained_two_transverse_entry {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ v : V, ‖v‖ ≤ 5 →
      c ≤ (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v (ball firstAxis ζ) := by
  let δ := min (ζ/2) (1/4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  let I := ENNReal.ofReal (beamEntryMass δ)
  let J := ENNReal.ofReal (sphereCapMass (ζ/12)/6)
  have hI : I ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (beamEntryMass_pos hδ))
  have hJ : J ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by
    exact div_pos (sphereCapMass_pos (by positivity)) (by norm_num)))
  refine ⟨I*J,mul_ne_zero hI hJ,ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,?_⟩
  intro v hv
  have hentry : I ≤ retainedJump beamAxis v (ball beamAxis δ) :=
    (ENNReal.ofReal_le_ofReal (retained_beam_entry hδ (min_le_right _ _) v hv)).trans
      ENNReal.ofReal_toReal_le
  have hlocal (u : V) (hu : u ∈ ball beamAxis δ) :
      J ≤ retainedJump beamAxis u (ball firstAxis ζ) :=
    (ENNReal.ofReal_le_ofReal (retained_transverse_entry_local hζ (min_le_left _ _)
      (min_le_right _ _) hu)).trans ENNReal.ofReal_toReal_le
  calc
    I*J ≤ retainedJump beamAxis v (ball beamAxis δ)*J := mul_le_mul' hentry le_rfl
    _ = ∫⁻ _u in ball beamAxis δ, J ∂retainedJump beamAxis v := by
      rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]
    _ ≤ ∫⁻ u in ball beamAxis δ, retainedJump beamAxis u (ball firstAxis ζ)
        ∂retainedJump beamAxis v := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
      exact hlocal u hu
    _ ≤ ∫⁻ u, retainedJump beamAxis u (ball firstAxis ζ) ∂retainedJump beamAxis v :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := (Kernel.comp_apply' _ _ _ measurableSet_ball).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Each selected small-velocity collision is dominated by the retained jump -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem outgoing_plus_le_retained (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 2)
    (hr : 1 ≤ ‖v-e‖) : outgoing (v,e) ≤ (6 : ℝ≥0∞) • retainedJump e v := by
  have hw : (1 : ℝ≥0∞) ≤ 6*ENNReal.ofReal (plusProbability e v) := by
    have hh := ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 6*plusProbability e v by
      linarith [plusProbability_lower_small e v he hv hr])
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6),
      ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using hh
  rw [retainedJump_small e v he (hv.trans (by norm_num)),referenceJump_measure]
  apply Measure.le_iff.mpr
  intro A _hA
  simp only [Measure.smul_apply,Measure.add_apply,smul_eq_mul]
  calc
    outgoing (v,e) A = 1*outgoing (v,e) A := (one_mul _).symm
    _ ≤ (6*ENNReal.ofReal (plusProbability e v))*outgoing (v,e) A := mul_le_mul' hw le_rfl
    _ ≤ _ := by rw [mul_assoc,mul_add]; exact le_add_right le_rfl

theorem outgoing_minus_le_retained (e v : V) (he : ‖e‖ = 1) (hv : ‖v‖ ≤ 2)
    (hr : 1 ≤ ‖v+e‖) : outgoing (v,-e) ≤ (6 : ℝ≥0∞) • retainedJump e v := by
  have hw : (1 : ℝ≥0∞) ≤ 6*ENNReal.ofReal (1-plusProbability e v) := by
    have hh := ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ 6*(1-plusProbability e v) by
      linarith [minusProbability_lower_small e v he hv hr])
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6),
      ENNReal.ofReal_ofNat,ENNReal.ofReal_one] using hh
  rw [retainedJump_small e v he (hv.trans (by norm_num)),referenceJump_measure]
  apply Measure.le_iff.mpr
  intro A _hA
  simp only [Measure.smul_apply,Measure.add_apply,smul_eq_mul]
  calc
    outgoing (v,-e) A = 1*outgoing (v,-e) A := (one_mul _).symm
    _ ≤ (6*ENNReal.ofReal (1-plusProbability e v))*outgoing (v,-e) A := mul_le_mul' hw le_rfl
    _ ≤ _ := by rw [mul_assoc,mul_add]; exact le_add_left le_rfl

theorem localCollisionCore_jump_bound {u : V} (hu : u ∈ localCollisionCore) :
    outgoing (u,beamAxis) ≤ (6 : ℝ≥0∞) • retainedJump beamAxis u :=
  outgoing_plus_le_retained _ _ axis_norms.2.2 (localCollisionCore_norm hu)
    (localCollisionCore_distance hu)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Two selected collisions are dominated by two retained reference jumps -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem localTwoCollisionLaw_apply (v : V) {A : Set V} (hA : MeasurableSet A) :
    localTwoCollisionLaw v A =
      ∫⁻ u in localCollisionCore, outgoing (u,beamAxis) A ∂outgoing (v,-beamAxis) := by
  have hm : Measurable (fun n : Sphere => child v (-beamAxis) n.1) := by
    unfold child
    fun_prop
  have hq : Measurable (fun u : V => outgoing (u,beamAxis) A) :=
    (outgoing.measurable_coe hA).comp (measurable_id.prodMk measurable_const)
  rw [localTwoCollisionLaw,Measure.map_apply (twoCollisionMap_measurable v) hA,
    Measure.restrict_apply ((twoCollisionMap_measurable v) hA),
    Measure.prod_apply (((twoCollisionMap_measurable v) hA).inter (firstAngleSet_measurable v)),
    ← lintegral_indicator localCollisionCore_measurable,outgoing_apply,
    lintegral_map (hq.indicator localCollisionCore_measurable) hm]
  apply lintegral_congr
  intro n
  by_cases hn : child v (-beamAxis) n.1 ∈ localCollisionCore
  · rw [indicator_of_mem hn,outgoing_apply,
      Measure.map_apply (by unfold child; fun_prop) hA]
    congr 1
    ext m
    simp only [mem_preimage,mem_inter_iff,firstAngleSet,mem_ofPred_eq,twoCollisionMap,hn,and_true]
  · rw [indicator_of_notMem hn]
    have hz : Prod.mk n ⁻¹' (twoCollisionMap v ⁻¹' A ∩ firstAngleSet v) = ∅ := by
      ext m
      simp only [mem_preimage,mem_inter_iff,firstAngleSet,mem_ofPred_eq,hn,and_false,mem_empty_iff_false]
    rw [hz,measure_empty]

theorem localTwoCollisionLaw_le_retained {v : V} (hv : v ∈ Metric.ball beamAxis (1/4)) :
    localTwoCollisionLaw v ≤ (36 : ℝ≥0∞) •
      (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v := by
  have hm := outgoing_minus_le_retained beamAxis v axis_norms.2.2
    (norm_le_two_of_near_unit axis_norms.2.2 hv) (beam_neighborhood_distance hv)
  apply Measure.le_iff.mpr
  intro A hA
  rw [localTwoCollisionLaw_apply v hA,Measure.smul_apply,smul_eq_mul,
    Kernel.comp_apply' _ _ _ hA]
  calc
    (∫⁻ u in localCollisionCore, outgoing (u,beamAxis) A ∂outgoing (v,-beamAxis)) ≤
        ∫⁻ u in localCollisionCore, (6 : ℝ≥0∞)*retainedJump beamAxis u A ∂outgoing (v,-beamAxis) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem localCollisionCore_measurable] with u hu
      exact localCollisionCore_jump_bound hu A
    _ ≤ ∫⁻ u, (6 : ℝ≥0∞)*retainedJump beamAxis u A ∂outgoing (v,-beamAxis) :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ ≤ ∫⁻ u, (6 : ℝ≥0∞)*retainedJump beamAxis u A ∂((6 : ℝ≥0∞) • retainedJump beamAxis v) :=
      lintegral_mono' hm le_rfl
    _ = _ := by
      rw [lintegral_smul_measure,lintegral_const_mul' _ _ (by norm_num)]
      simp only [smul_eq_mul,← mul_assoc]
      norm_num

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform volume domination by two retained reference jumps near the beam -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem retained_two_volume_domination :
    ∃ (δ : ℝ) (B : ℝ≥0∞), 0 < δ ∧ δ ≤ 1/4 ∧ B ≠ 0 ∧ B ≠ ⊤ ∧
      ∀ v ∈ ball beamAxis δ,
        volume.restrict (ball (0 : V) δ) ≤ B •
          (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v := by
  obtain ⟨d,C,hd,hC0,hCt,hout,hin⟩ := paired_parameterSphere_dominated
  obtain ⟨ε,hε,hεsmall,hgood⟩ := collision_window_good
  obtain ⟨a,δ,K,_ha,hab,hδ,hδa,hK,hvolume⟩ :=
    uniform_family_window_volume (lt_min hd hε)
  have had := hab.trans (min_le_left _ _)
  have haε := hab.trans (min_le_right _ _)
  have hδsmall := hδa.trans (haε.trans hεsmall)
  let I := ENNReal.ofReal (2*δ)
  let B := I⁻¹ * (K : ℝ≥0∞)^3 * (C^2*36)
  have hI0 : I ≠ 0 := by dsimp [I] <;> positivity
  have hIt : I ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKn : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
  have hB0 : B ≠ 0 := mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr hIt)
    (pow_ne_zero 3 hKn)) (mul_ne_zero (pow_ne_zero 2 hC0) (by norm_num))
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hI0) (ENNReal.pow_ne_top ENNReal.coe_ne_top))
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top hCt) (by norm_num))
  refine ⟨δ,B,hδ,hδsmall,hB0,hBt,?_⟩
  intro v hv
  have hvsmall : v ∈ ball beamAxis (1/4) := (ball_subset_ball hδsmall) hv
  have hupper := (familyWindowMap_local_le haε hδa had hCt hgood hout hin hv).trans
    (smul_le_smul_left (C^2) (localTwoCollisionLaw_le_retained hvsmall))
  rw [smul_smul] at hupper
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA,Measure.smul_apply,smul_eq_mul]
  have hlower := hvolume v hv (A ∩ ball (0 : V) δ) (hA.inter measurableSet_ball) inter_subset_right
  have hAupper : ((familyWindowMeasure a δ).map (familyWindowMap v)) (A ∩ ball (0 : V) δ) ≤
      (C^2*36) * (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v A := by
    exact (hupper _).trans (by
      rw [Measure.smul_apply,smul_eq_mul]
      exact mul_le_mul' le_rfl (measure_mono inter_subset_left))
  have htotal : I * volume (A ∩ ball (0 : V) δ) ≤ (K : ℝ≥0∞)^3 *
      ((C^2*36) * (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v A) := by
    exact hlower.trans (by gcongr)
  calc
    volume (A ∩ ball (0 : V) δ) = I⁻¹ * (I * volume (A ∩ ball (0 : V) δ)) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hI0 hIt,one_mul]
    _ ≤ I⁻¹ * ((K : ℝ≥0∞)^3 *
        ((C^2*36) * (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v A)) := by gcongr
    _ = B * (retainedJump beamAxis ∘ₖ retainedJump beamAxis) v A := by simp only [B,mul_assoc]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform three-jump minorization on the full retained velocity region -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem retained_three_volume_domination :
    ∃ (δ : ℝ) (B : ℝ≥0∞), 0 < δ ∧ δ ≤ 1/4 ∧ B ≠ 0 ∧ B ≠ ⊤ ∧
      ∀ v ∈ referenceRegion,
        volume.restrict (ball (0 : V) δ) ≤ B •
          ((retainedJump beamAxis ∘ₖ retainedJump beamAxis) ∘ₖ retainedJump beamAxis) v := by
  obtain ⟨δ,C,hδ,hδsmall,hC0,hCt,hlocal⟩ := retained_two_volume_domination
  let I := ENNReal.ofReal (beamEntryMass δ)
  have hI0 : I ≠ 0 := by dsimp [I]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (beamEntryMass_pos hδ))
  have hIt : I ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨δ,I⁻¹*C,hδ,hδsmall,mul_ne_zero (ENNReal.inv_ne_zero.mpr hIt) hC0,
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hI0) hCt,?_⟩
  intro v hv
  have hvnorm : ‖v‖ ≤ 5 := by simpa only [referenceRegion,mem_closedBall,dist_zero_right] using hv
  have hentry : I ≤ retainedJump beamAxis v (ball beamAxis δ) := by
    exact (ENNReal.ofReal_le_ofReal (retained_beam_entry hδ hδsmall v hvnorm)).trans
      ENNReal.ofReal_toReal_le
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA,Measure.smul_apply,smul_eq_mul]
  have hbound (u : V) (hu : u ∈ ball beamAxis δ) :
      volume (A ∩ ball (0 : V) δ) ≤
        C*(retainedJump beamAxis ∘ₖ retainedJump beamAxis) u A := by
    have hh := hlocal u hu A
    simpa only [Measure.restrict_apply hA,Measure.smul_apply,smul_eq_mul] using hh
  have htotal : I*volume (A ∩ ball (0 : V) δ) ≤ C*
      ((retainedJump beamAxis ∘ₖ retainedJump beamAxis) ∘ₖ retainedJump beamAxis) v A := by
    calc
      I*volume (A ∩ ball (0 : V) δ) ≤
          retainedJump beamAxis v (ball beamAxis δ)*volume (A ∩ ball (0 : V) δ) :=
        mul_le_mul' hentry le_rfl
      _ = ∫⁻ _u in ball beamAxis δ, volume (A ∩ ball (0 : V) δ) ∂retainedJump beamAxis v := by
        rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]
      _ ≤ ∫⁻ u in ball beamAxis δ,
          C*(retainedJump beamAxis ∘ₖ retainedJump beamAxis) u A ∂retainedJump beamAxis v := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
        exact hbound u hu
      _ ≤ ∫⁻ u, C*(retainedJump beamAxis ∘ₖ retainedJump beamAxis) u A ∂retainedJump beamAxis v :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = _ := by rw [lintegral_const_mul' _ _ hCt,Kernel.comp_apply' _ _ _ hA]
  calc
    volume (A ∩ ball (0 : V) δ) = I⁻¹*(I*volume (A ∩ ball (0 : V) δ)) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hI0 hIt,one_mul]
    _ ≤ I⁻¹*(C*
        ((retainedJump beamAxis ∘ₖ retainedJump beamAxis) ∘ₖ retainedJump beamAxis) v A) := by gcongr
    _ = _ := by rw [mul_assoc]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

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

/-! # A constant-rate uniformization of the retained velocity dynamics -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniformizedKernel_lower (v : RetainedState) :
    ENNReal.ofReal (1/12 : ℝ) • stateKernel v ≤ uniformizedKernel v := by
  rw [uniformizedKernel_apply]
  apply Measure.le_iff.mpr
  intro A _hA
  simp only [Measure.smul_apply,Measure.add_apply,smul_eq_mul]
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal (jumpFraction_bounds v).1) le_rfl).trans
    (le_add_right le_rfl)

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

theorem statePotential_lower (v : RetainedState) : 11*Real.pi/6 ≤ statePotential v :=
  retainedPotential_coarse beamAxis v.1 axis_norms.2.2 (retainedState_norm v)

theorem stateFrequency_bounds (v : RetainedState) :
    4*Real.pi ≤ stateFrequency v ∧ stateFrequency v ≤ 24*Real.pi :=
  ⟨frequency_lower v.1 beamAxis axis_norms.2.2,
    frequency_upper v.1 beamAxis axis_norms.2.2 (retainedState_norm v)⟩

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

theorem uniformizedKernel_intensity (v : RetainedState) :
    ENNReal.ofReal (48*Real.pi) • uniformizedKernel v =
      ENNReal.ofReal (stateRate v) • stateKernel v +
        ENNReal.ofReal (48*Real.pi-stateRate v) • Measure.dirac v := by
  rw [uniformizedKernel_apply,smul_add,smul_smul,smul_smul,
    ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  have hΛ : (48*Real.pi : ℝ) ≠ 0 := by positivity
  congr 2
  · rw [jumpFraction,mul_div_cancel₀ _ hΛ]
  · unfold jumpFraction
    field_simp

theorem branchingKernel_decomposition (v : RetainedState) :
    branchingKernel v = ENNReal.ofReal (48*Real.pi) • uniformizedKernel v +
      ENNReal.ofReal (statePotential v) • Measure.dirac v := by
  have hrBound := (stateRate_bounds v).2
  have hW : 0 ≤ statePotential v := le_trans (by positivity) (statePotential_lower v)
  rw [branchingKernel_apply,uniformizedKernel_intensity,add_assoc,← add_smul,
    ← ENNReal.ofReal_add (sub_nonneg.mpr hrBound) hW]
  congr 2
  unfold statePotential
  ring_nf

theorem branchingKernel_lower (v : RetainedState) :
    ENNReal.ofReal (48*Real.pi) • uniformizedKernel v +
      ENNReal.ofReal (11*Real.pi/6) • Measure.dirac v ≤ branchingKernel v := by
  rw [branchingKernel_decomposition]
  apply add_le_add le_rfl
  apply Measure.le_iff.mpr
  intro A _hA
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (statePotential_lower v)) le_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Three-step common volume on the bounded reference state space -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem stateKernel_map_kernel : stateKernel.map (Subtype.val : RetainedState → V) =
    (retainedJump beamAxis).comap Subtype.val measurable_subtype_coe := by
  ext1 v
  rw [Kernel.map_apply _ measurable_subtype_coe,Kernel.comap_apply,stateKernel_map]

theorem stateKernel_pow_map (n : ℕ) : (stateKernel^n).map (Subtype.val : RetainedState → V) =
    ((retainedJump beamAxis)^n).comap Subtype.val measurable_subtype_coe := by
  induction n with
  | zero =>
    simp only [pow_zero]
    change Kernel.id.map (Subtype.val : RetainedState → V) =
      Kernel.id.comap Subtype.val measurable_subtype_coe
    rw [Kernel.id_map,Kernel.id_comap]
  | succ n ih =>
    have hs : stateKernel^(n+1) = stateKernel ∘ₖ (stateKernel^n) := by
      simpa only [add_comm,pow_one] using Kernel.pow_add stateKernel 1 n
    have hr : (retainedJump beamAxis)^(n+1) =
        retainedJump beamAxis ∘ₖ ((retainedJump beamAxis)^n) := by
      simpa only [add_comm,pow_one] using Kernel.pow_add (retainedJump beamAxis) 1 n
    rw [hs,hr]
    rw [Kernel.map_comp,stateKernel_map_kernel,← Kernel.comp_map _ _ measurable_subtype_coe,ih]
    ext v A hA
    simp only [Kernel.comap_apply,Kernel.comp_apply' _ _ _ hA]

theorem state_three_volume_domination :
    ∃ (δ : ℝ) (B : ℝ≥0∞), 0 < δ ∧ δ ≤ 1/4 ∧ B ≠ 0 ∧ B ≠ ⊤ ∧
      ∀ v : RetainedState, stateBallMeasure δ ≤ B • (stateKernel^3) v := by
  obtain ⟨δ,B,hδ,hδsmall,hB0,hBt,hbound⟩ := retained_three_volume_domination
  refine ⟨δ,B,hδ,hδsmall,hB0,hBt,?_⟩
  intro v
  have hm : ((stateKernel^3) v).map (Subtype.val : RetainedState → V) =
      ((retainedJump beamAxis)^3) v.1 := by
    rw [← Kernel.map_apply _ measurable_subtype_coe,stateKernel_pow_map,Kernel.comap_apply]
  have h3 : ((retainedJump beamAxis)^3) =
      ((retainedJump beamAxis ∘ₖ retainedJump beamAxis) ∘ₖ retainedJump beamAxis) := by
    have htwo : (retainedJump beamAxis)^2 = retainedJump beamAxis ∘ₖ retainedJump beamAxis := by
      simpa only [pow_one] using Kernel.pow_add (retainedJump beamAxis) 1 1
    calc
      (retainedJump beamAxis)^3 = ((retainedJump beamAxis)^2) ∘ₖ retainedJump beamAxis := by
        simpa only [pow_one] using Kernel.pow_add (retainedJump beamAxis) 2 1
      _ = _ := by rw [htwo]
  apply Measure.le_iff.mpr
  intro A hA
  have hi := (MeasurableEmbedding.subtype_coe referenceRegion_measurable).measurableSet_image.mpr hA
  have hh := hbound v.1 v.2 ((Subtype.val : RetainedState → V) '' A)
  rw [← h3,← hm,Measure.smul_apply,smul_eq_mul,Measure.map_apply measurable_subtype_coe hi,
    Subtype.val_injective.preimage_image] at hh
  rw [stateBallMeasure,comap_subtype_coe_apply referenceRegion_measurable,Measure.smul_apply,smul_eq_mul]
  exact hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Reversal symmetry on the bounded state space and the uniformized chain -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem stateNeg_val (v : RetainedState) : (stateNeg v).1 = -v.1 := rfl

theorem stateKernel_neg (v : RetainedState) : (stateKernel v).map stateNeg = stateKernel (stateNeg v) := by
  apply (MeasurableEmbedding.subtype_coe referenceRegion_measurable).map_injective
  rw [Measure.map_map measurable_subtype_coe stateNeg.measurable,stateKernel_map]
  have heq : (Subtype.val : RetainedState → V) ∘ stateNeg = Neg.neg ∘ Subtype.val := rfl
  rw [heq,← Measure.map_map measurable_neg measurable_subtype_coe,stateKernel_map,
    retainedJump_neg _ _ axis_norms.2.2]
  rfl

theorem frequency_neg (e v : V) : frequency (-v) e = frequency v e := by
  have hm : ‖-v-e‖ = ‖v+e‖ := by rw [show -v-e = -(v+e) by module,norm_neg]
  have hp : ‖-v+e‖ = ‖v-e‖ := by rw [show -v+e = -(v-e) by module,norm_neg]
  simp only [frequency,hm,hp]
  rw [add_comm]

theorem stateRate_neg (v : RetainedState) : stateRate (stateNeg v) = stateRate v := by
  simp only [stateRate,stateNeg_val,retainedRate,retention_neg _ _ axis_norms.2.2,frequency_neg]

theorem jumpFraction_neg (v : RetainedState) : jumpFraction (stateNeg v) = jumpFraction v := by
  simp only [jumpFraction,stateRate_neg]

theorem uniformizedKernel_neg (v : RetainedState) :
    (uniformizedKernel v).map stateNeg = uniformizedKernel (stateNeg v) := by
  rw [uniformizedKernel_apply,uniformizedKernel_apply,Measure.map_add,Measure.map_smul,
    Measure.map_smul,stateKernel_neg,Measure.map_dirac' stateNeg.measurable,jumpFraction_neg]
  all_goals first | exact stateNeg.measurable | exact stateNeg.measurable.aemeasurable

theorem stateBallMeasure_map {δ : ℝ} (hδ : δ ≤ 5) :
    (stateBallMeasure δ).map (Subtype.val : RetainedState → V) = volume.restrict (ball (0 : V) δ) := by
  rw [stateBallMeasure,map_comap_subtype_coe referenceRegion_measurable]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [ae_restrict_mem (μ := (volume : Measure V)) measurableSet_ball] with v hv
  change dist v 0 ≤ 5
  exact (le_of_lt hv).trans hδ

theorem volume_ball_neg (δ : ℝ) :
    (volume.restrict (ball (0 : V) δ)).map (Neg.neg : V → V) = volume.restrict (ball (0 : V) δ) := by
  have hb : (Neg.neg : V → V) ⁻¹' ball (0 : V) δ = ball (0 : V) δ := by
    ext v
    simp only [mem_preimage,mem_ball,dist_zero_right,norm_neg]
  ext A hA
  rw [Measure.map_apply measurable_neg hA,Measure.restrict_apply (measurable_neg hA),
    ← hb,← preimage_inter,Measure.measure_preimage_neg,Measure.restrict_apply hA,hb]

theorem stateBallMeasure_neg {δ : ℝ} (hδ : δ ≤ 5) :
    (stateBallMeasure δ).map stateNeg = stateBallMeasure δ := by
  apply (MeasurableEmbedding.subtype_coe referenceRegion_measurable).map_injective
  rw [Measure.map_map measurable_subtype_coe stateNeg.measurable,stateBallMeasure_map hδ]
  have heq : (Subtype.val : RetainedState → V) ∘ stateNeg = Neg.neg ∘ Subtype.val := rfl
  rw [heq,← Measure.map_map measurable_neg measurable_subtype_coe,stateBallMeasure_map hδ,volume_ball_neg]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The constant-rate chain retains the three-collision common volume -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem stateKernel_power_le_uniformized (n : ℕ) (v : RetainedState) :
    (ENNReal.ofReal (1/12 : ℝ))^n • (stateKernel^n) v ≤ (uniformizedKernel^n) v := by
  induction n generalizing v with
  | zero => simp only [pow_zero,one_smul]; exact le_rfl
  | succ n ih =>
    have hs : stateKernel^(n+1) = (stateKernel^n) ∘ₖ stateKernel := by
      simpa only [pow_one] using Kernel.pow_add stateKernel n 1
    have hu : uniformizedKernel^(n+1) = (uniformizedKernel^n) ∘ₖ uniformizedKernel := by
      simpa only [pow_one] using Kernel.pow_add uniformizedKernel n 1
    rw [hs,hu]
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.smul_apply,smul_eq_mul,Kernel.comp_apply' _ _ _ hA,Kernel.comp_apply' _ _ _ hA]
    calc
      (ENNReal.ofReal (1/12 : ℝ))^(n+1) * (∫⁻ u, (stateKernel^n) u A ∂stateKernel v) =
          ∫⁻ u, (ENNReal.ofReal (1/12 : ℝ))^n * (stateKernel^n) u A
            ∂(ENNReal.ofReal (1/12 : ℝ) • stateKernel v) := by
        rw [lintegral_smul_measure,lintegral_const_mul' _ _
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),pow_succ]
        simp only [smul_eq_mul]
        ac_rfl
      _ ≤ ∫⁻ u, (uniformizedKernel^n) u A ∂uniformizedKernel v := by
        apply lintegral_mono' (uniformizedKernel_lower v)
        intro u
        exact ih u A

theorem uniformized_three_volume_domination :
    ∃ (δ : ℝ) (B : ℝ≥0∞), 0 < δ ∧ δ ≤ 1/4 ∧ B ≠ 0 ∧ B ≠ ⊤ ∧
      ∀ v : RetainedState, stateBallMeasure δ ≤ B • (uniformizedKernel^3) v := by
  obtain ⟨δ,C,hδ,hδsmall,hC0,hCt,hbound⟩ := state_three_volume_domination
  let c := (ENNReal.ofReal (1/12 : ℝ))^3
  have hc0 : c ≠ 0 := by dsimp [c] <;> positivity
  have hct : c ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ⟨δ,C*c⁻¹,hδ,hδsmall,mul_ne_zero hC0 (ENNReal.inv_ne_zero.mpr hct),
    ENNReal.mul_ne_top hCt (ENNReal.inv_ne_top.mpr hc0),?_⟩
  intro v
  have hp := smul_le_smul_left c⁻¹ (stateKernel_power_le_uniformized 3 v)
  rw [smul_smul,show c⁻¹*(ENNReal.ofReal (1/12 : ℝ))^3 = 1 from
    ENNReal.inv_mul_cancel hc0 hct,one_smul] at hp
  exact (hbound v).trans ((smul_le_smul_left C hp).trans_eq (smul_smul _ _ _))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A nonzero symmetric common part of all three-step transition laws -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem stateBallMeasure_univ {δ : ℝ} (hδ : δ ≤ 5) :
    stateBallMeasure δ univ = volume (ball (0 : V) δ) := by
  have h := congrArg (fun μ : Measure V => μ univ) (stateBallMeasure_map hδ)
  simpa only [Measure.map_apply measurable_subtype_coe MeasurableSet.univ,preimage_univ,
    Measure.restrict_apply_univ] using h

theorem uniformized_common_part : ∃ ρ : Measure RetainedState,
    IsFiniteMeasure ρ ∧ 0 < ρ univ ∧ ρ univ ≤ 1/2 ∧ ρ.map stateNeg = ρ ∧
      ∀ v : RetainedState, ρ ≤ (uniformizedKernel^3) v := by
  obtain ⟨δ,B,hδ,hδsmall,hB0,hBt,hbound⟩ := uniformized_three_volume_domination
  let c : ℝ≥0∞ := (1/2)*B⁻¹
  let ρ : Measure RetainedState := c • stateBallMeasure δ
  have hc : 0 < c := pos_iff_ne_zero.mpr
    (mul_ne_zero (by norm_num) (ENNReal.inv_ne_zero.mpr hBt))
  have hδfive : δ ≤ 5 := hδsmall.trans (by norm_num)
  have hscaled (v : RetainedState) : ρ ≤ (1/2 : ℝ≥0∞) • (uniformizedKernel^3) v := by
    calc
      ρ ≤ c • (B • (uniformizedKernel^3) v) := smul_le_smul_left c (hbound v)
      _ = _ := by
        rw [smul_smul]
        dsimp only [c]
        rw [mul_assoc,ENNReal.inv_mul_cancel hB0 hBt,mul_one]
  have hrpos : 0 < ρ univ := by
    rw [Measure.smul_apply,smul_eq_mul,stateBallMeasure_univ hδfive]
    exact pos_iff_ne_zero.mpr (mul_ne_zero hc.ne' (measure_ball_pos volume (0 : V) hδ).ne')
  let z : RetainedState := ⟨0,by simp [referenceRegion]⟩
  have hrsmall : ρ univ ≤ 1/2 := by
    have hh := hscaled z univ
    simpa only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using hh
  have hrfinite : IsFiniteMeasure ρ := ⟨hrsmall.trans_lt (by norm_num)⟩
  refine ⟨ρ,hrfinite,hrpos,hrsmall,?_,?_⟩
  · change (c • stateBallMeasure δ).map stateNeg = c • stateBallMeasure δ
    rw [Measure.map_smul,stateBallMeasure_neg hδfive]
  · intro v
    apply Measure.le_iff.mpr
    intro A _hA
    exact (hscaled v A).trans (by
      rw [Measure.smul_apply,smul_eq_mul]
      exact mul_le_of_le_one_left bot_le (by norm_num))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Contraction of odd observables by the actual three-step common part -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem state_odd_integral_zero {ρ : Measure RetainedState} (hρ : ρ.map stateNeg = ρ)
    {f : RetainedState → V} (hodd : ∀ v, f (stateNeg v) = -f v) : ∫ v, f v ∂ρ = 0 := by
  have hh := (show MeasurePreserving stateNeg ρ ρ from ⟨stateNeg.measurable,hρ⟩).integral_comp
    stateNeg.measurableEmbedding f
  simp_rw [hodd] at hh
  rw [integral_neg] at hh
  have htwo : (2 : ℝ) • (∫ v, f v ∂ρ) = 0 := by
    rw [two_smul]
    exact (congrArg (fun z : V => z + ∫ v, f v ∂ρ) hh.symm).trans (neg_add_cancel _)
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem integral_common_part_bound {μ ρ : Measure RetainedState} [IsProbabilityMeasure μ]
    [IsFiniteMeasure ρ] (hρ : ρ ≤ μ) (hsym : ρ.map stateNeg = ρ)
    {f : RetainedState → V} (hf : Measurable f) (hodd : ∀ v, f (stateNeg v) = -f v)
    {M : ℝ} (hM : ∀ v, ‖f v‖ ≤ M) :
    ‖∫ v, f v ∂μ‖ ≤ (1-ρ.real univ)*M := by
  have hfμ : Integrable f μ := (integrable_const M).mono' hf.aestronglyMeasurable (ae_of_all _ hM)
  have hfr := hfμ.mono_measure hρ
  have hfd := hfμ.mono_measure (Measure.sub_le : μ-ρ ≤ μ)
  have hm : (μ-ρ).real univ + ρ.real univ = 1 := by
    rw [← measureReal_add_apply,Measure.sub_add_cancel_of_le hρ]
    simp
  have hz := state_odd_integral_zero hsym hodd
  calc
    ‖∫ v, f v ∂μ‖ = ‖∫ v, f v ∂(μ-ρ)‖ := by
      nth_rw 1 [← Measure.sub_add_cancel_of_le hρ]
      rw [integral_add_measure hfd hfr,hz,add_zero]
    _ ≤ M*(μ-ρ).real univ := norm_integral_le_of_norm_le_const (ae_of_all _ hM)
    _ = (1-ρ.real univ)*M := by rw [show (μ-ρ).real univ = 1-ρ.real univ by linarith]; ring

theorem uniformized_three_odd_contraction : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧
    ∀ (f : RetainedState → V), Measurable f → (∀ v, f (stateNeg v) = -f v) →
      ∀ M : ℝ, (∀ v, ‖f v‖ ≤ M) → ∀ v : RetainedState,
        ‖∫ u, f u ∂(uniformizedKernel^3) v‖ ≤ (1-ε)*M := by
  obtain ⟨ρ,hρfin,hρpos,hρsmall,hρsym,hρbound⟩ := uniformized_common_part
  let _ := hρfin
  have hεpos : 0 < ρ.real univ := ENNReal.toReal_pos hρpos.ne' (measure_ne_top ρ univ)
  have hεsmall : ρ.real univ ≤ 1/2 := by
    have hh := (ENNReal.toReal_le_toReal (measure_ne_top ρ univ) (by norm_num)).mpr hρsmall
    norm_num at hh ⊢
    exact hh
  refine ⟨ρ.real univ,hεpos,hεsmall,?_⟩
  intro f hf ho M hM v
  exact integral_common_part_bound (hρbound v) hρsym hf ho hM

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Measurable symmetric averages of the actual uniformized velocity chain -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniformizedKernel_pow_neg (n : ℕ) :
    (uniformizedKernel^n).map stateNeg =
      (uniformizedKernel^n).comap stateNeg stateNeg.measurable := by
  have hb : uniformizedKernel.map stateNeg = uniformizedKernel.comap stateNeg stateNeg.measurable := by
    ext1 v
    rw [Kernel.map_apply _ stateNeg.measurable,Kernel.comap_apply,uniformizedKernel_neg]
  induction n with
  | zero =>
    simp only [pow_zero]
    change Kernel.id.map stateNeg = Kernel.id.comap stateNeg stateNeg.measurable
    rw [Kernel.id_map,Kernel.id_comap]
  | succ n ih =>
    have hs : uniformizedKernel^(n+1) = (uniformizedKernel^n) ∘ₖ uniformizedKernel := by
      simpa only [pow_one] using Kernel.pow_add uniformizedKernel n 1
    rw [hs,Kernel.map_comp,ih,← Kernel.comp_map _ _ stateNeg.measurable,hb]
    ext v A hA
    simp only [Kernel.comap_apply,Kernel.comp_apply' _ _ _ hA]

theorem chainAverage_measurable (n : ℕ) {f : RetainedState → V} (hf : Measurable f) :
    Measurable (chainAverage n f) := hf.stronglyMeasurable.integral_kernel.measurable

theorem chainAverage_odd (n : ℕ) {f : RetainedState → V}
    (hodd : ∀ v, f (stateNeg v) = -f v) :
    ∀ v, chainAverage n f (stateNeg v) = -chainAverage n f v := by
  intro v
  have hm : ((uniformizedKernel^n) v).map stateNeg = (uniformizedKernel^n) (stateNeg v) := by
    rw [← Kernel.map_apply _ stateNeg.measurable,uniformizedKernel_pow_neg,Kernel.comap_apply]
  unfold chainAverage
  rw [← hm,stateNeg.measurableEmbedding.integral_map]
  simp_rw [hodd]
  rw [integral_neg]

theorem chainAverage_bound (n : ℕ) {f : RetainedState → V} {M : ℝ}
    (hM : ∀ v, ‖f v‖ ≤ M) (v : RetainedState) : ‖chainAverage n f v‖ ≤ M := by
  have h := norm_integral_le_of_norm_le_const (μ := (uniformizedKernel^n) v) (ae_of_all _ hM)
  simpa only [chainAverage,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using! h

theorem chainAverage_zero (f : RetainedState → V) (v : RetainedState) : chainAverage 0 f v = f v := by
  unfold chainAverage
  change (∫ u, f u ∂Measure.dirac v) = f v
  simp

theorem chainAverage_add (n m : ℕ) {f : RetainedState → V} (hf : Measurable f)
    {M : ℝ} (hM : ∀ v, ‖f v‖ ≤ M) (v : RetainedState) :
    chainAverage (n+m) f v = chainAverage m (chainAverage n f) v := by
  unfold chainAverage
  rw [Kernel.pow_add]
  apply Kernel.integral_comp
  exact (integrable_const M).mono' hf.aestronglyMeasurable (ae_of_all _ hM)

end BoltzmannNonuniqueness.ReferenceGeometry

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

/-! # Geometric decay of odd observables for the actual velocity chain -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniformized_odd_decay : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/2 ∧
    ∀ (f : RetainedState → V), Measurable f → (∀ v, f (stateNeg v) = -f v) →
      ∀ M : ℝ, (∀ v, ‖f v‖ ≤ M) → ∀ (n : ℕ) (v : RetainedState),
        ‖chainAverage n f v‖ ≤ (1-ε)^(n/3)*M := by
  obtain ⟨ε,hε,hεsmall,hcontract⟩ := uniformized_three_odd_contraction
  refine ⟨ε,hε,hεsmall,?_⟩
  intro f hf ho M hM
  have hblocks : ∀ (k : ℕ) (v : RetainedState),
      ‖chainAverage (3*k) f v‖ ≤ (1-ε)^k*M := by
    intro k
    induction k with
    | zero => intro v; simpa only [Nat.mul_zero,chainAverage_zero,pow_zero,one_mul] using hM v
    | succ k ih =>
      intro v
      have hh := hcontract (chainAverage (3*k) f) (chainAverage_measurable _ hf)
        (chainAverage_odd _ ho) ((1-ε)^k*M) ih v
      calc
        ‖chainAverage (3*(k+1)) f v‖ = ‖chainAverage 3 (chainAverage (3*k) f) v‖ := by
          rw [show 3*(k+1) = 3*k+3 by omega,chainAverage_add _ _ hf hM]
        _ ≤ (1-ε)*((1-ε)^k*M) := hh
        _ = (1-ε)^(k+1)*M := by rw [pow_succ]; ring
  intro n v
  have hn : 3*(n/3)+n%3 = n := by omega
  calc
    ‖chainAverage n f v‖ = ‖chainAverage (n%3) (chainAverage (3*(n/3)) f) v‖ := by
      nth_rw 1 [← hn]
      rw [chainAverage_add _ _ hf hM]
    _ ≤ (1-ε)^(n/3)*M := chainAverage_bound _ (hblocks (n/3)) v

theorem uniformized_velocity_mean_decay : ∃ q : ℝ, 0 < q ∧ q < 1 ∧
    ∀ (n : ℕ) (v : RetainedState),
      ‖∫ u : RetainedState, (u : V) ∂(uniformizedKernel^n) v‖ ≤ 5*q^(n/3) := by
  obtain ⟨ε,hε,hεsmall,hdecay⟩ := uniformized_odd_decay
  refine ⟨1-ε,by linarith,by linarith,?_⟩
  intro n v
  have hh := hdecay (Subtype.val : RetainedState → V) measurable_subtype_coe
    (fun _ => rfl) 5 retainedState_norm n v
  simpa only [chainAverage,mul_comm] using hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A geometric bound at every jump count -/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniformized_geometric_mean : ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ r < 1 ∧
    ∀ (n : ℕ) (v : RetainedState),
      ‖∫ u : RetainedState, (u : V) ∂(uniformizedKernel^n) v‖ ≤ C*r^n := by
  obtain ⟨q,hq,hq1,hbound⟩ := uniformized_velocity_mean_decay
  let r := (q+2)/3
  have hr : 0 < r := by dsimp [r] <;> linarith
  have hr1 : r < 1 := by dsimp [r] <;> linarith
  have hqr : q ≤ r^3 := by
    have hh := mul_nonneg (sq_nonneg (q-1)) (show 0 ≤ q+8 by linarith)
    dsimp [r]
    nlinarith
  refine ⟨5/r^2,r,by positivity,hr,hr1,?_⟩
  intro n v
  have hp := pow_le_pow_left₀ hq.le hqr (n/3)
  have hrem : r^2 ≤ r^(n%3) := by
    have hh : n%3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases he : n%3
    · simp only [pow_zero] <;> nlinarith [sq_nonneg r]
    · simp only [pow_one] <;> nlinarith
    · exact le_rfl
  have hpow : q^(n/3)*r^2 ≤ r^n := by
    calc
      q^(n/3)*r^2 ≤ (r^3)^(n/3)*r^(n%3) :=
        mul_le_mul hp hrem (sq_nonneg _) (pow_nonneg (by positivity) _)
      _ = r^n := by rw [← pow_mul,← pow_add]; congr 1; omega
  have hh : 5*q^(n/3) ≤ (5/r^2)*r^n := by
    rw [div_mul_eq_mul_div,le_div_iff₀ (by positivity : 0 < r^2)]
    nlinarith
  exact (hbound n v).trans hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The constant-rate reference transition law as an actual Poisson mixture -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem poissonKernel_apply (r : ℝ≥0) (v : RetainedState) :
    poissonKernel r v = (poissonMeasure r).bind (fun n => (uniformizedKernel^n) v) := by
  rw [poissonKernel,Kernel.sum_apply,poissonMeasure,Measure.bind_sum _ _ (Measurable.of_discrete.aemeasurable)]
  apply congrArg Measure.sum
  funext n
  rw [Kernel.withDensity_apply _ measurable_const,withDensity_const,
    Measure.bind_smul _ _,Measure.dirac_bind Measurable.of_discrete,Measure.sum_smul_dirac_singleton]

instance poissonKernel_isMarkov (r : ℝ≥0) : IsMarkovKernel (poissonKernel r) := by
  constructor
  intro v
  constructor
  rw [poissonKernel_apply,Measure.bind_apply MeasurableSet.univ (Measurable.of_discrete.aemeasurable)]
  simp only [measure_univ,lintegral_const,one_mul]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniformly bounded sums of the expected velocities of the discrete chain -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem velocitySum_measurable (n : ℕ) : Measurable (velocitySum n) := by
  unfold velocitySum
  exact Finset.measurable_sum _ fun k _ => chainAverage_measurable k measurable_subtype_coe

theorem velocitySum_bound (n : ℕ) (v : RetainedState) : ‖velocitySum n v‖ ≤ (n+1 : ℕ)*5 := by
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖chainAverage k (fun u => (u : V)) v‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range (n+1), (5 : ℝ) :=
      Finset.sum_le_sum fun k _ => chainAverage_bound k retainedState_norm v
    _ = _ := by simp

theorem velocitySum_succ (n : ℕ) (v : RetainedState) :
    velocitySum (n+1) v = (v : V) + ∫ u, velocitySum n u ∂uniformizedKernel v := by
  have hi (k : ℕ) : Integrable (chainAverage k (fun u => (u : V))) (uniformizedKernel v) :=
    (integrable_const (5 : ℝ)).mono' (chainAverage_measurable k measurable_subtype_coe).aestronglyMeasurable
      (ae_of_all _ (chainAverage_bound k retainedState_norm))
  unfold velocitySum
  rw [integral_finsetSum _ (fun k _ => hi k),Finset.sum_range_succ']
  simp only [chainAverage_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [chainAverage,pow_one] using
    chainAverage_add k 1 measurable_subtype_coe retainedState_norm v

theorem velocitySum_uniform_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (n : ℕ) (v : RetainedState), ‖velocitySum n v‖ ≤ B := by
  obtain ⟨C,r,hC,hr,hr1,hmean⟩ := uniformized_geometric_mean
  refine ⟨C/(1-r),by positivity,?_⟩
  intro n v
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖chainAverage k (fun u => (u : V)) v‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n+1), C*r^k := Finset.sum_le_sum fun k _ => hmean k v
    _ = C * ∑ k ∈ Finset.range (n+1), r^k := (Finset.mul_sum _ _ _).symm
    _ ≤ C/(1-r) := by
      rw [div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ hC.le
      have hs := hasSum_geometric_of_lt_one hr.le hr1
      exact (Summable.sum_le_tsum (Finset.range (n+1)) (fun i _ => pow_nonneg hr.le i) hs.summable).trans_eq hs.tsum_eq

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Chapman–Kolmogorov for the actual Poisson reference transition law -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory MeasureTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem poissonKernel_lintegral (r : ℝ≥0) (v : RetainedState) {f : RetainedState → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ u, f u ∂poissonKernel r v) =
      ∫⁻ n, ∫⁻ u, f u ∂(uniformizedKernel^n) v ∂poissonMeasure r := by
  rw [poissonKernel_apply,Measure.lintegral_bind (Measurable.of_discrete.aemeasurable) hf.aemeasurable]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Position-preserving jumps and deterministic flights of the reference process -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem freeFlight_displacement (t : ℝ) (z : FlightState) :
    ‖(freeFlight t z).1-z.1‖ ≤ 5*|t| := by
  simp only [freeFlight,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
  have hh := mul_le_mul_of_nonneg_left (retainedState_norm z.2) (abs_nonneg t)
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

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

theorem jumpAfterWait_lintegral (q : TimeFlightState × ℝ) {f : TimeFlightState → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ p, f p ∂jumpAfterWait q) =
      ∫⁻ u, f (advanceState q.1 q.2 u) ∂uniformizedKernel q.1.2.2 := by
  rw [jumpAfterWait,Kernel.lintegral_map _ advanceState_measurable q hf]
  simpa only [Function.comp_def,Kernel.comap_apply] using!
    Kernel.lintegral_id_prod (hf.comp advanceState_measurable)
      (uniformizedKernel.comap (fun q : TimeFlightState × ℝ => q.1.2.2) (by fun_prop)) q

theorem historyStep_lintegral (p : TimeFlightState) {f : TimeFlightState → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ q, f q ∂historyStep p) =
      ∫⁻ s in Ioc 0 p.1, ∫⁻ u, f (advanceState p s u) ∂uniformizedKernel p.2.2 := by
  rw [historyStep,Kernel.lintegral_comp _ _ _ hf,
    Kernel.lintegral_id_prod (hf.lintegral_kernel (κ := jumpAfterWait))]
  simp_rw [jumpAfterWait_lintegral _ hf]
  rw [waitingTime_apply]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The actual finite free-flight and collision-history kernels -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historyKernel_zero : historyKernel 0 = Kernel.deterministic finishFlight finishFlight_measurable := by
  unfold historyKernel
  change Kernel.id.map finishFlight = _
  exact Kernel.id_map finishFlight_measurable

theorem historyKernel_succ_lintegral (n : ℕ) (p : TimeFlightState) {f : FlightState → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ z, f z ∂historyKernel (n+1) p) =
      ∫⁻ s in Ioc 0 p.1, ∫⁻ u, ∫⁻ z, f z ∂historyKernel n (advanceState p s u)
        ∂uniformizedKernel p.2.2 := by
  have hs : historyStep^(n+1) = (historyStep^n) ∘ₖ historyStep := by
    simpa only [pow_one] using Kernel.pow_add historyStep n 1
  have hg : Measurable (fun q : TimeFlightState => ∫⁻ w, f (finishFlight w) ∂(historyStep^n) q) :=
    (hf.comp finishFlight_measurable).lintegral_kernel
  calc
    (∫⁻ z, f z ∂historyKernel (n+1) p) =
        ∫⁻ q, ∫⁻ w, f (finishFlight w) ∂(historyStep^n) q ∂historyStep p := by
      rw [historyKernel,hs,Kernel.lintegral_map _ finishFlight_measurable _ hf]
      exact Kernel.lintegral_comp _ _ _ (hf.comp finishFlight_measurable)
    _ = ∫⁻ s in Ioc 0 p.1, ∫⁻ u, ∫⁻ w, f (finishFlight w)
        ∂(historyStep^n) (advanceState p s u) ∂uniformizedKernel p.2.2 := historyStep_lintegral p hg
    _ = _ := by
      apply lintegral_congr
      intro s
      apply lintegral_congr
      intro u
      exact (Kernel.lintegral_map _ finishFlight_measurable _ hf).symm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The exact time-simplex factor for a fixed number of collisions -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem simplexTime_ne_top (n : ℕ) (T : ℝ) : simplexTime n T ≠ ⊤ := ENNReal.ofReal_ne_top

theorem simplexTime_zero (T : ℝ) : simplexTime 0 T = 1 := by simp [simplexTime]

theorem simplexTime_integral (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (∫⁻ s in Ioc 0 T, simplexTime n (T-s)) = simplexTime (n+1) T := by
  let f : ℝ → ℝ := fun s => (T-s)^n/(n.factorial : ℝ)
  have hi : IntegrableOn f (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
      ((show Continuous f by dsimp [f]; fun_prop).intervalIntegrable 0 T)
  change (∫⁻ s in Ioc 0 T, ENNReal.ofReal (f s)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← intervalIntegral.integral_of_le hT]
    change ENNReal.ofReal (∫ s in (0 : ℝ)..T, (T-s)^n/(n.factorial : ℝ)) = _
    rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^n),
      integral_pow]
    simp only [sub_self,sub_zero,zero_pow (Nat.succ_ne_zero n),simplexTime,
      Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    congr 1
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr hs.2) _) (Nat.cast_nonneg _)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The first two time moments on a collision simplex -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem simplexVolume_nonneg (n : ℕ) {T : ℝ} (hT : 0 ≤ T) : 0 ≤ simplexVolume n T := by
  unfold simplexVolume
  positivity

theorem simplexTime_toReal (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (simplexTime n T).toReal = simplexVolume n T :=
  ENNReal.toReal_ofReal (simplexVolume_nonneg n hT)

theorem simplexVolume_continuous (n : ℕ) : Continuous (simplexVolume n) := by
  unfold simplexVolume
  fun_prop

theorem simplexVolume_step (n : ℕ) (T : ℝ) :
    (n+1 : ℝ)*simplexVolume (n+1) T = T*simplexVolume n T := by
  simp only [simplexVolume,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp

theorem integral_simplexVolume (n : ℕ) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, simplexVolume n (T-s)) = simplexVolume (n+1) T := by
  simp only [simplexVolume,intervalIntegral.integral_div]
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^n),integral_pow]
  simp only [sub_self,sub_zero,zero_pow (Nat.succ_ne_zero n),Nat.factorial_succ,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp

theorem integral_time_simplexVolume (n : ℕ) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, s*simplexVolume n (T-s)) = simplexVolume (n+2) T := by
  have hp (s : ℝ) : s*simplexVolume n (T-s) =
      T*simplexVolume n (T-s)-(n+1 : ℝ)*simplexVolume (n+1) (T-s) := by
    rw [simplexVolume_step]
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_sub,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,integral_simplexVolume,integral_simplexVolume]
  · have h := simplexVolume_step (n+1) T
    push_cast at h
    nlinarith
  · exact ((simplexVolume_continuous n).comp (by fun_prop)).const_mul T |>.intervalIntegrable _ _
  · exact ((simplexVolume_continuous (n+1)).comp (by fun_prop)).const_mul (n+1 : ℝ) |>.intervalIntegrable _ _

theorem integral_time_sq_simplexVolume (n : ℕ) (T : ℝ) :
    (∫ s in (0 : ℝ)..T, s^2*simplexVolume n (T-s)) = 2*simplexVolume (n+3) T := by
  have hp (s : ℝ) : s^2*simplexVolume n (T-s) =
      T*(s*simplexVolume n (T-s))-(n+1 : ℝ)*(s*simplexVolume (n+1) (T-s)) := by
    rw [mul_left_comm (n+1 : ℝ) s, simplexVolume_step]
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_sub,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,integral_time_simplexVolume,integral_time_simplexVolume]
  · have h := simplexVolume_step (n+2) T
    push_cast at h
    nlinarith
  · exact (show Continuous (fun s : ℝ => T*(s*simplexVolume n (T-s))) by
      unfold simplexVolume; fun_prop).intervalIntegrable _ _
  · exact (show Continuous (fun s : ℝ => (n+1 : ℝ)*(s*simplexVolume (n+1) (T-s))) by
      unfold simplexVolume; fun_prop).intervalIntegrable _ _

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Velocity marginal and total mass of each actual flight history -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historyKernel_velocity_lintegral (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1)
    {f : RetainedState → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z.2 ∂historyKernel n p) =
      simplexTime n p.1 * ∫⁻ u, f u ∂(uniformizedKernel^n) p.2.2 := by
  induction n generalizing p with
  | zero =>
    rw [historyKernel_zero,Kernel.deterministic_apply,lintegral_dirac' (finishFlight p) (show Measurable (fun z : FlightState => f z.2) from hf.comp measurable_snd)]
    simp only [simplexTime_zero,one_mul,finishFlight,freeFlight,pow_zero]
    change f p.2.2 = ∫⁻ u, f u ∂Kernel.id p.2.2
    rw [Kernel.id_apply,lintegral_dirac' _ hf]
  | succ n ih =>
    rw [historyKernel_succ_lintegral n p (f := fun z => f z.2) (hf.comp measurable_snd)]
    have hpow : uniformizedKernel^(n+1) = (uniformizedKernel^n) ∘ₖ uniformizedKernel := by
      simpa only [pow_one] using Kernel.pow_add uniformizedKernel n 1
    calc
      (∫⁻ s in Ioc 0 p.1, ∫⁻ u, ∫⁻ z, f z.2 ∂historyKernel n (advanceState p s u)
          ∂uniformizedKernel p.2.2) =
        ∫⁻ s in Ioc 0 p.1, simplexTime n (p.1-s) *
          ∫⁻ u, ∫⁻ w, f w ∂(uniformizedKernel^n) u ∂uniformizedKernel p.2.2 := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        simp_rw [ih _ (show 0 ≤ (advanceState p s _).1 from sub_nonneg.mpr hs.2)]
        exact lintegral_const_mul' _ _ (simplexTime_ne_top _ _)
      _ = (∫⁻ s in Ioc 0 p.1, simplexTime n (p.1-s)) *
          ∫⁻ u, f u ∂(uniformizedKernel^(n+1)) p.2.2 := by
        rw [hpow,Kernel.lintegral_comp _ _ _ hf]
        exact lintegral_mul_const _ (by unfold simplexTime; fun_prop)
      _ = _ := by rw [simplexTime_integral n hT]

theorem historyKernel_mass (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    historyKernel n p univ = simplexTime n p.1 := by
  have h := historyKernel_velocity_lintegral n p hT (measurable_const (a := (1 : ℝ≥0∞)))
  simpa only [lintegral_const,one_mul,measure_univ,mul_one] using h

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The actual free-flight law with a fixed Poisson collision rate -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightWeight_simplexTime (rate T : ℝ≥0) (n : ℕ) :
    flightWeight rate T n * simplexTime n T = poissonMeasure (rate*T) {n} := by
  rw [flightWeight,simplexTime,← ENNReal.ofReal_mul (by positivity),poissonMeasure_singleton]
  congr 1
  simp only [NNReal.coe_mul,neg_mul,mul_pow]
  ring

theorem flightKernel_apply (rate T : ℝ≥0) (z : FlightState) :
    flightKernel rate T z =
      Measure.sum (fun n => flightWeight rate T n • historyKernel n ((T : ℝ),z)) := by
  rw [flightKernel,Kernel.sum_apply]
  congr 1
  funext n
  rw [Kernel.withDensity_apply _ measurable_const,withDensity_const,Kernel.comap_apply]

theorem flightKernel_velocity_lintegral (rate T : ℝ≥0) (z : FlightState)
    {f : RetainedState → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ w, f w.2 ∂flightKernel rate T z) = ∫⁻ u, f u ∂poissonKernel (rate*T) z.2 := by
  rw [flightKernel_apply,lintegral_sum_measure]
  simp_rw [lintegral_smul_measure,smul_eq_mul]
  simp_rw [historyKernel_velocity_lintegral _ ((T : ℝ),z) T.coe_nonneg hf]
  simp_rw [← mul_assoc,flightWeight_simplexTime]
  rw [poissonKernel_lintegral _ _ hf,poissonMeasure,lintegral_sum_measure]
  congr 1
  funext n
  rw [lintegral_smul_measure,lintegral_dirac,Measure.sum_smul_dirac_singleton,smul_eq_mul]

instance flightKernel_isMarkov (rate T : ℝ≥0) : IsMarkovKernel (flightKernel rate T) := by
  constructor
  intro z
  constructor
  have h := flightKernel_velocity_lintegral rate T z (measurable_const (a := (1 : ℝ≥0∞)))
  simpa only [lintegral_const,one_mul,measure_univ] using h

theorem flightKernel_velocity_map (rate T : ℝ≥0) (z : FlightState) :
    (flightKernel rate T z).map Prod.snd = poissonKernel (rate*T) z.2 := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_snd hA]
  have h := flightKernel_velocity_lintegral rate T z
    (f := A.indicator 1) (measurable_const.indicator hA)
  change (∫⁻ w, (Prod.snd ⁻¹' A).indicator 1 w ∂flightKernel rate T z) =
    ∫⁻ u, A.indicator 1 u ∂poissonKernel (rate*T) z.2 at h
  rw [lintegral_indicator_one (measurable_snd hA),lintegral_indicator_one hA] at h
  exact h

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Jointly measurable flight laws with remaining time as a kernel input -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem realFlightWeight_measurable (rate : ℝ≥0) (n : ℕ) :
    Measurable (Function.uncurry (fun (p : TimeFlightState) (_ : FlightState) => realFlightWeight rate n p.1)) := by
  unfold realFlightWeight
  fun_prop

theorem flightFamily_apply (rate : ℝ≥0) (p : TimeFlightState) :
    flightFamily rate p = Measure.sum (fun n => realFlightWeight rate n p.1 • historyKernel n p) := by
  rw [flightFamily,Kernel.sum_apply]
  congr 1
  funext n
  rw [Kernel.withDensity_apply _ (realFlightWeight_measurable rate n),withDensity_const]

theorem flightFamily_eq (rate T : ℝ≥0) (z : FlightState) :
    flightFamily rate ((T : ℝ),z) = flightKernel rate T z := by
  rw [flightFamily_apply,flightKernel_apply]
  rfl

theorem flightFamily_lintegral (rate : ℝ≥0) (p : TimeFlightState) (f : FlightState → ℝ≥0∞) :
    (∫⁻ z, f z ∂flightFamily rate p) =
      ∑' n, realFlightWeight rate n p.1 * ∫⁻ z, f z ∂historyKernel n p := by
  rw [flightFamily_apply,lintegral_sum_measure]
  simp only [lintegral_smul_measure,smul_eq_mul]

theorem realFlightWeight_succ (rate : ℝ≥0) (n : ℕ) (T s : ℝ) :
    realFlightWeight rate (n+1) T = ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s)) *
      realFlightWeight rate n (T-s) := by
  unfold realFlightWeight
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have he : Real.exp (-(rate : ℝ)*s)*Real.exp (-(rate : ℝ)*(T-s)) =
      Real.exp (-(rate : ℝ)*T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [pow_succ]
  calc
    _ = (rate : ℝ)*((Real.exp (-(rate : ℝ)*s)*Real.exp (-(rate : ℝ)*(T-s)))*(rate : ℝ)^n) := by
      rw [he]
      ring
    _ = _ := by ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The first-event renewal identity for the actual reference flight law -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weighted_history_succ_lintegral (rate : ℝ≥0) (n : ℕ) (p : TimeFlightState)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) :
    realFlightWeight rate (n+1) p.1 * (∫⁻ z, f z ∂historyKernel (n+1) p) =
      ∫⁻ s in Ioc 0 p.1, ∫⁻ u,
        ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s)) *
          (realFlightWeight rate n (p.1-s) * ∫⁻ z, f z ∂historyKernel n (advanceState p s u))
        ∂uniformizedKernel p.2.2 := by
  have hw : realFlightWeight rate (n+1) p.1 ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [historyKernel_succ_lintegral n p hf,← lintegral_const_mul' _ _ hw]
  apply lintegral_congr
  intro s
  rw [← lintegral_const_mul' _ _ hw]
  apply lintegral_congr
  intro u
  rw [realFlightWeight_succ,mul_assoc]

theorem flightFamily_first_event (rate : ℝ≥0) (p : TimeFlightState)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂flightFamily rate p) =
      ENNReal.ofReal (Real.exp (-(rate : ℝ)*p.1))*f (finishFlight p) +
      ∫⁻ s in Ioc 0 p.1, ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s)) *
        ∫⁻ u, ∫⁻ z, f z ∂flightFamily rate (advanceState p s u) ∂uniformizedKernel p.2.2 := by
  let a : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s))
  have ha : Measurable a := by dsimp [a]; fun_prop
  have hadv : Measurable (fun q : ℝ × RetainedState => advanceState p q.1 q.2) := by
    unfold advanceState freeFlight
    fun_prop
  have hb (n : ℕ) : Measurable (fun q : ℝ × RetainedState => a q.1 *
      (realFlightWeight rate n (p.1-q.1) * ∫⁻ z, f z ∂historyKernel n (advanceState p q.1 q.2))) := by
    apply (ha.comp measurable_fst).mul
    apply Measurable.mul
    · unfold realFlightWeight
      fun_prop
    · exact (hf.lintegral_kernel (κ := historyKernel n)).comp hadv
  rw [flightFamily_lintegral,tsum_eq_zero_add' ENNReal.summable]
  congr 1
  · rw [historyKernel_zero,Kernel.deterministic_apply,lintegral_dirac' _ hf]
    simp [realFlightWeight]
  · simp_rw [weighted_history_succ_lintegral rate _ p hf]
    change (∑' n, ∫⁻ s in Ioc 0 p.1, ∫⁻ u, a s *
      (realFlightWeight rate n (p.1-s) * ∫⁻ z, f z ∂historyKernel n (advanceState p s u))
      ∂uniformizedKernel p.2.2) = _
    rw [← lintegral_tsum (fun n => (hb n).lintegral_prod_right'.aemeasurable)]
    apply lintegral_congr
    intro s
    have hs (n : ℕ) : Measurable (fun u : RetainedState => a s *
        (realFlightWeight rate n (p.1-s) * ∫⁻ z, f z ∂historyKernel n (advanceState p s u))) :=
      (hb n).comp (measurable_const.prodMk measurable_id)
    change (∑' n, ∫⁻ u, a s *
      (realFlightWeight rate n (p.1-s) * ∫⁻ z, f z ∂historyKernel n (advanceState p s u))
      ∂uniformizedKernel p.2.2) = _
    rw [← lintegral_tsum (fun n => (hs n).aemeasurable)]
    simp_rw [ENNReal.tsum_mul_left]
    have hi (u : RetainedState) :
        (∑' n, realFlightWeight rate n (p.1-s) *
          ∫⁻ z, f z ∂historyKernel n (advanceState p s u)) =
          ∫⁻ z, f z ∂flightFamily rate (advanceState p s u) :=
      (flightFamily_lintegral rate (advanceState p s u) f).symm
    simp_rw [hi]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The exponential first-event kernel on remaining-time flight states -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem renewalDensity_measurable (rate : ℝ≥0) : Measurable (Function.uncurry (renewalDensity rate)) := by
  unfold renewalDensity
  fun_prop

theorem renewalStep_lintegral (rate : ℝ≥0) (p : TimeFlightState)
    {F : TimeFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂renewalStep rate p) =
      ∫⁻ s in Ioc 0 p.1, ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s))*
        ∫⁻ u, F (advanceState p s u) ∂uniformizedKernel p.2.2 := by
  rw [renewalStep,Kernel.lintegral_withDensity _ (renewalDensity_measurable rate) _ hF,
    historyStep_lintegral p]
  · apply lintegral_congr
    intro s
    have he (u : RetainedState) : renewalDensity rate p (advanceState p s u) =
        ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s)) := by
      simp only [renewalDensity,advanceState,sub_sub_cancel]
    simp_rw [he]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · exact ((renewalDensity_measurable rate).comp (measurable_const.prodMk measurable_id)).mul hF

theorem renewalStep_le (rate : ℝ≥0) (p : TimeFlightState) :
    renewalStep rate p ≤ ENNReal.ofReal (rate : ℝ) • historyStep p := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [← lintegral_indicator_one hA,renewalStep_lintegral rate p (F := A.indicator 1) (measurable_const.indicator hA),
    Measure.smul_apply,smul_eq_mul,← lintegral_indicator_one hA,
    historyStep_lintegral p (f := A.indicator 1) (measurable_const.indicator hA),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_of_le_one_right rate.coe_nonneg
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr rate.coe_nonneg) hs.1.le))

theorem flightFamily_renewal (rate : ℝ≥0) (p : TimeFlightState)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂flightFamily rate p) =
      ENNReal.ofReal (Real.exp (-(rate : ℝ)*p.1))*f (finishFlight p) +
        ∫⁻ q, ∫⁻ z, f z ∂flightFamily rate q ∂renewalStep rate p := by
  rw [renewalStep_lintegral rate p (hf.lintegral_kernel)]
  exact flightFamily_first_event rate p hf

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Factorial remainder bounds for the actual first-event kernel -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem renewalStep_power_le (rate : ℝ≥0) (n : ℕ) (p : TimeFlightState) :
    ((renewalStep rate)^n) p ≤ (ENNReal.ofReal (rate : ℝ))^n • (historyStep^n) p := by
  induction n generalizing p with
  | zero => simp only [pow_zero,one_smul]; exact le_rfl
  | succ n ih =>
    have hh : ((renewalStep rate)^(n+1)) = (((renewalStep rate)^n)) ∘ₖ renewalStep rate := by
      simpa only [pow_one] using Kernel.pow_add (renewalStep rate) n 1
    have hg : historyStep^(n+1) = (historyStep^n) ∘ₖ historyStep := by
      simpa only [pow_one] using Kernel.pow_add historyStep n 1
    apply Measure.le_iff.mpr
    intro A hA
    rw [hh,hg,Kernel.comp_apply' _ _ _ hA,Measure.smul_apply,smul_eq_mul,
      Kernel.comp_apply' _ _ _ hA]
    calc
      _ ≤ ∫⁻ q, (ENNReal.ofReal (rate : ℝ))^n * (historyStep^n) q A
          ∂(ENNReal.ofReal (rate : ℝ) • historyStep p) := by
        apply lintegral_mono' (renewalStep_le rate p)
        intro q
        exact ih q A
      _ = _ := by
        rw [lintegral_smul_measure,lintegral_const_mul' _ _
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),pow_succ]
        simp only [smul_eq_mul]
        ac_rfl

theorem historyStep_power_mass (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    (historyStep^n) p univ = simplexTime n p.1 := by
  have hh := historyKernel_mass n p hT
  rw [historyKernel,Kernel.map_apply' _ finishFlight_measurable _ MeasurableSet.univ,preimage_univ] at hh
  exact hh

theorem renewalStep_power_mass_bound (rate : ℝ≥0) (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    ((renewalStep rate)^n) p univ ≤ ENNReal.ofReal (((rate : ℝ)*p.1)^n/(n.factorial : ℝ)) := by
  have hh := renewalStep_power_le rate n p univ
  rw [Measure.smul_apply,smul_eq_mul,historyStep_power_mass n p hT,simplexTime,
    ← ENNReal.ofReal_pow rate.coe_nonneg,← ENNReal.ofReal_mul (by positivity)] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [mul_pow]
  congr 1
  ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # First-event iterations stay inside the initial time interval -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historyStep_time_support (p : TimeFlightState) (_hT : 0 ≤ p.1) :
    ∀ᵐ q ∂historyStep p, q.1 ∈ Icc 0 p.1 := by
  let A : Set TimeFlightState := {q | q.1 ∉ Icc 0 p.1}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  change historyStep p A = 0
  rw [← lintegral_indicator_one hA,historyStep_lintegral p (f := A.indicator 1)
    (measurable_const.indicator hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply lintegral_eq_zero_of_ae_eq_zero
  apply ae_of_all
  intro u
  have hq : (advanceState p s u).1 ∈ Icc 0 p.1 :=
    ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1.le⟩
  exact indicator_of_notMem (show advanceState p s u ∉ A from not_not.mpr hq) 1

theorem renewalStep_time_support (rate : ℝ≥0) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    ∀ᵐ q ∂renewalStep rate p, q.1 ∈ Icc 0 p.1 :=
  (Measure.absolutelyContinuous_of_le_smul (renewalStep_le rate p)).ae_le (historyStep_time_support p hT)

theorem renewalStep_power_time_support (rate : ℝ≥0) (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    ∀ᵐ q ∂((renewalStep rate)^n) p, q.1 ∈ Icc 0 p.1 := by
  induction n generalizing p with
  | zero =>
    have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
    rw [pow_zero,hi,Kernel.id_apply,ae_dirac_iff (by measurability)]
    exact ⟨hT,le_rfl⟩
  | succ n ih =>
    rw [show ((renewalStep rate)^(n+1)) = (((renewalStep rate)^n)) ∘ₖ renewalStep rate by
      simpa only [pow_one] using Kernel.pow_add (renewalStep rate) n 1]
    apply Kernel.ae_comp_of_ae_ae (by measurability)
    filter_upwards [renewalStep_time_support rate p hT] with q hq
    filter_upwards [ih q hq.1] with w hw
    exact ⟨hw.1,hw.2.trans hq.2⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceBranchingHistories
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Splitting and translating the first-event time integral -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lintegral_time_split (f : ℝ → ℝ≥0∞) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫⁻ r in Ioc 0 (s+t), f r) =
      (∫⁻ r in Ioc 0 s, f r) + ∫⁻ r in Ioc s (s+t), f r := by
  rw [← Ioc_union_Ioc_eq_Ioc hs (by linarith)]
  apply lintegral_union
  · exact measurableSet_Ioc
  · apply disjoint_left.mpr
    intro r hr hs'
    exact (not_lt_of_ge hr.2) hs'.1

theorem lintegral_time_shift (f : ℝ → ℝ≥0∞) (s t : ℝ) :
    (∫⁻ r in Ioc s (s+t), f r) = ∫⁻ r in Ioc 0 t, f (s+r) := by
  classical
  rw [← lintegral_indicator measurableSet_Ioc,← lintegral_indicator measurableSet_Ioc]
  calc
    _ = ∫⁻ r : ℝ, (Ioc s (s+t)).indicator f (s+r) :=
      (lintegral_add_left_eq_self ((Ioc s (s+t)).indicator f) s).symm
    _ = _ := by
      apply lintegral_congr
      intro r
      have hh : s+r ∈ Ioc s (s+t) ↔ r ∈ Ioc 0 t := by
        constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
      simp only [indicator_apply,hh]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

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

theorem clockDensity_add (rate : ℝ≥0) (s t : ℝ) :
    clockDensity rate (s+t) = clockSurvival rate s*clockDensity rate t := by
  rw [clockDensity,clockSurvival,clockDensity,← ENNReal.ofReal_mul (by positivity)]
  have he : Real.exp (-(rate : ℝ)*(s+t)) =
      Real.exp (-(rate : ℝ)*s)*Real.exp (-(rate : ℝ)*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  congr 1
  ring

theorem advanceState_time_cut (z : FlightState) (s t r : ℝ) (u : RetainedState) :
    advanceState (s+t,z) (s+r) u = advanceState (t,freeFlight s z) r u := by
  ext1
  · dsimp [advanceState]
    ring
  · ext1
    · simp only [advanceState,freeFlight]
      module
    · rfl

theorem finishFlight_time_cut (z : FlightState) (s t : ℝ) :
    finishFlight (s+t,z) = finishFlight (t,freeFlight s z) := by
  ext1
  · simp only [finishFlight,freeFlight]
    module
  · rfl

theorem first_event_tail (rate : ℝ≥0) (z : FlightState) (s t : ℝ)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) :
    clockSurvival rate (s+t)*f (finishFlight (s+t,z)) +
      (∫⁻ r in Ioc s (s+t), clockDensity rate r *
        ∫⁻ u, ∫⁻ w, f w ∂flightFamily rate (advanceState (s+t,z) r u) ∂uniformizedKernel z.2) =
      clockSurvival rate s * ∫⁻ w, f w ∂flightFamily rate (t,freeFlight s z) := by
  rw [flightFamily_first_event rate (t,freeFlight s z) hf,mul_add]
  change _ = clockSurvival rate s*(clockSurvival rate t*f (finishFlight (t,freeFlight s z))) +
    clockSurvival rate s*(∫⁻ r in Ioc 0 t, clockDensity rate r *
      ∫⁻ u, ∫⁻ w, f w ∂flightFamily rate (advanceState (t,freeFlight s z) r u)
        ∂uniformizedKernel z.2)
  congr 1
  · rw [clockSurvival_add,finishFlight_time_cut,mul_assoc]
  · rw [lintegral_time_shift]
    simp_rw [clockDensity_add,advanceState_time_cut,mul_assoc]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem flightFamily_time_cut (rate : ℝ≥0) (z : FlightState) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) {f : FlightState → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ w, f w ∂flightFamily rate (s+t,z)) =
      clockSurvival rate s * (∫⁻ w, f w ∂flightFamily rate (t,freeFlight s z)) +
        ∫⁻ r in Ioc 0 s, clockDensity rate r *
          ∫⁻ u, ∫⁻ w, f w ∂flightFamily rate (advanceState (s+t,z) r u) ∂uniformizedKernel z.2 := by
  rw [flightFamily_first_event rate (s+t,z) hf]
  change clockSurvival rate (s+t)*f (finishFlight (s+t,z)) +
    (∫⁻ r in Ioc 0 (s+t), clockDensity rate r *
      ∫⁻ u, ∫⁻ w, f w ∂flightFamily rate (advanceState (s+t,z) r u) ∂uniformizedKernel z.2) = _
  rw [lintegral_time_split _ hs ht]
  rw [show ∀ a b c : ℝ≥0∞, a+(b+c) = (a+c)+b from fun a b c => by ac_rfl]
  rw [first_event_tail rate z s t hf]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive Fubini on the ordered two-event time triangle -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lintegral_time_triangle {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) (T : ℝ) :
    (∫⁻ s in Ioc 0 T, ∫⁻ r in Ioc 0 s, f (s,r)) =
      ∫⁻ r in Ioc 0 T, ∫⁻ s in Icc r T, f (s,r) := by
  classical
  let D : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}
  have hD : MeasurableSet D := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const))
  have hleft : (∫⁻ s in Ioc 0 T, ∫⁻ r in Ioc 0 s, f (s,r)) =
      ∫⁻ s : ℝ, ∫⁻ r : ℝ, D.indicator f (s,r) := by
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ Ioc 0 T
    · rw [indicator_of_mem hs,← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro r
      have he : (s,r) ∈ D ↔ r ∈ Ioc 0 s := by
        simp only [D,mem_ofPred_eq,mem_Ioc]
        exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,hs.2⟩⟩
      simp only [indicator_apply,he]
    · rw [indicator_of_notMem hs]
      symm
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with r
      apply indicator_of_notMem
      intro hr
      exact hs ⟨hr.1.trans_le hr.2.1,hr.2.2⟩
  have hright : (∫⁻ r in Ioc 0 T, ∫⁻ s in Icc r T, f (s,r)) =
      ∫⁻ r : ℝ, ∫⁻ s : ℝ, D.indicator f (s,r) := by
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro r
    by_cases hr : r ∈ Ioc 0 T
    · rw [indicator_of_mem hr,← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro s
      have he : (s,r) ∈ D ↔ s ∈ Icc r T := by
        simp only [D,mem_ofPred_eq,mem_Icc]
        exact ⟨fun h => h.2,fun h => ⟨hr.1,h⟩⟩
      simp only [indicator_apply,he]
    · rw [indicator_of_notMem hr]
      symm
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with s
      apply indicator_of_notMem
      intro hs
      exact hr ⟨hs.1,hs.2.1.trans hs.2.2⟩
  rw [hleft,hright]
  exact lintegral_lintegral_swap (hf.indicator hD).aemeasurable

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniqueness of bounded solutions of the reference first-event equation -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem renewal_solution_comparison (rate : ℝ≥0) {T B : ℝ} (hB : 0 ≤ B)
    {F G D : TimeFlightState → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (hFb : ∀ p, p.1 ∈ Icc 0 T → F p ≤ ENNReal.ofReal B)
    (hFeq : ∀ p, p.1 ∈ Icc 0 T → F p = D p + ∫⁻ q, F q ∂renewalStep rate p)
    (hGeq : ∀ p, p.1 ∈ Icc 0 T → G p = D p + ∫⁻ q, G q ∂renewalStep rate p)
    (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) : F p ≤ G p := by
  have hfinite (n : ℕ) : ∀ p : TimeFlightState, p.1 ∈ Icc 0 T →
      F p ≤ G p + ∫⁻ q, F q ∂((renewalStep rate)^n) p := by
    induction n with
    | zero =>
      intro q hq
      have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
      rw [pow_zero,hi,Kernel.id_apply,lintegral_dirac]
      exact le_add_left le_rfl
    | succ n ih =>
      intro q hq
      have hmon : (∫⁻ w, F w ∂renewalStep rate q) ≤
          ∫⁻ w, (G w + ∫⁻ v, F v ∂((renewalStep rate)^n) w) ∂renewalStep rate q := by
        apply lintegral_mono_ae
        filter_upwards [renewalStep_time_support rate q hq.1] with w hw
        exact ih w ⟨hw.1,hw.2.trans hq.2⟩
      have hpow : ((renewalStep rate)^(n+1)) = (((renewalStep rate)^n)) ∘ₖ renewalStep rate := by
        simpa only [pow_one] using Kernel.pow_add (renewalStep rate) n 1
      calc
        F q = D q + ∫⁻ w, F w ∂renewalStep rate q := hFeq q hq
        _ ≤ D q + ∫⁻ w, (G w + ∫⁻ v, F v ∂((renewalStep rate)^n) w) ∂renewalStep rate q :=
          add_le_add le_rfl hmon
        _ = G q + ∫⁻ v, F v ∂((renewalStep rate)^(n+1)) q := by
          rw [lintegral_add_left hG,hpow,Kernel.lintegral_comp _ _ _ hF,
            ← add_assoc,← hGeq q hq]
  have hr (n : ℕ) : (∫⁻ q, F q ∂((renewalStep rate)^n) p) ≤
      ENNReal.ofReal (B*(((rate : ℝ)*p.1)^n/(n.factorial : ℝ))) := by
    calc
      _ ≤ ∫⁻ _q, ENNReal.ofReal B ∂((renewalStep rate)^n) p := by
        apply lintegral_mono_ae
        filter_upwards [renewalStep_power_time_support rate n p hp.1] with q hq
        exact hFb q ⟨hq.1,hq.2.trans hp.2⟩
      _ = ENNReal.ofReal B * ((renewalStep rate)^n) p univ := lintegral_const _
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal (((rate : ℝ)*p.1)^n/(n.factorial : ℝ)) := by
        gcongr
        exact renewalStep_power_mass_bound rate n p hp.1
      _ = _ := (ENNReal.ofReal_mul hB).symm
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (B*(((rate : ℝ)*p.1)^n/(n.factorial : ℝ))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((FloorSemiring.tendsto_pow_div_factorial_atTop ((rate : ℝ)*p.1)).const_mul B)
  have hlim : Tendsto (fun n : ℕ => G p +
      ENNReal.ofReal (B*(((rate : ℝ)*p.1)^n/(n.factorial : ℝ)))) atTop (𝓝 (G p)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := G p)).add ht
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    (fun n => (hfinite n p hp).trans (add_le_add le_rfl (hr n)))

theorem renewal_solution_unique (rate : ℝ≥0) {T B : ℝ} (hB : 0 ≤ B)
    {F G D : TimeFlightState → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (hFb : ∀ p, p.1 ∈ Icc 0 T → F p ≤ ENNReal.ofReal B)
    (hGb : ∀ p, p.1 ∈ Icc 0 T → G p ≤ ENNReal.ofReal B)
    (hFeq : ∀ p, p.1 ∈ Icc 0 T → F p = D p + ∫⁻ q, F q ∂renewalStep rate p)
    (hGeq : ∀ p, p.1 ∈ Icc 0 T → G p = D p + ∫⁻ q, G q ∂renewalStep rate p)
    (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) : F p = G p :=
  le_antisymm (renewal_solution_comparison rate hB hF hG hFb hFeq hGeq p hp)
    (renewal_solution_comparison rate hB hG hF hGb hGeq hFeq p hp)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Chapman–Kolmogorov for the actual space-and-velocity flight law -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightFamily_average_bound (rate : ℝ≥0) (p : TimeFlightState) (hp : 0 ≤ p.1)
    {f : FlightState → ℝ≥0∞} {B : ℝ≥0∞} (hb : ∀ z, f z ≤ B) :
    (∫⁻ z, f z ∂flightFamily rate p) ≤ B := by
  have he : flightFamily rate p = flightKernel rate ⟨p.1,hp⟩ p.2 :=
    flightFamily_eq rate ⟨p.1,hp⟩ p.2
  rw [he]
  calc
    _ ≤ ∫⁻ _z, B ∂flightKernel rate ⟨p.1,hp⟩ p.2 := lintegral_mono hb
    _ = B := by
      have hm := (flightKernel_isMarkov rate ⟨p.1,hp⟩).isProbabilityMeasure p.2
      rw [lintegral_const,hm.measure_univ,mul_one]

theorem advanceState_add_remaining (p : TimeFlightState) (t r : ℝ) (u : RetainedState) :
    advanceState (p.1+t,p.2) r u =
      ((advanceState p r u).1+t,(advanceState p r u).2) := by
  ext1
  · simp only [advanceState]
    ring
  · rfl

theorem flightFamily_add_average (rate : ℝ≥0) {t : ℝ} (ht : 0 ≤ t)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) (hb : ∀ z, f z ≤ 1)
    (p : TimeFlightState) (hp : 0 ≤ p.1) :
    (∫⁻ w, f w ∂flightFamily rate (p.1+t,p.2)) =
      ∫⁻ z, ∫⁻ w, f w ∂flightFamily rate (t,z) ∂flightFamily rate p := by
  let F : TimeFlightState → ℝ≥0∞ := fun q => ∫⁻ w, f w ∂flightFamily rate (q.1+t,q.2)
  let g : FlightState → ℝ≥0∞ := fun z => ∫⁻ w, f w ∂flightFamily rate (t,z)
  let G : TimeFlightState → ℝ≥0∞ := fun q => ∫⁻ z, g z ∂flightFamily rate q
  let D : TimeFlightState → ℝ≥0∞ := fun q => clockSurvival rate q.1*g (finishFlight q)
  have hF : Measurable F := (hf.lintegral_kernel (κ := flightFamily rate)).comp (by fun_prop)
  have hg : Measurable g := (hf.lintegral_kernel (κ := flightFamily rate)).comp
    (measurable_const.prodMk measurable_id)
  have hG : Measurable G := hg.lintegral_kernel
  have hFb (q : TimeFlightState) (hq : q.1 ∈ Icc 0 p.1) : F q ≤ ENNReal.ofReal 1 := by
    simpa only [ENNReal.ofReal_one] using
      flightFamily_average_bound rate (q.1+t,q.2) (add_nonneg hq.1 ht) hb
  have hgb (z : FlightState) : g z ≤ 1 := flightFamily_average_bound rate (t,z) ht hb
  have hGb (q : TimeFlightState) (hq : q.1 ∈ Icc 0 p.1) : G q ≤ ENNReal.ofReal 1 := by
    simpa only [ENNReal.ofReal_one] using flightFamily_average_bound rate q hq.1 hgb
  have hFeq (q : TimeFlightState) (hq : q.1 ∈ Icc 0 p.1) :
      F q = D q + ∫⁻ w, F w ∂renewalStep rate q := by
    rw [renewalStep_lintegral rate q hF]
    have hc := flightFamily_time_cut rate q.2 hq.1 ht hf
    simp_rw [advanceState_add_remaining] at hc
    exact hc
  have hGeq (q : TimeFlightState) (_hq : q.1 ∈ Icc 0 p.1) :
      G q = D q + ∫⁻ w, G w ∂renewalStep rate q :=
    flightFamily_renewal rate q hg
  exact renewal_solution_unique rate (by norm_num : (0:ℝ) ≤ 1) hF hG hFb hGb hFeq hGeq p ⟨hp,le_rfl⟩

theorem flightKernel_add (rate s t : ℝ≥0) :
    flightKernel rate (s+t) = flightKernel rate t ∘ₖ flightKernel rate s := by
  ext z A hA
  have hi : Measurable (A.indicator (1 : FlightState → ℝ≥0∞)) := measurable_const.indicator hA
  have hb (w : FlightState) : A.indicator (1 : FlightState → ℝ≥0∞) w ≤ 1 := by
    by_cases h : w ∈ A <;> simp [h]
  have hh := flightFamily_add_average rate t.coe_nonneg hi hb ((s : ℝ),z) s.coe_nonneg
  simp only [flightFamily_eq,lintegral_indicator_one hA] at hh
  have he := flightFamily_eq rate (s+t) z
  simp only [NNReal.coe_add] at he
  rw [he] at hh
  rw [Kernel.comp_apply' _ _ _ hA]
  exact hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The scalar exponential factor in the reference branching equation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem growthWeight_measurable (c : ℝ) : Measurable (growthWeight c) := by
  unfold growthWeight
  fun_prop

theorem growthDensity_measurable (c T : ℝ) : Measurable (growthDensity c T) := by
  unfold growthDensity
  fun_prop

theorem growthDensity_integral {c r T : ℝ} (hc : 0 ≤ c) (hr : r ≤ T) :
    (∫⁻ s in Icc r T, growthDensity c T s) = growthWeight c (T-r)-1 := by
  let f : ℝ → ℝ := fun s => c*Real.exp (c*(T-s))
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have hi : IntegrableOn f (Ioc r T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mp (hcont.intervalIntegrable _ _)
  have hd (s : ℝ) : HasDerivAt (fun x : ℝ => -Real.exp (c*(T-x))) (f s) s := by
    refine ((((hasDerivAt_const s T).sub (hasDerivAt_id s)).const_mul c).exp.neg).congr_deriv ?_
    dsimp [f]
    ring
  have he : (∫ s in r..T, f s) = Real.exp (c*(T-r))-1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hcont.intervalIntegrable _ _)]
    simp only [sub_self,mul_zero,Real.exp_zero]
    ring
  rw [← restrict_Ioc_eq_restrict_Icc]
  change (∫⁻ s in Ioc r T, ENNReal.ofReal (f s)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun s => mul_nonneg hc (Real.exp_pos _).le)),
    ← intervalIntegral.integral_of_le hr,he]
  simpa only [growthWeight,ENNReal.ofReal_one] using
    ENNReal.ofReal_sub (Real.exp (c*(T-r))) (by norm_num : (0:ℝ) ≤ 1)

theorem growthWeight_split {c r T : ℝ} (hc : 0 ≤ c) (hr : r ≤ T) :
    growthWeight c (T-r) = 1+∫⁻ s in Icc r T, growthDensity c T s := by
  rw [growthDensity_integral hc hr,add_comm,tsub_add_cancel_of_le]
  simpa only [growthWeight,ENNReal.ofReal_one] using
    ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hc (sub_nonneg.mpr hr)))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exponential weighting of a positive first-event time-cut identity -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weighted_time_cut {c T : ℝ} (hc : 0 ≤ c) (hT : 0 ≤ T)
    {P D : ℝ≥0∞} {A B : ℝ → ℝ≥0∞} (hA : Measurable A) (hB : Measurable B)
    (hcut : ∀ s ∈ Ioc 0 T, P = A s + ∫⁻ r in Ioc 0 s, B r)
    (htop : P = D + ∫⁻ r in Ioc 0 T, B r) :
    growthWeight c T * P = D +
      (∫⁻ r in Ioc 0 T, growthWeight c (T-r)*B r) +
      ∫⁻ s in Ioc 0 T, growthDensity c T s*A s := by
  let J : ℝ≥0∞ := ∫⁻ s in Ioc 0 T, growthDensity c T s * ∫⁻ r in Ioc 0 s, B r
  have hJ : J = ∫⁻ r in Ioc 0 T,
      (∫⁻ s in Icc r T, growthDensity c T s)*B r := by
    unfold J
    have hp (s : ℝ) : growthDensity c T s * (∫⁻ r in Ioc 0 s, B r) =
        ∫⁻ r in Ioc 0 s, growthDensity c T s*B r :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    simp_rw [hp]
    have hm : Measurable (fun p : ℝ × ℝ => growthDensity c T p.1*B p.2) :=
      ((growthDensity_measurable c T).comp measurable_fst).mul (hB.comp measurable_snd)
    rw [lintegral_time_triangle hm T]
    apply lintegral_congr
    intro r
    simpa only using! lintegral_mul_const (μ := volume.restrict (Icc r T))
      (B r) (growthDensity_measurable c T)
  have hsum : (∫⁻ r in Ioc 0 T, B r) + J =
      ∫⁻ r in Ioc 0 T, growthWeight c (T-r)*B r := by
    rw [hJ,← lintegral_add_left hB]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [growthWeight_split hc hr.2,add_mul,one_mul]
  have hi : (∫⁻ s in Ioc 0 T, growthDensity c T s*P) =
      (∫⁻ s in Ioc 0 T, growthDensity c T s*A s) + J := by
    calc
      _ = ∫⁻ s in Ioc 0 T, growthDensity c T s*(A s+∫⁻ r in Ioc 0 s, B r) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        rw [← hcut s hs]
      _ = _ := by
        simp_rw [mul_add]
        exact lintegral_add_left ((growthDensity_measurable c T).mul hA) _
  have hscalar : growthWeight c T = 1+∫⁻ s in Ioc 0 T, growthDensity c T s := by
    simpa only [sub_zero,← restrict_Ioc_eq_restrict_Icc] using growthWeight_split hc hT
  calc
    growthWeight c T*P = P+∫⁻ s in Ioc 0 T, growthDensity c T s*P := by
      rw [hscalar,add_mul,one_mul,lintegral_mul_const _ (growthDensity_measurable c T)]
    _ = D+(∫⁻ r in Ioc 0 T, B r)+((∫⁻ s in Ioc 0 T, growthDensity c T s*A s)+J) := by
      rw [hi,htop]
    _ = D+((∫⁻ r in Ioc 0 T, B r)+J)+(∫⁻ s in Ioc 0 T, growthDensity c T s*A s) := by ac_rfl
    _ = _ := by rw [hsum]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The reference flight with a constant positive branching potential -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weightedFlight_measurable (rate : ℝ≥0) (c : ℝ)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) : Measurable (weightedFlight rate c f) :=
  ((growthWeight_measurable c).comp measurable_fst).mul (hf.lintegral_kernel)

theorem clockDensity_eq (rate : ℝ≥0) (s : ℝ) :
    clockDensity rate s = clockSurvival rate s * ENNReal.ofReal rate := by
  rw [clockDensity,clockSurvival,← ENNReal.ofReal_mul (by positivity),mul_comm]

theorem growthDensity_eq {c : ℝ} (hc : 0 ≤ c) (T s : ℝ) :
    growthDensity c T s = ENNReal.ofReal c * growthWeight c (T-s) :=
  ENNReal.ofReal_mul hc

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

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

theorem eventStep_power_mass_bound (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] {C : ℝ} (_hC : 0 ≤ C)
    (hK : ∀ v, K v univ ≤ ENNReal.ofReal C) (n : ℕ) (p : TimeFlightState) (hp : 0 ≤ p.1) :
    ((eventStep rate K)^n) p univ ≤ ENNReal.ofReal C^n * simplexTime n p.1 := by
  induction n generalizing p with
  | zero =>
    have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
    rw [pow_zero,hi,Kernel.id_apply,Measure.dirac_apply_of_mem (mem_univ p),
      simplexTime_zero,pow_zero,one_mul]
  | succ n ih =>
    rw [show (eventStep rate K)^(n+1) = ((eventStep rate K)^n) ∘ₖ eventStep rate K by
      simpa only [pow_one] using Kernel.pow_add (eventStep rate K) n 1,
      Kernel.comp_apply' _ _ _ MeasurableSet.univ,
      eventStep_lintegral rate K p (((eventStep rate K)^n).measurable_coe MeasurableSet.univ)]
    calc
      _ ≤ ∫⁻ s in Ioc 0 p.1, ENNReal.ofReal C^n*simplexTime n (p.1-s)*ENNReal.ofReal C := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        calc
          _ ≤ 1 * (∫⁻ _u, ENNReal.ofReal C^n*simplexTime n (p.1-s) ∂K p.2.2) := by
            apply mul_le_mul' (clockSurvival_le_one rate hs.1.le)
            apply lintegral_mono
            intro u
            exact ih _ (sub_nonneg.mpr hs.2)
          _ ≤ _ := by
            rw [one_mul,lintegral_const]
            exact mul_le_mul' le_rfl (hK _)
      _ = ENNReal.ofReal C^(n+1) * ∫⁻ s in Ioc 0 p.1, simplexTime n (p.1-s) := by
        have he (s : ℝ) : ENNReal.ofReal C^n*simplexTime n (p.1-s)*ENNReal.ofReal C =
            ENNReal.ofReal C^(n+1)*simplexTime n (p.1-s) := by rw [pow_succ]; ac_rfl
        simp_rw [he]
        exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      _ = _ := by rw [simplexTime_integral n hp]

theorem eventStep_time_support (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] (p : TimeFlightState) :
    ∀ᵐ q ∂eventStep rate K p, q.1 ∈ Icc 0 p.1 := by
  let A : Set TimeFlightState := {q | q.1 ∉ Icc 0 p.1}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  change eventStep rate K p A = 0
  rw [← lintegral_indicator_one hA,eventStep_lintegral rate K p
    (F := A.indicator 1) (measurable_const.indicator hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have he : (∫⁻ u, A.indicator 1 (advanceState p s u) ∂K p.2.2) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro u
    have hq : (advanceState p s u).1 ∈ Icc 0 p.1 :=
      ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1.le⟩
    exact indicator_of_notMem (show advanceState p s u ∉ A from not_not.mpr hq) 1
  simp only [he,mul_zero,Pi.zero_apply]

theorem eventStep_power_time_support (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] (n : ℕ) (p : TimeFlightState) (hp : 0 ≤ p.1) :
    ∀ᵐ q ∂((eventStep rate K)^n) p, q.1 ∈ Icc 0 p.1 := by
  induction n generalizing p with
  | zero =>
    have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
    rw [pow_zero,hi,Kernel.id_apply,ae_dirac_iff (by measurability)]
    exact ⟨hp,le_rfl⟩
  | succ n ih =>
    rw [show (eventStep rate K)^(n+1) = ((eventStep rate K)^n) ∘ₖ eventStep rate K by
      simpa only [pow_one] using Kernel.pow_add (eventStep rate K) n 1]
    apply Kernel.ae_comp_of_ae_ae (by measurability)
    filter_upwards [eventStep_time_support rate K p] with q hq
    filter_upwards [ih q hq.1] with w hw
    exact ⟨hw.1,hw.2.trans hq.2⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive finite-history exhaustion for a bounded reference subsolution -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem event_finite_expansion (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] {F D : TimeFlightState → ℝ≥0∞} (hF : Measurable F) (hD : Measurable D)
    {T : ℝ} (hsub : ∀ q, q.1 ∈ Icc 0 T → F q ≤ D q + ∫⁻ w, F w ∂eventStep rate K q)
    (n : ℕ) (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) :
    F p ≤ (∑ j ∈ Finset.range n, eventHistory rate K D j p) +
      ∫⁻ q, F q ∂((eventStep rate K)^n) p := by
  induction n with
  | zero =>
    have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
    rw [Finset.range_zero,Finset.sum_empty,pow_zero,hi,Kernel.id_apply,lintegral_dirac,zero_add]
  | succ n ih =>
    have hr : (∫⁻ q, F q ∂((eventStep rate K)^n) p) ≤ eventHistory rate K D n p +
        ∫⁻ q, F q ∂((eventStep rate K)^(n+1)) p := by
      calc
        _ ≤ ∫⁻ q, (D q + ∫⁻ w, F w ∂eventStep rate K q) ∂((eventStep rate K)^n) p := by
          apply lintegral_mono_ae
          filter_upwards [eventStep_power_time_support rate K n p hp.1] with q hq
          exact hsub q ⟨hq.1,hq.2.trans hp.2⟩
        _ = _ := by
          rw [lintegral_add_left hD]
          have he : (eventStep rate K)^(n+1) = eventStep rate K ∘ₖ ((eventStep rate K)^n) := by
            simpa only [pow_one,Nat.add_comm] using Kernel.pow_add (eventStep rate K) 1 n
          rw [he,Kernel.lintegral_comp _ _ _ hF]
          rfl
    calc
      _ ≤ (∑ j ∈ Finset.range n, eventHistory rate K D j p) +
          (eventHistory rate K D n p + ∫⁻ q, F q ∂((eventStep rate K)^(n+1)) p) :=
        ih.trans (add_le_add le_rfl hr)
      _ = _ := by rw [Finset.sum_range_succ,add_assoc]

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

/-! # Summing the time-simplex second-moment factors -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightWeight_secondMoment_le (rate T : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    flightWeight rate T n * ENNReal.ofReal ((n+1 : ℕ)*simplexVolume (n+2) T) ≤
      ENNReal.ofReal ((T : ℝ)/rate) * poissonMeasure (rate*T) {n+1} := by
  have hr' : 0 < (rate : ℝ) := hr
  have hn : 0 < (n+2 : ℝ) := by positivity
  let R : ℝ := (T : ℝ)/rate *
    (Real.exp (-(rate : ℝ)*T) * ((rate : ℝ)*T)^(n+1)/(n+1).factorial)
  have hR : 0 ≤ R := by dsimp [R] <;> positivity
  have heq : (Real.exp (-(rate : ℝ)*T)*(rate : ℝ)^n)*
      ((n+1 : ℕ)*simplexVolume (n+2) T) = R*((n+1 : ℝ)/(n+2)) := by
    dsimp [R,simplexVolume]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_pow,pow_succ]
    field_simp
    ring
  rw [flightWeight,← ENNReal.ofReal_mul (by positivity),poissonMeasure_singleton,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simp only [NNReal.coe_mul,← neg_mul]
  change _ ≤ R
  rw [heq]
  exact mul_le_of_le_one_right hR ((div_le_one hn).mpr (by linarith))

theorem flightWeight_secondMoment_sum_le (rate T : ℝ≥0) (hr : 0 < rate) :
    (∑' n : ℕ, flightWeight rate T n *
      ENNReal.ofReal ((n+1 : ℕ)*simplexVolume (n+2) T)) ≤ ENNReal.ofReal ((T : ℝ)/rate) := by
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((T : ℝ)/rate)*poissonMeasure (rate*T) {n+1} :=
      ENNReal.tsum_le_tsum (flightWeight_secondMoment_le rate T hr)
    _ = ENNReal.ofReal ((T : ℝ)/rate) * ∑' n : ℕ, poissonMeasure (rate*T) {n+1} :=
      ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal ((T : ℝ)/rate) * ∑' n : ℕ, poissonMeasure (rate*T) {n} := by
      have hs := ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective
        (fun n => poissonMeasure (rate*T) {n})
      exact mul_le_mul le_rfl hs zero_le zero_le
    _ = ENNReal.ofReal ((T : ℝ)/rate) := by
      have hh : (∑' n : ℕ, poissonMeasure (rate*T) {n}) = 1 := by
        simpa only [lintegral_const,one_mul,measure_univ] using
          (lintegral_countable' (μ := poissonMeasure (rate*T)) (fun _ => (1 : ℝ≥0∞))).symm
      rw [hh,mul_one]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceHistoryMoments
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite propagation and integrability for the actual flight histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historyKernel_displacement (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    ∀ᵐ z ∂historyKernel n p, ‖z.1-p.2.1‖ ≤ 5*p.1 := by
  induction n generalizing p with
  | zero =>
    rw [historyKernel_zero,Kernel.deterministic_apply,ae_dirac_iff (by measurability)]
    simpa only [finishFlight,abs_of_nonneg hT] using freeFlight_displacement p.1 p.2
  | succ n ih =>
    let A : Set FlightState := {z | ¬ ‖z.1-p.2.1‖ ≤ 5*p.1}
    have hA : MeasurableSet A := by dsimp [A]; measurability
    change historyKernel (n+1) p A = 0
    rw [← lintegral_indicator_one hA,
      historyKernel_succ_lintegral n p (f := A.indicator 1) (measurable_const.indicator hA)]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro u
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ih (advanceState p s u) (sub_nonneg.mpr hs.2)] with z hz
    have hb : ‖z.1-p.2.1‖ ≤ 5*p.1 := by
      calc
        ‖z.1-p.2.1‖ ≤ ‖z.1-(advanceState p s u).2.1‖ +
            ‖(advanceState p s u).2.1-p.2.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 5*(p.1-s)+5*s := by
          exact add_le_add hz (by simpa only [advanceState,abs_of_pos hs.1] using
            freeFlight_displacement s p.2)
        _ = _ := by ring
    exact indicator_of_notMem (show z ∉ A from not_not.mpr hb) 1

theorem historyKernel_isFinite (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    IsFiniteMeasure (historyKernel n p) := by
  constructor
  rw [historyKernel_mass n p hT]
  exact (simplexTime_ne_top n p.1).lt_top

theorem history_displacement_integrable (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    Integrable (fun z : FlightState => z.1-p.2.1) (historyKernel n p) := by
  let _ := historyKernel_isFinite n p hT
  exact (integrable_const (5*p.1)).mono' (by fun_prop) (historyKernel_displacement n p hT)

theorem history_displacement_sq_integrable (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    Integrable (fun z : FlightState => ‖z.1-p.2.1‖^2) (historyKernel n p) := by
  let _ := historyKernel_isFinite n p hT
  apply (integrable_const ((5*p.1)^2)).mono' (by fun_prop)
  filter_upwards [historyKernel_displacement n p hT] with z hz
  simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖z.1-p.2.1‖)] using
    pow_le_pow_left₀ (norm_nonneg _) hz 2

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

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Bochner integration over the first collision in an actual history -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historyKernel_succ (n : ℕ) :
    historyKernel (n+1) = historyKernel n ∘ₖ historyStep := by
  unfold historyKernel
  rw [show historyStep^(n+1) = (historyStep^n) ∘ₖ historyStep by
    simpa only [pow_one] using Kernel.pow_add historyStep n 1]
  exact Kernel.map_comp _ _ _

theorem jumpAfterWait_apply (p : TimeFlightState) (s : ℝ) :
    jumpAfterWait (p,s) = (uniformizedKernel p.2.2).map (advanceState p s) := by
  ext A hA
  rw [jumpAfterWait,Kernel.map_apply' _ advanceState_measurable _ hA,
    Kernel.id_prod_apply' _ _ (advanceState_measurable hA),Kernel.comap_apply,
    Measure.map_apply (by unfold advanceState; fun_prop) hA]
  rfl

private theorem id_prod_integral {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : Kernel α β) [IsSFiniteKernel κ]
    (a : α) {f : α × β → E} (hf : StronglyMeasurable f) :
    (∫ q, f q ∂(Kernel.id ×ₖ κ) a) = ∫ b, f (a,b) ∂κ a := by
  rw [Kernel.prod_apply,Kernel.id_apply,Measure.dirac_prod]
  exact integral_map_of_stronglyMeasurable (by fun_prop) hf

theorem historyStep_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : TimeFlightState) {f : TimeFlightState → E} (hf : StronglyMeasurable f)
    (hi : Integrable f (historyStep p)) :
    (∫ q, f q ∂historyStep p) =
      ∫ s in Ioc 0 p.1, ∫ u, f (advanceState p s u) ∂uniformizedKernel p.2.2 := by
  rw [historyStep] at hi ⊢
  rw [Kernel.integral_comp hi,id_prod_integral _ _ hf.integral_kernel,waitingTime_apply]
  apply integral_congr_ae
  filter_upwards [] with s
  rw [jumpAfterWait_apply]
  exact integral_map_of_stronglyMeasurable (by unfold advanceState; fun_prop) hf

theorem historyKernel_succ_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (p : TimeFlightState) {f : FlightState → E} (hf : StronglyMeasurable f)
    (hi : Integrable f (historyKernel (n+1) p)) :
    (∫ z, f z ∂historyKernel (n+1) p) =
      ∫ s in Ioc 0 p.1, ∫ u, ∫ z, f z ∂historyKernel n (advanceState p s u)
        ∂uniformizedKernel p.2.2 := by
  rw [historyKernel_succ] at hi ⊢
  rw [Kernel.integral_comp hi]
  exact historyStep_integral p hf.integral_kernel hi.integral_comp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The exact mean displacement of each finite collision history -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historyMean_shift (n : ℕ) (p q : TimeFlightState) (hT : 0 ≤ q.1) :
    (∫ z, z.1-p.2.1 ∂historyKernel n q) =
      historyMean n q + simplexVolume n q.1 • (q.2.1-p.2.1) := by
  let _ := historyKernel_isFinite n q hT
  have heq (z : FlightState) : z.1-p.2.1 = (z.1-q.2.1)+(q.2.1-p.2.1) := by abel
  rw [show (fun z : FlightState => z.1-p.2.1) =
    (fun z => (z.1-q.2.1)+(q.2.1-p.2.1)) from funext heq]
  rw [integral_add (history_displacement_integrable n q hT) (integrable_const _),integral_const]
  change historyMean n q + (historyKernel n q univ).toReal • _ = _
  rw [historyKernel_mass n q hT,simplexTime_toReal n hT]

theorem historyMean_formula (n : ℕ) (p : TimeFlightState) (hT : 0 ≤ p.1) :
    historyMean n p = simplexVolume (n+1) p.1 • velocitySum n p.2.2 := by
  induction n generalizing p with
  | zero =>
    simp [historyMean,historyKernel_zero,Kernel.deterministic_apply,finishFlight,freeFlight,
      simplexVolume,velocitySum,chainAverage_zero]
  | succ n ih =>
    have hi := history_displacement_integrable (n+1) p hT
    rw [historyMean,historyKernel_succ_integral n p (by fun_prop) hi]
    have heq (s : ℝ) (hs : s ∈ Ioc 0 p.1) (u : RetainedState) :
        (∫ z, z.1-p.2.1 ∂historyKernel n (advanceState p s u)) =
          simplexVolume (n+1) (p.1-s) • velocitySum n u +
          (s*simplexVolume n (p.1-s)) • (p.2.2 : V) := by
      rw [historyMean_shift n p _ (sub_nonneg.mpr hs.2),ih _ (sub_nonneg.mpr hs.2)]
      simp only [advanceState,freeFlight,add_sub_cancel_left,smul_smul]
      rw [mul_comm]
    have hinner (s : ℝ) (hs : s ∈ Ioc 0 p.1) :
        (∫ u, ∫ z, z.1-p.2.1 ∂historyKernel n (advanceState p s u) ∂uniformizedKernel p.2.2) =
          simplexVolume (n+1) (p.1-s) • (∫ u, velocitySum n u ∂uniformizedKernel p.2.2) +
          (s*simplexVolume n (p.1-s)) • (p.2.2 : V) := by
      simp_rw [heq s hs]
      have hj : Integrable (fun u => simplexVolume (n+1) (p.1-s) • velocitySum n u)
          (uniformizedKernel p.2.2) := by
        have hf : Measurable (fun u : RetainedState =>
            simplexVolume (n+1) (p.1-s) • velocitySum n u) :=
          (measurable_const (a := simplexVolume (n+1) (p.1-s))).smul (velocitySum_measurable n)
        apply (integrable_const (‖simplexVolume (n+1) (p.1-s)‖*((n+1 : ℕ)*5 : ℝ))).mono'
          hf.aestronglyMeasurable
        apply ae_of_all
        intro u
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (velocitySum_bound n u) (norm_nonneg _)
      rw [integral_add hj (integrable_const _),integral_smul,integral_const,
        probReal_univ,one_smul]
    rw [setIntegral_congr_fun measurableSet_Ioc hinner,← intervalIntegral.integral_of_le hT]
    rw [intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_smul_const,intervalIntegral.integral_smul_const,
        integral_simplexVolume,integral_time_simplexVolume,← smul_add]
      congr 1
      rw [add_comm,velocitySum_succ]
    · exact (show Continuous (fun s : ℝ => simplexVolume (n+1) (p.1-s) •
        (∫ u, velocitySum n u ∂uniformizedKernel p.2.2)) by
          unfold simplexVolume; fun_prop).intervalIntegrable _ _
    · exact (show Continuous (fun s : ℝ => (s*simplexVolume n (p.1-s)) • (p.2.2 : V)) by
          unfold simplexVolume; fun_prop).intervalIntegrable _ _

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Translation of the exact second displacement moment -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historySecondMoment_shift (n : ℕ) (p q : TimeFlightState) (hT : 0 ≤ q.1) :
    (∫ z, ‖z.1-p.2.1‖^2 ∂historyKernel n q) =
      historySecondMoment n q + 2*inner ℝ (q.2.1-p.2.1) (historyMean n q) +
        simplexVolume n q.1 * ‖q.2.1-p.2.1‖^2 := by
  let _ := historyKernel_isFinite n q hT
  have hi := history_displacement_integrable n q hT
  have hs := history_displacement_sq_integrable n q hT
  have hj : Integrable (fun z : FlightState => inner ℝ (q.2.1-p.2.1) (z.1-q.2.1))
      (historyKernel n q) := (innerSL ℝ (q.2.1-p.2.1)).integrable_comp hi
  have hj2 : Integrable (fun z : FlightState => 2*inner ℝ (q.2.1-p.2.1) (z.1-q.2.1))
      (historyKernel n q) := hj.const_mul 2
  have hsum : Integrable (fun z : FlightState => ‖z.1-q.2.1‖^2 +
      2*inner ℝ (q.2.1-p.2.1) (z.1-q.2.1)) (historyKernel n q) := hs.add hj2
  have heq (z : FlightState) : ‖z.1-p.2.1‖^2 =
      ‖z.1-q.2.1‖^2 + 2*inner ℝ (q.2.1-p.2.1) (z.1-q.2.1) + ‖q.2.1-p.2.1‖^2 := by
    rw [show z.1-p.2.1 = (z.1-q.2.1)+(q.2.1-p.2.1) by abel,norm_add_sq_real,real_inner_comm]
  rw [show (fun z : FlightState => ‖z.1-p.2.1‖^2) = _ from funext heq,
    integral_add hsum (integrable_const _),
    integral_add hs hj2,integral_const_mul,integral_const]
  have hc := (innerSL ℝ (q.2.1-p.2.1)).integral_comp_comm hi
  change (∫ z, inner ℝ (q.2.1-p.2.1) (z.1-q.2.1) ∂historyKernel n q) =
    inner ℝ (q.2.1-p.2.1) (historyMean n q) at hc
  rw [hc]
  change historySecondMoment n q + _ + (historyKernel n q univ).toReal • _ = _
  rw [historyKernel_mass n q hT,simplexTime_toReal n hT,smul_eq_mul]

theorem historyMean_bound : ∃ B : ℝ, 0 < B ∧
    ∀ (n : ℕ) (p : TimeFlightState), 0 ≤ p.1 →
      ‖historyMean n p‖ ≤ B*simplexVolume (n+1) p.1 := by
  obtain ⟨B,hB,hbound⟩ := velocitySum_uniform_bound
  refine ⟨B,hB,?_⟩
  intro n p hT
  rw [historyMean_formula n p hT,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (simplexVolume_nonneg _ hT),mul_comm B]
  exact mul_le_mul_of_nonneg_left (hbound n p.2.2) (simplexVolume_nonneg _ hT)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A linear-in-count bound for the second moment on each time simplex -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory RealInnerProductSpace

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historySecondMoment_uniform_bound : ∃ K : ℝ, 0 < K ∧
    ∀ (n : ℕ) (p : TimeFlightState), 0 ≤ p.1 →
      historySecondMoment n p ≤ K*(n+1 : ℕ)*simplexVolume (n+2) p.1 := by
  obtain ⟨B,hB,hmean⟩ := historyMean_bound
  let K := 50+10*B
  have hK : 0 < K := by dsimp [K] <;> positivity
  refine ⟨K,hK,?_⟩
  intro n
  induction n with
  | zero =>
    intro p hT
    have hv := retainedState_norm p.2.2
    have hv2 : ‖(p.2.2 : V)‖^2 ≤ 25 := by nlinarith [norm_nonneg (p.2.2 : V)]
    simp only [historySecondMoment,historyKernel_zero,Kernel.deterministic_apply,integral_dirac,
      finishFlight,freeFlight,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hT]
    norm_num only [Nat.reduceAdd,Nat.cast_one,mul_one]
    have hc : K*simplexVolume 2 p.1 = K*p.1^2/2 := by norm_num [simplexVolume] <;> ring
    rw [hc,mul_pow]
    have hh := mul_le_mul_of_nonneg_left hv2 (sq_nonneg p.1)
    dsimp [K]
    nlinarith [mul_nonneg hB.le (sq_nonneg p.1)]
  | succ n ih =>
    intro p hT
    let F : ℝ → ℝ := fun s => K*(n+1 : ℕ)*simplexVolume (n+2) (p.1-s) +
      (10*B)*(s*simplexVolume (n+1) (p.1-s)) +
      25*(s^2*simplexVolume n (p.1-s))
    have hpoint (s : ℝ) (hs : s ∈ Ioc 0 p.1) (u : RetainedState) :
        (∫ z, ‖z.1-p.2.1‖^2 ∂historyKernel n (advanceState p s u)) ≤ F s := by
      let q := advanceState p s u
      have hq : 0 ≤ q.1 := sub_nonneg.mpr hs.2
      have hm := hmean n q hq
      have hsq := ih q hq
      have hd : ‖q.2.1-p.2.1‖ ≤ 5*s := by
        simpa only [q,advanceState,abs_of_pos hs.1] using freeFlight_displacement s p.2
      have hcross : 2*inner ℝ (q.2.1-p.2.1) (historyMean n q) ≤
          (10*B)*(s*simplexVolume (n+1) (p.1-s)) := by
        have hh := real_inner_le_norm (q.2.1-p.2.1) (historyMean n q)
        have hprod := mul_le_mul hd hm (norm_nonneg _) (mul_nonneg (by norm_num) hs.1.le : 0 ≤ 5*s)
        change ‖q.2.1-p.2.1‖*‖historyMean n q‖ ≤ 5*s*(B*simplexVolume (n+1) (p.1-s)) at hprod
        nlinarith
      have hlast : simplexVolume n q.1 * ‖q.2.1-p.2.1‖^2 ≤
          25*(s^2*simplexVolume n (p.1-s)) := by
        have hh := pow_le_pow_left₀ (norm_nonneg _) hd 2
        have hm := mul_le_mul_of_nonneg_left hh (simplexVolume_nonneg n hq)
        change simplexVolume n (p.1-s)*‖q.2.1-p.2.1‖^2 ≤
          simplexVolume n (p.1-s)*(5*s)^2 at hm
        change simplexVolume n (p.1-s)*‖q.2.1-p.2.1‖^2 ≤ _
        nlinarith
      rw [historySecondMoment_shift n p q hq]
      change historySecondMoment n q ≤ K*(n+1 : ℕ)*simplexVolume (n+2) (p.1-s) at hsq
      dsimp [F]
      linarith
    have hinner (s : ℝ) (hs : s ∈ Ioc 0 p.1) :
        (∫ u, ∫ z, ‖z.1-p.2.1‖^2 ∂historyKernel n (advanceState p s u)
          ∂uniformizedKernel p.2.2) ≤ F s := by
      calc
        _ ≤ ∫ _u, F s ∂uniformizedKernel p.2.2 :=
          integral_mono_of_nonneg (ae_of_all _ (fun _ => integral_nonneg (fun _ => sq_nonneg _)))
            (integrable_const _) (ae_of_all _ (hpoint s hs))
        _ = F s := by simp
    have hF : IntegrableOn F (Ioc 0 p.1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
        ((show Continuous F by dsimp [F,simplexVolume]; fun_prop).intervalIntegrable _ _)
    calc
      historySecondMoment (n+1) p =
          ∫ s in Ioc 0 p.1, ∫ u, ∫ z, ‖z.1-p.2.1‖^2
            ∂historyKernel n (advanceState p s u) ∂uniformizedKernel p.2.2 :=
        historyKernel_succ_integral n p (by fun_prop) (history_displacement_sq_integrable _ p hT)
      _ ≤ ∫ s in Ioc 0 p.1, F s := integral_mono_of_nonneg
        (ae_of_all _ (fun _ => integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))))
        hF (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs; exact hinner s hs)
      _ = K*(n+1+1 : ℕ)*simplexVolume (n+1+2) p.1 := by
        rw [← intervalIntegral.integral_of_le hT]
        dsimp [F]
        rw [intervalIntegral.integral_add,intervalIntegral.integral_add,
          intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul,integral_simplexVolume,
          integral_time_simplexVolume,integral_time_sq_simplexVolume]
        · dsimp [K]
          push_cast
          ring
        all_goals
          apply Continuous.intervalIntegrable
          unfold simplexVolume
          fun_prop

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A linear displacement second moment for the actual reference flight -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flight_displacement_second_moment : ∃ K : ℝ, 0 < K ∧
    ∀ (rate T : ℝ≥0), 0 < rate → ∀ z : FlightState,
      (∫⁻ w, ENNReal.ofReal (‖w.1-z.1‖^2) ∂flightKernel rate T z) ≤
        ENNReal.ofReal (K*(T : ℝ)/rate) := by
  obtain ⟨K,hK,hbound⟩ := historySecondMoment_uniform_bound
  refine ⟨K,hK,?_⟩
  intro rate T hr z
  have hn (n : ℕ) :
      (∫⁻ w, ENNReal.ofReal (‖w.1-z.1‖^2) ∂historyKernel n ((T : ℝ),z)) ≤
        ENNReal.ofReal K * ENNReal.ofReal ((n+1 : ℕ)*simplexVolume (n+2) T) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (history_displacement_sq_integrable n _ T.coe_nonneg)
      (ae_of_all _ (fun _ => sq_nonneg _)),← ENNReal.ofReal_mul hK.le]
    apply ENNReal.ofReal_le_ofReal
    simpa only [historySecondMoment,mul_assoc] using hbound n ((T : ℝ),z) T.coe_nonneg
  rw [flightKernel_apply,lintegral_sum_measure]
  simp only [lintegral_smul_measure,smul_eq_mul]
  calc
    _ ≤ ∑' n : ℕ, flightWeight rate T n *
        (ENNReal.ofReal K * ENNReal.ofReal ((n+1 : ℕ)*simplexVolume (n+2) T)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      gcongr
      exact hn n
    _ = ENNReal.ofReal K * (∑' n : ℕ, flightWeight rate T n *
        ENNReal.ofReal ((n+1 : ℕ)*simplexVolume (n+2) T)) := by
      simp_rw [mul_left_comm _ (ENNReal.ofReal K)]
      exact ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal ((T : ℝ)/rate) := by
      gcongr
      exact flightWeight_secondMoment_sum_le rate T hr
    _ = ENNReal.ofReal (K*(T : ℝ)/rate) := by
      rw [← ENNReal.ofReal_mul hK.le]
      congr 1
      ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform sublinear displacement probability for the actual flight -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flight_displacement_tail : ∃ K : ℝ, 0 < K ∧
    ∀ (rate T : ℝ≥0), 0 < rate → 0 < T → ∀ a : ℝ, 0 < a → ∀ z : FlightState,
      flightKernel rate T z {w | a*(T : ℝ) ≤ ‖w.1-z.1‖} ≤
        ENNReal.ofReal (K/((rate : ℝ)*a^2*T)) := by
  obtain ⟨K,hK,hbound⟩ := flight_displacement_second_moment
  refine ⟨K,hK,?_⟩
  intro rate T hr hT a ha z
  have hr' : 0 < (rate : ℝ) := hr
  have hT' : 0 < (T : ℝ) := hT
  have he : 0 < (a*(T : ℝ))^2 := sq_pos_of_pos (mul_pos ha hT')
  have hf : Measurable (fun w : FlightState => ENNReal.ofReal (‖w.1-z.1‖^2)) := by fun_prop
  calc
    _ ≤ flightKernel rate T z {w | ENNReal.ofReal ((a*(T : ℝ))^2) ≤
        ENNReal.ofReal (‖w.1-z.1‖^2)} := by
      apply measure_mono
      intro w hw
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hw 2)
    _ ≤ (∫⁻ w, ENNReal.ofReal (‖w.1-z.1‖^2) ∂flightKernel rate T z) /
        ENNReal.ofReal ((a*(T : ℝ))^2) :=
      meas_ge_le_lintegral_div hf.aemeasurable (by positivity) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (K*(T : ℝ)/rate) / ENNReal.ofReal ((a*(T : ℝ))^2) :=
      ENNReal.div_le_div (hbound rate T hr z) le_rfl
    _ = ENNReal.ofReal (K/((rate : ℝ)*a^2*T)) := by
      rw [← ENNReal.ofReal_div_of_pos he]
      congr 1
      field_simp

theorem flight_small_displacement (rate : ℝ≥0) (hr : 0 < rate) {a : ℝ} (ha : 0 < a) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ≥0, T₀ ≤ (T : ℝ) → ∀ z : FlightState,
      (1/2 : ℝ≥0∞) ≤ flightKernel rate T z {w | ‖w.1-z.1‖ < a*(T : ℝ)} := by
  obtain ⟨K,hK,hbound⟩ := flight_displacement_tail
  have hr' : 0 < (rate : ℝ) := hr
  let T₀ := 2*K/((rate : ℝ)*a^2)
  have hT₀ : 0 < T₀ := by dsimp [T₀] <;> positivity
  refine ⟨T₀,hT₀,?_⟩
  intro T hT z
  have hT' : 0 < (T : ℝ) := hT₀.trans_le hT
  have hd : 0 < (rate : ℝ)*a^2*T := by positivity
  have hlarge : 2*K ≤ (rate : ℝ)*a^2*T := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < (rate : ℝ)*a^2)).mp hT
  have hquot : K/((rate : ℝ)*a^2*T) ≤ (1:ℝ)/2 := by
    rw [div_le_iff₀ hd]
    nlinarith
  have hbad : flightKernel rate T z {w | a*(T : ℝ) ≤ ‖w.1-z.1‖} ≤ (1/2 : ℝ≥0∞) := by
    exact (hbound rate T hr hT' a ha z).trans (by
      simpa using ENNReal.ofReal_le_ofReal hquot)
  calc
    (1/2 : ℝ≥0∞) = 1-1/2 := by norm_num
    _ ≤ 1-flightKernel rate T z {w | a*(T : ℝ) ≤ ‖w.1-z.1‖} := tsub_le_tsub_left hbad 1
    _ = flightKernel rate T z {w | ‖w.1-z.1‖ < a*(T : ℝ)} := by
      rw [← prob_compl_eq_one_sub (by measurability)]
      congr 1
      ext w
      simp

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ReferenceGrowthBlocks
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform transverse-velocity entry for the actual Poisson flight -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem poissonKernel_term_le (r : ℝ≥0) (n : ℕ) (v : RetainedState) :
    poissonMeasure r {n} • (uniformizedKernel^n) v ≤ poissonKernel r v := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [poissonKernel,Kernel.sum_apply,Measure.sum_apply _ hA,Measure.smul_apply,smul_eq_mul]
  have hh := ENNReal.le_tsum (f := fun k => (Kernel.withDensity (uniformizedKernel^k)
    (fun _ _ => poissonMeasure r {k})) v A) n
  have heq (k : ℕ) : (Kernel.withDensity (uniformizedKernel^k)
      (fun _ _ => poissonMeasure r {k})) v A = poissonMeasure r {k}*(uniformizedKernel^k) v A := by
    rw [Kernel.withDensity_apply _ (show Measurable
      (Function.uncurry (fun (_ : RetainedState) (_ : RetainedState) => poissonMeasure r {k}))
      from measurable_const),withDensity_const,Measure.smul_apply,smul_eq_mul]
  simpa only [heq] using hh

theorem state_two_transverse_entry {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ v : RetainedState,
      c ≤ (uniformizedKernel^2) v {u | (u : V) ∈ ball firstAxis ζ} := by
  obtain ⟨c,hc,hct,hbound⟩ := retained_two_transverse_entry hζ
  let q := (ENNReal.ofReal (1/12 : ℝ))^2
  have hq : q ≠ 0 := by dsimp [q] <;> positivity
  have hqt : q ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ⟨q*c,mul_ne_zero hq hc,ENNReal.mul_ne_top hqt hct,?_⟩
  intro v
  have hm : ((stateKernel^2) v).map (Subtype.val : RetainedState → V) =
      (retainedJump beamAxis ∘ₖ retainedJump beamAxis) (v : V) := by
    rw [← Kernel.map_apply _ measurable_subtype_coe,stateKernel_pow_map,Kernel.comap_apply]
    congr 1
    simpa only [pow_one] using Kernel.pow_add (retainedJump beamAxis) 1 1
  have hb := hbound (v : V) (retainedState_norm v)
  rw [← hm,Measure.map_apply measurable_subtype_coe measurableSet_ball] at hb
  exact (mul_le_mul' le_rfl hb).trans
    (stateKernel_power_le_uniformized 2 v {u | (u : V) ∈ ball firstAxis ζ})

theorem poisson_transverse_entry (r : ℝ≥0) (hr : 0 < r) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ v : RetainedState,
      c ≤ poissonKernel r v {u | (u : V) ∈ ball firstAxis ζ} := by
  obtain ⟨c,hc,hct,hbound⟩ := state_two_transverse_entry hζ
  have hp : poissonMeasure r {2} ≠ 0 := by rw [poissonMeasure_singleton]; positivity
  have hpt : poissonMeasure r {2} ≠ ⊤ := measure_ne_top _ _
  refine ⟨poissonMeasure r {2}*c,mul_ne_zero hp hc,ENNReal.mul_ne_top hpt hct,?_⟩
  intro v
  exact (mul_le_mul' le_rfl (hbound v)).trans
    (poissonKernel_term_le r 2 v {u | (u : V) ∈ ball firstAxis ζ})

theorem flightKernel_displacement (rate T : ℝ≥0) (z : FlightState) :
    ∀ᵐ w ∂flightKernel rate T z, ‖w.1-z.1‖ ≤ 5*(T : ℝ) := by
  rw [flightKernel_apply,Measure.ae_sum_iff]
  intro n
  exact Measure.ae_smul_measure (historyKernel_displacement n ((T : ℝ),z) T.coe_nonneg) _

theorem flight_transverse_entry (rate : ℝ≥0) (hr : 0 < rate) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ z : FlightState,
      c ≤ flightKernel rate 1 z {w | (w.2 : V) ∈ ball firstAxis ζ} := by
  obtain ⟨c,hc,hct,hbound⟩ := poisson_transverse_entry rate hr hζ
  refine ⟨c,hc,hct,?_⟩
  intro z
  have hm := congrArg (fun μ : Measure RetainedState => μ {u | (u : V) ∈ ball firstAxis ζ})
    (flightKernel_velocity_map rate 1 z)
  rw [Measure.map_apply measurable_snd (show MeasurableSet {u : RetainedState | (u : V) ∈ ball firstAxis ζ} from
    measurable_subtype_coe measurableSet_ball),mul_one] at hm
  exact hm.symm ▸ hbound z.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Displacement geometry for the three intervals of a branching block -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem blockTarget_measurable (x : V) (A κ d : ℝ) : MeasurableSet (blockTarget x A κ d) := by
  unfold blockTarget
  measurability

theorem flight_block_geometry {x : V} {A κ d : ℝ} (hA : 0 < A) (hκ : 0 < κ)
    (hd : d ≤ 1) (hlarge : 5 < d*κ*A/4) {z w : FlightState}
    (hz : ‖z.1-x‖ < d*κ*A/4) (hw : ‖w.1-z.1‖ ≤ 5)
    (hv : (w.2 : V) ∈ ball firstAxis (d/4)) :
    freeFlight (κ*A) w ∈ blockTarget x A κ d := by
  have hdist : ‖(w.2 : V)-firstAxis‖ < d/4 := hv
  have hvnorm : ‖(w.2 : V)‖ < 2 := by
    have hh := norm_add_le ((w.2 : V)-firstAxis) firstAxis
    rw [sub_add_cancel,axis_norms.1] at hh
    linarith
  constructor
  · have heq : (freeFlight (κ*A) w).1-(x+(κ*A) • firstAxis) =
        (z.1-x)+(w.1-z.1)+(κ*A) • ((w.2 : V)-firstAxis) := by
      unfold freeFlight
      module
    rw [heq]
    have hn := norm_add_le ((z.1-x)+(w.1-z.1)) ((κ*A) • ((w.2 : V)-firstAxis))
    have hn' := norm_add_le (z.1-x) (w.1-z.1)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (mul_pos hκ hA)] at hn
    have hm := mul_lt_mul_of_pos_left hdist (mul_pos hκ hA)
    nlinarith
  · exact hvnorm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Cancellation of additional damping against positive retention weights -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem growth_damping_cancel (c δ T : ℝ) :
    growthWeight (c+δ) T * growthWeight (-δ) T = growthWeight c T := by
  unfold growthWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

theorem growth_damping_split (c δ T s : ℝ) :
    growthWeight (c+δ) (T-s) * growthWeight (-δ) T =
      growthWeight c (T-s) * growthWeight (-δ) s := by
  unfold growthWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

theorem growth_damping_clock (L C : ℝ≥0) (s : ℝ) :
    growthWeight ((L:ℝ)-(C:ℝ)) s * clockSurvival L s = clockSurvival C s := by
  unfold growthWeight clockSurvival
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

theorem time_cut_scale (k : ℝ≥0∞) (hk : k ≠ ⊤) {P D : ℝ≥0∞}
    {A B : ℝ → ℝ≥0∞} {T : ℝ}
    (hcut : ∀ s ∈ Ioc 0 T, P = A s+∫⁻ r in Ioc 0 s, B r)
    (htop : P = D+∫⁻ r in Ioc 0 T, B r) :
    (∀ s ∈ Ioc 0 T, k*P = k*A s+∫⁻ r in Ioc 0 s, k*B r) ∧
      k*P = k*D+∫⁻ r in Ioc 0 T, k*B r := by
  constructor
  · intro s hs
    rw [hcut s hs,mul_add,lintegral_const_mul' _ _ hk]
  · rw [htop,mul_add,lintegral_const_mul' _ _ hk]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The probability of a flight, a transverse refresh, and a straight final segment -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem terminalBlock_apply (rate : ℝ≥0) (τ : ℝ) (z : FlightState) :
    terminalBlock rate τ z = (flightKernel rate 1 z).map (freeFlight τ) := by
  rw [terminalBlock,freeFlightKernel,Kernel.deterministic_comp_eq_map,Kernel.map_apply]
  exact freeFlight_measurable.comp (measurable_const.prodMk measurable_id)

theorem driftBlock_lower (rate : ℝ≥0) (hr : 0 < rate) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ (A κ : ℝ) (T : ℝ≥0) (z : FlightState),
      0 < A → 0 < κ → 5 < d*κ*A/4 →
      (1/2 : ℝ≥0∞) ≤ flightKernel rate T z {w | ‖w.1-z.1‖ < d*κ*A/4} →
      c ≤ driftBlock rate T (κ*A) z (blockTarget z.1 A κ d) := by
  obtain ⟨c,hc,hct,hentry⟩ := flight_transverse_entry rate hr (ζ := d/4) (by positivity)
  refine ⟨(1/2)*c,mul_ne_zero (by norm_num) hc,ENNReal.mul_ne_top (by norm_num) hct,?_⟩
  intro A κ T z hA hκ hlarge hsmall
  let S : Set FlightState := {w | ‖w.1-z.1‖ < d*κ*A/4}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hlocal (w : FlightState) (hw : w ∈ S) :
      c ≤ terminalBlock rate (κ*A) w (blockTarget z.1 A κ d) := by
    rw [terminalBlock_apply,Measure.map_apply
      (show Measurable (freeFlight (κ*A)) from
        freeFlight_measurable.comp (measurable_const.prodMk measurable_id))
      (blockTarget_measurable z.1 A κ d)]
    apply (hentry w).trans
    apply measure_mono_ae
    filter_upwards [flightKernel_displacement rate 1 w] with y hy
    intro hv
    apply flight_block_geometry hA hκ hd1 hlarge hw
    · simpa using hy
    · exact hv
  rw [driftBlock,Kernel.comp_apply' _ _ _ (blockTarget_measurable z.1 A κ d)]
  calc
    (1/2 : ℝ≥0∞)*c ≤ flightKernel rate T z S*c := mul_le_mul' hsmall le_rfl
    _ = ∫⁻ _w in S, c ∂flightKernel rate T z := by
      rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]
    _ ≤ ∫⁻ w in S, terminalBlock rate (κ*A) w (blockTarget z.1 A κ d)
        ∂flightKernel rate T z := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hS] with w hw
      exact hlocal w hw
    _ ≤ ∫⁻ w, terminalBlock rate (κ*A) w (blockTarget z.1 A κ d)
        ∂flightKernel rate T z := lintegral_mono' Measure.restrict_le_self le_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The reference flight admits any larger damping with positive self-retention -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weightedFlight_changed_damping (L C : ℝ≥0) (hLC : L ≤ C)
    {c : ℝ} (hc : 0 ≤ c) {f : FlightState → ℝ≥0∞} (hf : Measurable f)
    (p : TimeFlightState) (hp : 0 ≤ p.1) :
    weightedFlight L c f p = clockSurvival C p.1*f (finishFlight p) +
      (∫⁻ s in Ioc 0 p.1, clockSurvival C s * ENNReal.ofReal (L:ℝ) *
        ∫⁻ u, weightedFlight L c f (advanceState p s u) ∂uniformizedKernel p.2.2) +
      ∫⁻ s in Ioc 0 p.1, clockSurvival C s * ENNReal.ofReal (c+(C:ℝ)-(L:ℝ)) *
        weightedFlight L c f (p.1-s,freeFlight s p.2) := by
  let δ : ℝ := (C:ℝ)-(L:ℝ)
  let k := growthWeight (-δ) p.1
  let A : ℝ → ℝ≥0∞ := fun s => clockSurvival L s *
    ∫⁻ z, f z ∂flightFamily L (p.1-s,freeFlight s p.2)
  let B : ℝ → ℝ≥0∞ := fun s => clockDensity L s *
    ∫⁻ u, ∫⁻ z, f z ∂flightFamily L (advanceState p s u) ∂uniformizedKernel p.2.2
  have hA : Measurable A := (show Measurable (clockSurvival L) by unfold clockSurvival; fun_prop).mul
    ((hf.lintegral_kernel (κ := flightFamily L)).comp (by unfold freeFlight; fun_prop))
  have hB : Measurable B := by
    have hm : Measurable (fun q : ℝ × RetainedState =>
        ∫⁻ z, f z ∂flightFamily L (advanceState p q.1 q.2)) :=
      (hf.lintegral_kernel (κ := flightFamily L)).comp (by unfold advanceState freeFlight; fun_prop)
    exact (show Measurable (clockDensity L) by unfold clockDensity; fun_prop).mul hm.lintegral_prod_right'
  have hcut (s : ℝ) (hs : s ∈ Ioc 0 p.1) :
      (∫⁻ z, f z ∂flightFamily L p) = A s+∫⁻ r in Ioc 0 s, B r := by
    simpa only [add_sub_cancel,p.eta] using
      flightFamily_time_cut L p.2 hs.1.le (sub_nonneg.mpr hs.2) hf
  have htop : (∫⁻ z, f z ∂flightFamily L p) =
      clockSurvival L p.1*f (finishFlight p)+∫⁻ s in Ioc 0 p.1, B s :=
    flightFamily_first_event L p hf
  have hδ : 0 ≤ δ := sub_nonneg.mpr (show (L:ℝ) ≤ (C:ℝ) from hLC)
  have hcδ : 0 ≤ c+δ := add_nonneg hc hδ
  have hs := time_cut_scale k (show k ≠ ⊤ from ENNReal.ofReal_ne_top) hcut htop
  have H := weighted_time_cut hcδ hp (measurable_const.mul hA) (measurable_const.mul hB) hs.1 hs.2
  have hkclock (s : ℝ) : growthWeight (-δ) s*clockSurvival L s = clockSurvival C s := by
    convert growth_damping_clock L C s using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [δ]
    congr 1
    ring_nf
  have hw (s : ℝ) : growthWeight (c+δ) (p.1-s)*k*clockSurvival L s =
      clockSurvival C s*growthWeight c (p.1-s) := by
    rw [show k = growthWeight (-δ) p.1 from rfl,growth_damping_split,mul_assoc,hkclock,mul_comm]
  rw [← mul_assoc,growth_damping_cancel] at H
  change weightedFlight L c f p = _ at H
  have hfirst : k*(clockSurvival L p.1*f (finishFlight p)) =
      clockSurvival C p.1*f (finishFlight p) := by
    rw [← mul_assoc,hkclock]
  rw [hfirst] at H
  rw [H]
  congr 1
  · congr 1
    apply lintegral_congr
    intro s
    dsimp only [Pi.mul_apply]
    rw [show growthWeight (c+δ) (p.1-s)*(k*B s) =
      (growthWeight (c+δ) (p.1-s)*k*clockSurvival L s)*ENNReal.ofReal (L:ℝ)*
        ∫⁻ u, ∫⁻ z, f z ∂flightFamily L (advanceState p s u) ∂uniformizedKernel p.2.2 by
          dsimp [B]; rw [clockDensity_eq]; ac_rfl,hw]
    have hg : growthWeight c (p.1-s) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [show (clockSurvival C s*growthWeight c (p.1-s))*ENNReal.ofReal (L:ℝ) =
      (clockSurvival C s*ENNReal.ofReal (L:ℝ))*growthWeight c (p.1-s) by ac_rfl,mul_assoc,
      ← lintegral_const_mul' _ _ hg]
    rfl
  · apply lintegral_congr
    intro s
    dsimp only [Pi.mul_apply]
    rw [growthDensity_eq hcδ]
    change ENNReal.ofReal (c+δ)*growthWeight (c+δ) (p.1-s)*(k*A s) = _
    rw [show ENNReal.ofReal (c+δ)*growthWeight (c+δ) (p.1-s)*(k*A s) =
      ENNReal.ofReal (c+δ)*(growthWeight (c+δ) (p.1-s)*k*clockSurvival L s)*
        ∫⁻ z, f z ∂flightFamily L (p.1-s,freeFlight s p.2) by dsimp [A]; ac_rfl,hw]
    have hcdef : c+δ = c+(C:ℝ)-(L:ℝ) := by dsimp [δ] <;> ring
    rw [hcdef]
    unfold weightedFlight
    ac_rfl

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

theorem branchingAt_physical {C : ℝ≥0} (hC : referenceClock ≤ C) (v : RetainedState) :
    branchingAt C v = ENNReal.ofReal (stateRate v) • stateKernel v +
      ENNReal.ofReal ((C:ℝ)-stateFrequency v) • Measure.dirac v := by
  have hδ : 0 ≤ (C:ℝ)-(referenceClock:ℝ) := sub_nonneg.mpr hC
  have hf : 0 ≤ 48*Real.pi-stateFrequency v := by
    linarith [(stateFrequency_bounds v).2,Real.pi_pos]
  rw [branchingAt_apply,branchingKernel_apply,add_assoc,← add_smul,← ENNReal.ofReal_add hf hδ]
  congr 2
  congr 1
  change 48*Real.pi-stateFrequency v+((C:ℝ)-48*Real.pi) = (C:ℝ)-stateFrequency v
  ring

theorem branchingAt_lower {C : ℝ≥0} (hC : referenceClock ≤ C) (v : RetainedState) :
    ENNReal.ofReal (referenceClock:ℝ) • uniformizedKernel v +
      ENNReal.ofReal (referenceGrowth+(C:ℝ)-(referenceClock:ℝ)) • Measure.dirac v ≤ branchingAt C v := by
  have hδ : 0 ≤ (C:ℝ)-(referenceClock:ℝ) := sub_nonneg.mpr hC
  have hg : 0 ≤ referenceGrowth := by unfold referenceGrowth; positivity
  have he : referenceGrowth+((C:ℝ)-(referenceClock:ℝ)) =
      referenceGrowth+(C:ℝ)-(referenceClock:ℝ) := by ring
  rw [branchingAt_apply]
  calc
    _ = (ENNReal.ofReal (referenceClock:ℝ) • uniformizedKernel v+
          ENNReal.ofReal referenceGrowth • Measure.dirac v)+
        ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) • Measure.dirac v := by
      rw [add_assoc,← add_smul,← ENNReal.ofReal_add hg hδ,he]
    _ ≤ _ := add_le_add (branchingKernel_lower v) le_rfl

theorem branchingAt_mass_bound {C : ℝ≥0} (hC : referenceClock ≤ C) (v : RetainedState) :
    branchingAt C v univ ≤ ENNReal.ofReal ((C:ℝ)+48*Real.pi) := by
  have hf := (stateFrequency_bounds v).1
  have hr := (stateRate_bounds v).2
  have hr0 : 0 ≤ stateRate v := by linarith [(stateRate_bounds v).1,Real.pi_pos]
  have hfreq : stateFrequency v ≤ (C:ℝ) :=
    (stateFrequency_bounds v).2.trans (by
      have hc : 48*Real.pi ≤ (C:ℝ) := hC
      linarith [Real.pi_pos])
  rw [branchingAt_physical hC,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    measure_univ,Measure.dirac_apply_of_mem (Set.mem_univ v),smul_eq_mul,smul_eq_mul,mul_one,mul_one,
    ← ENNReal.ofReal_add hr0 (sub_nonneg.mpr hfreq)]
  apply ENNReal.ofReal_le_ofReal
  linarith [Real.pi_pos]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The growing reference flight is dominated by histories at any larger damping -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weightedFlight_damped_subsolution {C : ℝ≥0} (hC : referenceClock ≤ C)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f)
    (p : TimeFlightState) (hp : 0 ≤ p.1) :
    weightedFlight referenceClock referenceGrowth f p ≤ flightSeed C f p +
      ∫⁻ q, weightedFlight referenceClock referenceGrowth f q ∂eventStep C (branchingAt C) p := by
  let F := weightedFlight referenceClock referenceGrowth f
  have hF : Measurable F := weightedFlight_measurable _ _ hf
  have hgain : Measurable (fun s : ℝ => clockSurvival C s * ENNReal.ofReal (referenceClock:ℝ) *
      ∫⁻ u, F (advanceState p s u) ∂uniformizedKernel p.2.2) := by
    have hm : Measurable (fun q : ℝ × RetainedState => F (advanceState p q.1 q.2)) :=
      hF.comp (by unfold advanceState freeFlight; fun_prop)
    exact (show Measurable (fun s => clockSurvival C s * ENNReal.ofReal (referenceClock:ℝ)) by
      unfold clockSurvival; fun_prop).mul hm.lintegral_prod_right'
  rw [weightedFlight_changed_damping referenceClock C hC (by unfold referenceGrowth; positivity) hf p hp,
    eventStep_lintegral _ _ _ hF]
  change flightSeed C f p+_+_ ≤ flightSeed C f p+_
  rw [add_assoc,← lintegral_add_left hgain]
  apply add_le_add le_rfl
  apply lintegral_mono
  intro s
  have hi := lintegral_mono' (branchingAt_lower hC p.2.2)
    (f := fun u => F (advanceState p s u)) le_rfl
  rw [lintegral_add_measure,lintegral_smul_measure,lintegral_smul_measure,
    lintegral_dirac,smul_eq_mul,smul_eq_mul] at hi
  change clockSurvival C s * ENNReal.ofReal (referenceClock:ℝ) *
      (∫⁻ u, F (advanceState p s u) ∂uniformizedKernel p.2.2) +
      clockSurvival C s * ENNReal.ofReal (referenceGrowth+(C:ℝ)-(referenceClock:ℝ)) *
        F (advanceState p s p.2.2) ≤ _
  calc
    _ = clockSurvival C s * (ENNReal.ofReal (referenceClock:ℝ) *
      (∫⁻ u, F (advanceState p s u) ∂uniformizedKernel p.2.2) +
      ENNReal.ofReal (referenceGrowth+(C:ℝ)-(referenceClock:ℝ))*F (advanceState p s p.2.2)) := by
        ring
    _ ≤ _ := mul_le_mul' le_rfl hi

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A uniform positive displacement block at every sufficiently large duration -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem large_driftBlock_lower (rate : ℝ≥0) (hr : 0 < rate) {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A₀ : ℝ) (c : ℝ≥0∞), 0 < A₀ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ z : FlightState,
        c ≤ driftBlock rate (blockFirstTime A κ) (κ*A) z (blockTarget z.1 A κ d) := by
  obtain ⟨T₀,hT₀,hsmall⟩ := flight_small_displacement rate hr (a := d*κ/4) (by positivity)
  obtain ⟨c,hc,hct,hblock⟩ := driftBlock_lower rate hr hd hd1
  let A₀ := max ((T₀+1)/(1-κ)) (20/(d*κ)+1)
  have hpos : 0 < 20/(d*κ)+1 := by positivity
  have hA₀ : 0 < A₀ := hpos.trans_le (le_max_right _ _)
  refine ⟨A₀,c,hA₀,hc,hct,?_⟩
  intro A hA z
  have hApos : 0 < A := hA₀.trans_le hA
  have htime : T₀ ≤ (1-κ)*A-1 := by
    have hh := (div_le_iff₀ (by linarith : 0 < 1-κ)).mp ((le_max_left _ _).trans hA)
    linarith
  have htime0 : 0 ≤ (1-κ)*A-1 := hT₀.le.trans htime
  have htime_coe : (blockFirstTime A κ : ℝ) = (1-κ)*A-1 := by
    exact Real.coe_toNNReal _ htime0
  have htimeA : (blockFirstTime A κ : ℝ) ≤ A := by
    rw [htime_coe]
    nlinarith [mul_pos hκ hApos]
  have hlarge : 5 < d*κ*A/4 := by
    have hh : 20/(d*κ)+1 ≤ A := (le_max_right _ _).trans hA
    have hi : 20/(d*κ) < A := by linarith
    have hj := (div_lt_iff₀ (mul_pos hd hκ)).mp hi
    nlinarith
  apply hblock A κ (blockFirstTime A κ) z hApos hκ hlarge
  apply (hsmall (blockFirstTime A κ) (by rwa [htime_coe]) z).trans
  apply measure_mono
  intro w hw
  change ‖w.1-z.1‖ < d*κ*A/4
  apply lt_of_lt_of_le hw
  have hh := mul_le_mul_of_nonneg_left htimeA (by positivity : 0 ≤ d*κ/4)
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive potential overcomes the cost of the final straight segment -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weighted_driftBlock_growth (rate : ℝ≥0) (hr : 0 < rate) {d κ g : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (rate : ℝ)*κ < g) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ z : FlightState,
      (8 : ℝ≥0∞) < ENNReal.ofReal (Real.exp ((g-(rate : ℝ)*κ)*A)) *
        driftBlock rate (blockFirstTime A κ) (κ*A) z (blockTarget z.1 A κ d) := by
  obtain ⟨a,c,ha,hc,hct,hblock⟩ := large_driftBlock_lower rate hr hd hd1 hκ hκ1
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc hct
  have he : 0 < g-(rate : ℝ)*κ := sub_pos.mpr hg
  let A₀ := max a (Real.log (9/c.toReal)/(g-(rate : ℝ)*κ))
  refine ⟨A₀,ha.trans_le (le_max_left _ _),?_⟩
  intro A hA z
  have haA : a ≤ A := (le_max_left _ _).trans hA
  have hexp : 9/c.toReal ≤ Real.exp ((g-(rate : ℝ)*κ)*A) := by
    have hlog := (div_le_iff₀ he).mp ((le_max_right _ _).trans hA)
    calc
      9/c.toReal = Real.exp (Real.log (9/c.toReal)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hnine : 9 ≤ Real.exp ((g-(rate : ℝ)*κ)*A)*c.toReal := by
    have hh := mul_le_mul_of_nonneg_right hexp hcpos.le
    rwa [div_mul_cancel₀ _ hcpos.ne'] at hh
  calc
    (8 : ℝ≥0∞) < 9 := by norm_num
    _ ≤ ENNReal.ofReal (Real.exp ((g-(rate : ℝ)*κ)*A)*c.toReal) := by
      simpa using ENNReal.ofReal_le_ofReal hnine
    _ = ENNReal.ofReal (Real.exp ((g-(rate : ℝ)*κ)*A))*c := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_toReal hct]
    _ ≤ _ := mul_le_mul' le_rfl (hblock A haA z)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The constructed drift block occurs inside the full reference flight law -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightKernel_free_lower (rate T : ℝ≥0) (z : FlightState) :
    clockSurvival rate T • freeFlightKernel T z ≤ flightKernel rate T z := by
  apply Measure.le_iff.mpr
  intro A hA
  have hf : Measurable (A.indicator (1 : FlightState → ℝ≥0∞)) := measurable_const.indicator hA
  have h := flightFamily_first_event rate ((T : ℝ),z) hf
  rw [flightFamily_eq,lintegral_indicator_one hA] at h
  rw [Measure.smul_apply,smul_eq_mul,freeFlightKernel,Kernel.deterministic_apply,
    Measure.dirac_apply' _ hA]
  rw [h]
  change clockSurvival rate T * A.indicator 1 (finishFlight ((T : ℝ),z)) ≤ _
  exact le_add_right le_rfl

theorem driftBlock_le_flight (rate T τ : ℝ≥0) (z : FlightState) {A : Set FlightState}
    (hA : MeasurableSet A) :
    clockSurvival rate τ * driftBlock rate T τ z A ≤ flightKernel rate (T+1+τ) z A := by
  rw [driftBlock,terminalBlock,Kernel.comp_assoc,← flightKernel_add,
    Kernel.comp_apply' _ _ _ hA,flightKernel_add rate (T+1) τ,Kernel.comp_apply' _ _ _ hA,
    ← lintegral_const_mul' _ _ (show clockSurvival rate τ ≠ ⊤ from ENNReal.ofReal_ne_top)]
  apply lintegral_mono
  intro w
  exact flightKernel_free_lower rate τ w A

theorem blockFirstTime_sum {A κ : ℝ} (h : 0 ≤ (1-κ)*A-1) (hκA : 0 ≤ κ*A) :
    (blockFirstTime A κ : ℝ) + 1 + (Real.toNNReal (κ*A) : ℝ) = A := by
  rw [blockFirstTime,Real.coe_toNNReal _ h,Real.coe_toNNReal _ hκA]
  ring

theorem full_flight_block_growth (rate : ℝ≥0) (hr : 0 < rate) {d κ g : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (rate : ℝ)*κ < g) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ z : FlightState,
      (8 : ℝ≥0∞) < growthWeight g A *
        flightKernel rate (Real.toNNReal A) z (blockTarget z.1 A κ d) := by
  obtain ⟨a,ha,hgrowth⟩ := weighted_driftBlock_growth rate hr hd hd1 hκ hκ1 hg
  let A₀ := max a (1/(1-κ))
  refine ⟨A₀,ha.trans_le (le_max_left _ _),?_⟩
  intro A hA z
  have hAA : 0 < A := ha.trans_le ((le_max_left _ _).trans hA)
  have hκA : 0 ≤ κ*A := (mul_pos hκ hAA).le
  have htime : 0 ≤ (1-κ)*A-1 := by
    have hh := (div_le_iff₀ (by linarith : 0 < 1-κ)).mp ((le_max_right _ _).trans hA)
    linarith
  have hsum : blockFirstTime A κ+1+Real.toNNReal (κ*A) = Real.toNNReal A := by
    apply NNReal.eq
    simp only [NNReal.coe_add,NNReal.coe_one,Real.coe_toNNReal _ hAA.le]
    exact blockFirstTime_sum htime hκA
  have hlow := driftBlock_le_flight rate (blockFirstTime A κ) (Real.toNNReal (κ*A)) z
    (blockTarget_measurable z.1 A κ d)
  rw [hsum,Real.coe_toNNReal _ hκA] at hlow
  have he : ENNReal.ofReal (Real.exp ((g-(rate : ℝ)*κ)*A)) =
      growthWeight g A * clockSurvival rate (κ*A) := by
    rw [growthWeight,clockSurvival,← ENNReal.ofReal_mul (by positivity),← Real.exp_add]
    congr 2
    ring
  calc
    (8 : ℝ≥0∞) < ENNReal.ofReal (Real.exp ((g-(rate : ℝ)*κ)*A)) *
        driftBlock rate (blockFirstTime A κ) (κ*A) z (blockTarget z.1 A κ d) :=
      hgrowth A ((le_max_left _ _).trans hA) z
    _ = growthWeight g A * (clockSurvival rate (κ*A)*
        driftBlock rate (blockFirstTime A κ) (κ*A) z (blockTarget z.1 A κ d)) := by rw [he,mul_assoc]
    _ ≤ _ := mul_le_mul' le_rfl hlow

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A uniformly finite positive-history block with transverse displacement -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weightedFlight_indicator (rate : ℝ≥0) (c : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (z : FlightState) {A : Set FlightState} (hA : MeasurableSet A) :
    weightedFlight rate c (A.indicator 1) (T,z) =
      growthWeight c T * flightKernel rate (Real.toNNReal T) z A := by
  have he : flightFamily rate (T,z) = flightKernel rate (Real.toNNReal T) z := by
    simpa only [Real.coe_toNNReal _ hT] using flightFamily_eq rate (Real.toNNReal T) z
  rw [weightedFlight,he,lintegral_indicator_one hA]

theorem weightedFlight_window_bound {f : FlightState → ℝ≥0∞} (hb : ∀ z, f z ≤ 1)
    {T : ℝ} (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) :
    weightedFlight referenceClock referenceGrowth f p ≤ ENNReal.ofReal (Real.exp (referenceGrowth*T)) := by
  calc
    _ ≤ growthWeight referenceGrowth p.1*1 :=
      mul_le_mul' le_rfl (flightFamily_average_bound _ p hp.1 hb)
    _ ≤ _ := by
      rw [mul_one]
      apply ENNReal.ofReal_le_ofReal
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp.2 (by unfold referenceGrowth; positivity))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite growing reference blocks with uniform larger damping -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_branching_remainder {C : ℝ≥0} (hC : referenceClock ≤ C)
    {A : ℝ} {f : FlightState → ℝ≥0∞} (hb : ∀ z, f z ≤ 1)
    (n : ℕ) (z : FlightState) (hA : 0 ≤ A) :
    (∫⁻ q, weightedFlight referenceClock referenceGrowth f q
      ∂((eventStep C (branchingAt C))^n) (A,z)) ≤
      ENNReal.ofReal (Real.exp (referenceGrowth*A)*
        (((C:ℝ)+48*Real.pi)*A)^n/(n.factorial : ℝ)) := by
  calc
    _ ≤ ∫⁻ _q, ENNReal.ofReal (Real.exp (referenceGrowth*A))
        ∂((eventStep C (branchingAt C))^n) (A,z) := by
      apply lintegral_mono_ae
      filter_upwards [eventStep_power_time_support C (branchingAt C) n (A,z) hA] with q hq
      exact weightedFlight_window_bound hb q hq
    _ = ENNReal.ofReal (Real.exp (referenceGrowth*A))*
        ((eventStep C (branchingAt C))^n) (A,z) univ := lintegral_const _
    _ ≤ ENNReal.ofReal (Real.exp (referenceGrowth*A))*
        (ENNReal.ofReal ((C:ℝ)+48*Real.pi)^n*simplexTime n A) :=
      mul_le_mul' le_rfl (eventStep_power_mass_bound C (branchingAt C)
        (by positivity) (branchingAt_mass_bound hC) n (A,z) hA)
    _ = _ := by
      rw [simplexTime,← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),mul_pow]
      congr 1
      ring

theorem damped_branching_remainder_on_window {C Cmax : ℝ≥0}
    (hC : referenceClock ≤ C) (hCmax : C ≤ Cmax) {A T : ℝ}
    (hA : 0 ≤ A) (hAT : A ≤ T) {f : FlightState → ℝ≥0∞}
    (hb : ∀ z, f z ≤ 1) (n : ℕ) (z : FlightState) :
    (∫⁻ q, weightedFlight referenceClock referenceGrowth f q
      ∂((eventStep C (branchingAt C))^n) (A,z)) ≤
      ENNReal.ofReal (Real.exp (referenceGrowth*T)*
        (((Cmax:ℝ)+48*Real.pi)*T)^n/(n.factorial : ℝ)) := by
  apply (damped_branching_remainder hC hb n z hA).trans
  apply ENNReal.ofReal_le_ofReal
  have hg : 0 ≤ referenceGrowth := by unfold referenceGrowth; positivity
  have hCC : (C:ℝ) ≤ (Cmax:ℝ) := hCmax
  gcongr

theorem uniform_damped_finite_block_growth_q80_oai {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Cmax : ℝ≥0, ∃ N : ℕ,
      ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
      ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
        (7 : ℝ≥0∞) < ∑ j ∈ Finset.range N,
          eventHistory C (branchingAt C)
            (flightSeed C ((blockTarget z.1 A κ d).indicator 1)) j (A,z) := by
  have hr : 0 < referenceClock := by
    change (0 : ℝ) < 48*Real.pi
    positivity
  obtain ⟨A₀,hA₀,hgrowth⟩ := full_flight_block_growth referenceClock hr hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T _hT Cmax
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.exp (referenceGrowth*T)*(((Cmax:ℝ)+48*Real.pi)*T)^n/(n.factorial : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero,mul_div_assoc] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((FloorSemiring.tendsto_pow_div_factorial_atTop (((Cmax:ℝ)+48*Real.pi)*T)).const_mul
          (Real.exp (referenceGrowth*T)))
  obtain ⟨N,hN⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ≥0∞) < 1))).exists
  refine ⟨N,?_⟩
  intro C hC hCmax A hA z
  have hApos : 0 < A := hA₀.trans_le hA.1
  let f : FlightState → ℝ≥0∞ := (blockTarget z.1 A κ d).indicator 1
  have hf : Measurable f := measurable_const.indicator (blockTarget_measurable z.1 A κ d)
  have hb (w : FlightState) : f w ≤ 1 := by
    dsimp [f]
    by_cases h : w ∈ blockTarget z.1 A κ d <;> simp [h]
  have hlower : (8 : ℝ≥0∞) < weightedFlight referenceClock referenceGrowth f (A,z) := by
    rw [weightedFlight_indicator _ _ hApos.le z (blockTarget_measurable z.1 A κ d)]
    exact hgrowth A hA.1 z
  have hexpand := event_finite_expansion C (branchingAt C)
    (weightedFlight_measurable _ _ hf) (flightSeed_measurable _ hf)
    (T := A) (fun q hq => weightedFlight_damped_subsolution hC hf q hq.1)
    N (A,z) ⟨hApos.le,le_rfl⟩
  have hrem := (damped_branching_remainder_on_window hC hCmax hApos.le hA.2 hb N z).trans hN.le
  by_contra hn
  have hsum : (∑ j ∈ Finset.range N, eventHistory C (branchingAt C)
      (flightSeed C f) j (A,z)) ≤ 7 := le_of_not_gt hn
  have hh := hexpand.trans (add_le_add hsum hrem)
  norm_num at hh
  exact (not_lt_of_ge hh) hlower

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniform_damped_finite_block_growth_q80_oai := @OAI.BoltzmannNonuniqueness.ReferenceGeometry.uniform_damped_finite_block_growth_q80_oai
