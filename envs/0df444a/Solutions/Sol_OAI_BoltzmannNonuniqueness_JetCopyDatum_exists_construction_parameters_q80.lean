-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:51:37.564194+00:00
-- url     : https://prove2.me/submissions/f1a1428c-e59e-4b52-98f4-93c613745c0b

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotLimitExtraction_exists_positive_seed_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotPairExtraction_characteristic_test_balance_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotPairExtraction_entry_window_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_uniform_late_zero_parameters_q80

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CompactParameterConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Compact time primitives for the characteristic weak equation -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem primitive_hasDerivAt {f : ℝ → ℝ} (hf : Continuous f) (a t : ℝ) :
    HasDerivAt (primitive a f) (f t) t :=
  intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a t)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt

theorem primitive_deriv {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    deriv (primitive a f) = f := by
  funext t
  exact (primitive_hasDerivAt hf a t).deriv

theorem primitive_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (primitive a f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun t => (primitive_hasDerivAt hf.continuous a t).differentiableAt,?_⟩
  rw [primitive_deriv hf.continuous]
  exact hf

theorem primitive_eq_zero_left {f : ℝ → ℝ} {a b t : ℝ}
    (hs : tsupport f ⊆ Ioo a b) (ht : t ≤ a) : primitive a f t = 0 := by
  rw [primitive,intervalIntegral.integral_symm]
  have hz : (∫ s in t..a, f s) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with s hs'
    rw [uIoc_of_le ht] at hs'
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact (not_lt_of_ge hs'.2) (hs h).1
  rw [hz,neg_zero]

theorem primitive_eq_zero_right {f : ℝ → ℝ} {a b t : ℝ}
    (hs : tsupport f ⊆ Ioo a b) (ht : b ≤ t) (hi : (∫ s, f s) = 0) :
    primitive a f t = 0 := by
  rw [primitive,intervalIntegral.integral_eq_integral_of_support_subset]
  · exact hi
  · intro s hs'
    have h := hs (subset_tsupport _ hs')
    exact ⟨h.1,h.2.le.trans ht⟩

theorem primitive_support {f : ℝ → ℝ} {a b : ℝ}
    (hs : tsupport f ⊆ Ioo a b) (hi : (∫ s, f s) = 0) :
    tsupport (primitive a f) ⊆ Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra h
  simp only [mem_Icc,not_and_or,not_le] at h
  obtain ht' | ht' := h
  · exact ht (primitive_eq_zero_left hs ht'.le)
  · exact ht (primitive_eq_zero_right hs ht'.le hi)

theorem primitive_compact {f : ℝ → ℝ} {a b : ℝ}
    (hs : tsupport f ⊆ Ioo a b) (hi : (∫ s, f s) = 0) :
    HasCompactSupport (primitive a f) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (primitive_support hs hi)

theorem exists_test_primitive {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ Ioo a b) (hi : (∫ s, f s) = 0) :
    ∃ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      tsupport g ⊆ Ioo a b ∧ deriv g = f := by
  obtain ⟨a₀,haa₀,ha₀⟩ := hc.isCompact.exists_forall_le' continuous_id.continuousOn
    (fun x hx => (hs hx).1)
  obtain ⟨b₀,hb₀b,hb₀⟩ := hc.isCompact.exists_forall_le' (α := ℝᵒᵈ)
    continuous_id.continuousOn (fun x hx => (hs hx).2)
  let b₁ : ℝ := OrderDual.ofDual b₀
  change b₁ < b at hb₀b
  change ∀ x ∈ tsupport f, x ≤ b₁ at hb₀
  let c := (a+a₀)/2
  let d := (b₁+b)/2
  have hs' : tsupport f ⊆ Ioo c d := by
    intro x hx
    have h₁ := ha₀ x hx
    have h₂ := hb₀ x hx
    change a₀ ≤ x at h₁
    constructor <;> dsimp [c,d] <;> linarith
  refine ⟨primitive c f,primitive_contDiff hf c,primitive_compact hs' hi,?_,
    primitive_deriv hf.continuous c⟩
  intro x hx
  have hx' := primitive_support hs' hi hx
  dsimp [c,d] at hx'
  constructor <;> linarith [hx'.1,hx'.2]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Compact-open convergence of tests with one common compact support -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

theorem tendsto_integral_mul_common_support {μ : Measure E} {u : E → ℝ} (hu : Integrable u μ)
    {F : ℕ → C(E,ℝ)} {f : C(E,ℝ)} {K : Set E} (hK : IsCompact K)
    (hF : ∀ n, tsupport (F n) ⊆ K) (hf : tsupport f ⊆ K)
    (h : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun n => ∫ x, F n x*u x ∂μ) atTop (𝓝 (∫ x, f x*u x ∂μ)) := by
  have hfc : HasCompactSupport f := hK.of_isClosed_subset (isClosed_tsupport f) hf
  obtain ⟨C,hC⟩ := f.continuous.bounded_above_of_compact_support hfc
  have hU := ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp h K hK
  have hb : ∀ᶠ n in atTop, ∀ x, ‖F n x‖ ≤ max C 0+1 := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hU) 1 (by norm_num)] with n hn x
    by_cases hx : x ∈ K
    · have hd := hn x hx
      have hfbound := (hC x).trans (le_max_left C 0)
      have he : ‖F n x‖ ≤ ‖F n x-f x‖+‖f x‖ := by
        simpa only [sub_add_cancel] using norm_add_le (F n x-f x) (f x)
      have hdist : ‖F n x-f x‖ < 1 := by
        rw [dist_eq_norm, norm_sub_rev] at hd
        exact hd
      linarith
    · have hz : F n x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hF n hs))
      rw [hz,norm_zero]
      positivity
  apply tendsto_integral_filter_of_dominated_convergence (fun x => (max C 0+1)*‖u x‖)
  · exact Eventually.of_forall (fun n => (F n).continuous.measurable.aestronglyMeasurable.mul hu.1)
  · filter_upwards [hb] with n hn
    exact ae_of_all _ (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hn x) (norm_nonneg _))
  · exact hu.norm.const_mul _
  · filter_upwards [] with x
    have ht : Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
      (continuous_eval_const x).continuousAt.tendsto.comp h
    exact ht.mul_const (u x)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AngularPairTests
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Angular normalization of the hard-sphere collision kernel

The angular measure is the ordinary area measure `volume.toSphere`. Its mass is
`4 * π`; the absolute normal component integrates to `2 * π * ‖g‖`.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem integrable_abs_inner_sphereArea (g : Velocity) :
    Integrable (fun ω : Sphere => |inner ℝ g (ω : Velocity)|) sphereArea := by
  apply (integrable_const ‖g‖).mono' (by fun_prop)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_abs]
  have hω : ‖(ω : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  simpa only [hω, mul_one] using abs_real_inner_le_norm g (ω : Velocity)

/-- The loss-frequency angular normalization in the manuscript. -/
theorem integral_collisionKernel_sphereArea (v w : Velocity) :
    (∫ ω : Sphere, collisionKernel v w ω ∂sphereArea) = 2 * Real.pi * ‖v - w‖ :=
  integral_abs_inner_sphereArea (v - w)

theorem integrable_collisionKernel_sphereArea (v w : Velocity) :
    Integrable (fun ω : Sphere => collisionKernel v w ω) sphereArea :=
  integrable_abs_inner_sphereArea (v - w)

end BoltzmannNonuniqueness

end

end

end OAI
end

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

end BoltzmannNonuniqueness.DatumBounds

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetProfiles
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A fixed smooth compactly supported thermal probability kernel -/

noncomputable section

open MeasureTheory Set Metric
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetThermalKernel

theorem bound_pos : 0 < bound := inv_pos.mpr bump.integral_pos

end BoltzmannNonuniqueness.JetThermalKernel

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetBarriers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetPeriodicDatum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakL1Operations
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded multipliers and uniqueness for weak L¹ limits -/

noncomputable section

open MeasureTheory Filter Set

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.unique {μ : Measure X} {f : ℕ → X → ℝ} {g h : X → ℝ}
    (hg : WeakL1Converges μ f g) (hh : WeakL1Converges μ f h) : g =ᵐ[μ] h := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq g h hg.2.1 hh.2.1
  intro s hs _hfinite
  let ψ : X → ℝ := s.indicator (fun _ => 1)
  have hψ : Measurable ψ := measurable_const.indicator hs
  have hb : ∃ C : ℝ, ∀ x, |ψ x| ≤ C := by
    refine ⟨1,fun x => ?_⟩
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  have he (u : X → ℝ) : (∫ x, ψ x*u x ∂μ) = ∫ x in s, u x ∂μ := by
    rw [← integral_indicator hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [ψ,hx]
  have h1 := hg.2.2 ψ hψ hb
  have h2 := hh.2.2 ψ hψ hb
  simp_rw [he] at h1 h2
  exact tendsto_nhds_unique h1 h2

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

/-! # Localizing weak L¹ convergence on measurable sets -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.restrict {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) {s : Set X} (hs : MeasurableSet s) :
    WeakL1Converges (μ.restrict s) f g := by
  refine ⟨h.1,h.2.1.restrict,?_⟩
  intro ψ hψ hB
  have hm : Measurable (s.indicator ψ) := hψ.indicator hs
  obtain ⟨C,hC⟩ := hB
  have hb : ∃ D : ℝ, ∀ x, |s.indicator ψ x| ≤ D := by
    refine ⟨max C 0,fun x => ?_⟩
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx] using (hC x).trans (le_max_left C 0)
    · simp only [indicator_of_notMem hx,abs_zero]
      exact le_max_right C 0
  have ht := h.2.2 _ hm hb
  have he (u : X → ℝ) : (∫ x, s.indicator ψ x*u x ∂μ) = ∫ x in s, ψ x*u x ∂μ := by
    rw [← integral_indicator hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  simpa only [he] using ht

end BoltzmannNonuniqueness.Published

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
theorem weight_one_le (v : Velocity) : 1 ≤ weight v := Real.one_le_exp (by positivity)

theorem moment_mono {f g : Velocity → ℝ} (h : ∀ v, f v ≤ g v) : moment f ≤ moment g :=
  lintegral_mono (fun v => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (h v) (weight_pos v).le))

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

theorem norm_le_weight (v : Velocity) : ‖v‖ ≤ weight v := by
  have he := Real.add_one_le_exp (‖v‖^2/2)
  change ‖v‖ ≤ Real.exp (‖v‖^2/2)
  nlinarith [sq_nonneg (‖v‖-1)]

theorem pair_weight_le (v w : Velocity) : 1+‖v‖+‖w‖ ≤ 3*weight v*weight w := by
  have h1 := weight_one_le v
  have h2 := weight_one_le w
  have ha : weight v ≤ weight v*weight w := le_mul_of_one_le_right (weight_pos v).le h2
  have hb : weight w ≤ weight v*weight w := le_mul_of_one_le_left (weight_pos w).le h1
  have hc : 1 ≤ weight v*weight w := (h1.trans ha)
  linarith [norm_le_weight v,norm_le_weight w]

end BoltzmannNonuniqueness.VelocityMoment

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_IncomingLossRate
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Incoming collision measures, including atomic cold partners -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*}

theorem incomingRate_nonneg (z : X × (Velocity × Velocity)) : 0 ≤ incomingRate z := by
  unfold incomingRate
  positivity

variable [MeasurableSpace X]

theorem incomingRate_measurable : Measurable (incomingRate (X := X)) := by
  unfold incomingRate
  fun_prop

theorem incomingCollisionMeasure_mass (μ : Measure (X × (Velocity × Velocity))) [SFinite μ] :
    incomingCollisionMeasure μ univ = ∫⁻ z, ENNReal.ofReal (incomingRate z) ∂μ := by
  rw [incomingCollisionMeasure,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  rw [lintegral_prod _ hm.aemeasurable]
  apply lintegral_congr
  intro z
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_collisionKernel_sphereArea z.2.1 z.2.2)
    (ae_of_all _ (fun ω : Sphere => show 0 ≤ collisionKernel z.2.1 z.2.2 ω from abs_nonneg _)),
    integral_collisionKernel_sphereArea]
  rfl

theorem incomingCollisionMeasure_finite {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ) : IsFiniteMeasure (incomingCollisionMeasure μ) := by
  constructor
  rw [incomingCollisionMeasure_mass,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ incomingRate_nonneg)]
  exact ENNReal.ofReal_lt_top

theorem incomingLeft_measurable : Measurable (incomingLeft (X := X)) := by
  unfold incomingLeft scatterLeft normalComponent
  fun_prop

theorem incomingRight_measurable : Measurable (incomingRight (X := X)) := by
  unfold incomingRight scatterRight normalComponent
  fun_prop

theorem incomingGainMeasure_mass (μ : Measure (X × (Velocity × Velocity))) :
    incomingGainMeasure μ univ = incomingCollisionMeasure μ univ := by
  rw [incomingGainMeasure,Measure.smul_apply,Measure.add_apply,
    Measure.map_apply incomingLeft_measurable MeasurableSet.univ,
    Measure.map_apply incomingRight_measurable MeasurableSet.univ]
  simp only [preimage_univ,smul_eq_mul]
  rw [← two_mul,← mul_assoc]
  rw [one_div,ENNReal.inv_mul_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0) (by simp),one_mul]

theorem incomingLossMeasure_mass (μ : Measure (X × (Velocity × Velocity))) :
    incomingLossMeasure μ univ = incomingCollisionMeasure μ univ := by
  rw [incomingLossMeasure,Measure.map_apply (by fun_prop) MeasurableSet.univ,preimage_univ]

theorem incomingGainMeasure_finite {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ) : IsFiniteMeasure (incomingGainMeasure μ) := by
  let _ := incomingCollisionMeasure_finite hi
  exact ⟨by rw [incomingGainMeasure_mass]; exact measure_lt_top _ _⟩

theorem incomingLossMeasure_finite {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ) : IsFiniteMeasure (incomingLossMeasure μ) := by
  let _ := incomingCollisionMeasure_finite hi
  exact ⟨by rw [incomingLossMeasure_mass]; exact measure_lt_top _ _⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Testing the actual incoming gain and loss measures -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingCollisionMeasure_integral (μ : Measure (X × (Velocity × Velocity)))
    (f : (X × (Velocity × Velocity)) × Sphere → ℝ) :
    (∫ z, f z ∂incomingCollisionMeasure μ) =
      ∫ z, collisionKernel z.1.2.1 z.1.2.2 z.2*f z ∂μ.prod sphereArea := by
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  rw [incomingCollisionMeasure,integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only
    rw [ENNReal.toReal_ofReal (show 0 ≤ collisionKernel z.1.2.1 z.1.2.2 z.2 from abs_nonneg _),
      smul_eq_mul])

theorem incomingLossMeasure_integral {μ : Measure (X × (Velocity × Velocity))}
    {f : X × Velocity → ℝ} (hf : Measurable f) :
    (∫ z, f z ∂incomingLossMeasure μ) =
      ∫ z, f (z.1.1,z.1.2.2) ∂incomingCollisionMeasure μ := by
  rw [incomingLossMeasure,integral_map (by fun_prop) hf.aestronglyMeasurable]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Fubini formulas for incoming collision measures with atomic partners -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingCollisionMeasure_integral_prod
    {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ)
    {f : (X × (Velocity × Velocity)) × Sphere → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ z, |f z| ≤ B) :
    (∫ z, f z ∂incomingCollisionMeasure μ) =
      ∫ p, ∫ ω, collisionKernel p.2.1 p.2.2 ω*f (p,ω) ∂sphereArea ∂μ := by
  let _ := incomingCollisionMeasure_finite hi
  have hif : Integrable f (incomingCollisionMeasure μ) :=
    (integrable_const B).mono' hf.aestronglyMeasurable (ae_of_all _ hB)
  have hd : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  have hw := (integrable_withDensity_iff_integrable_smul' hd
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hif
  have hweight : Integrable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      collisionKernel z.1.2.1 z.1.2.2 z.2*f z) (μ.prod sphereArea) := by
    convert hw using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    rw [ENNReal.toReal_ofReal (show 0 ≤ collisionKernel z.1.2.1 z.1.2.2 z.2 from abs_nonneg _),
      smul_eq_mul]
  rw [incomingCollisionMeasure_integral]
  exact integral_prod _ hweight

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Finite incoming collision rates from the proved Gaussian pair moment -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingRate_integrable_of_gaussian {μ : Measure (X × (Velocity × Velocity))}
    (hm : (∫⁻ z, ENNReal.ofReal (weight z.2.1*weight z.2.2) ∂μ) < ∞) :
    Integrable incomingRate μ := by
  have hn : ∀ᵐ z ∂μ, 0 ≤ weight z.2.1*weight z.2.2 :=
    ae_of_all _ (fun z => mul_nonneg (weight_pos z.2.1).le (weight_pos z.2.2).le)
  have hw : Integrable (fun z : X × (Velocity × Velocity) => weight z.2.1*weight z.2.2) μ := by
    refine ⟨by unfold weight; fun_prop,?_⟩
    exact (hasFiniteIntegral_iff_ofReal hn).mpr hm
  apply (hw.const_mul (6*Real.pi)).mono' incomingRate_measurable.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (incomingRate_nonneg z)]
  have hv := norm_sub_le z.2.1 z.2.2
  have hp := pair_weight_le z.2.1 z.2.2
  have hh : ‖z.2.1-z.2.2‖ ≤ 3*(weight z.2.1*weight z.2.2) := by linarith
  have he := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*Real.pi by positivity)
  dsimp only [incomingRate]
  nlinarith

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The incoming loss measure is the incoming rate at the retained velocity -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingLossMeasure_rate_integral
    {μ : Measure (X × (Velocity × Velocity))} [SFinite μ]
    (hi : Integrable incomingRate μ) {ψ : X × Velocity → ℝ}
    (hψ : Measurable ψ) {B : ℝ} (hB : ∀ z, |ψ z| ≤ B) :
    (∫ z, ψ z ∂incomingLossMeasure μ) =
      ∫ z, incomingRate z*ψ (z.1,z.2.2) ∂μ := by
  rw [incomingLossMeasure_integral hψ]
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ψ (z.1.1,z.1.2.2)) := hψ.comp (measurable_fst.fst.prodMk measurable_fst.snd.snd)
  rw [incomingCollisionMeasure_integral_prod hi hm (fun z => hB _)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [integral_mul_const,integral_collisionKernel_sphereArea]
  rfl

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveSourceFormula
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! # Finite positive measures associated with integrable collision densities -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem positiveDensityMeasure_finite {μ : Measure X} {f : X → ℝ}
    (hi : Integrable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) :
    IsFiniteMeasure (positiveDensityMeasure μ f) := by
  exact isFiniteMeasure_withDensity ((hasFiniteIntegral_iff_ofReal hn).mp hi.2).ne

theorem positiveDensityMeasure_integral {μ : Measure X} {f : X → ℝ}
    (hm : AEMeasurable f μ) (hn : ∀ᵐ x ∂μ, 0 ≤ f x) (ψ : X → ℝ) :
    (∫ x, ψ x ∂positiveDensityMeasure μ f) = ∫ x, ψ x*f x ∂μ := by
  rw [positiveDensityMeasure,integral_withDensity_eq_integral_toReal_smul₀ hm.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  rw [ENNReal.toReal_ofReal hx,smul_eq_mul,mul_comm]

end BoltzmannNonuniqueness

end

end

section

/-! # Nonnegative smooth compact tests determine finite phase measures -/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem positive_smooth_compact_approximation {f : X → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hn : ∀ x, 0 ≤ f x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      (∀ x, 0 ≤ g x) ∧ ∀ x, |g x-f x| ≤ 2*ε := by
  obtain ⟨g,hg,hgf⟩ := (hc.uniformContinuous_of_continuous hf).exists_contDiff_dist_le hε
  obtain ⟨R,hR,hball⟩ := hc.isBounded.subset_ball_lt 0 (0 : X)
  let b : ContDiffBump (0 : X) := ⟨R,R+1,hR,by linarith⟩
  have hbf (x : X) : b x*f x = f x := by
    by_cases hx : x ∈ tsupport f
    · rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall (hball hx)),one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero]
  have hgε (x : X) : |g x-f x| < ε := by
    simpa only [Real.dist_eq] using hgf x
  refine ⟨fun x => b x*(g x+ε),b.contDiff.mul (hg.add contDiff_const),
    b.hasCompactSupport.mul_right,?_,?_⟩
  · intro x
    have := (abs_lt.mp (hgε x)).1
    exact mul_nonneg b.nonneg (by linarith [hn x])
  · intro x
    have he : b x*(g x+ε)-f x = b x*(g x-f x+ε) := by
      calc
        _ = b x*(g x+ε)-b x*f x := by rw [hbf]
        _ = _ := by ring
    rw [he,abs_mul,abs_of_nonneg b.nonneg]
    have hb : b x ≤ 1 := b.le_one
    have hh : |g x-f x+ε| ≤ 2*ε := by
      calc
        _ ≤ |g x-f x|+|ε| := abs_add_le _ _
        _ ≤ 2*ε := by rw [abs_of_pos hε]; linarith [hgε x]
    exact (mul_le_mul_of_nonneg_left hh b.nonneg).trans (by nlinarith)

variable [MeasurableSpace X] [BorelSpace X]

theorem finite_measure_eq_of_positive_smooth_tests
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ f : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      (∀ x, 0 ≤ f x) → ∫ x, f x ∂μ = ∫ x, f x ∂ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported_nnreal
  intro f
  let F : X → ℝ := fun x => (f x : ℝ)
  have hF : Continuous F := NNReal.continuous_coe.comp f.continuous
  have hFc : HasCompactSupport F := f.hasCompactSupport.comp_left rfl
  have hFn : ∀ x, 0 ≤ F x := fun x => (f x).coe_nonneg
  have hFiμ : Integrable F μ := hF.integrable_of_hasCompactSupport hFc
  have hFiν : Integrable F ν := hF.integrable_of_hasCompactSupport hFc
  apply eq_of_abs_sub_le_all
  intro δ hδ
  let ε := δ/(2*(μ.real univ+ν.real univ+1))
  have hmass : 0 < μ.real univ+ν.real univ+1 := by positivity
  have hε : 0 < ε := div_pos hδ (mul_pos (by norm_num) hmass)
  obtain ⟨g,hg,hgc,hgn,hgF⟩ := positive_smooth_compact_approximation hF hFc hFn hε
  have hgiμ : Integrable g μ := hg.continuous.integrable_of_hasCompactSupport hgc
  have hgiν : Integrable g ν := hg.continuous.integrable_of_hasCompactSupport hgc
  have hμ : |(∫ x, F x ∂μ)-(∫ x, g x ∂μ)| ≤ 2*ε*μ.real univ := by
    rw [← integral_sub hFiμ hgiμ]
    change ‖∫ x, F x-g x ∂μ‖ ≤ _
    exact norm_integral_le_of_norm_le_const (ae_of_all μ (fun x => by
      simpa only [Real.norm_eq_abs,abs_sub_comm] using hgF x))
  have hν : |(∫ x, g x ∂ν)-(∫ x, F x ∂ν)| ≤ 2*ε*ν.real univ := by
    rw [← integral_sub hgiν hFiν]
    change ‖∫ x, g x-F x ∂ν‖ ≤ _
    exact norm_integral_le_of_norm_le_const (ae_of_all ν (fun x => by
      simpa only [Real.norm_eq_abs] using hgF x))
  have he : (∫ x, g x ∂μ) = ∫ x, g x ∂ν := h g hg hgc hgn
  calc
    |(∫ x, F x ∂μ)-(∫ x, F x ∂ν)| ≤
        |(∫ x, F x ∂μ)-(∫ x, g x ∂μ)|+
        |(∫ x, g x ∂ν)-(∫ x, F x ∂ν)| := by
      rw [he]
      exact abs_sub_le _ _ _
    _ ≤ 2*ε*(μ.real univ+ν.real univ) := by linarith
    _ ≤ δ := by
      calc
        _ ≤ 2*ε*(μ.real univ+ν.real univ+1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = δ := by
          dsimp [ε]
          field_simp


end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # A countable positive smooth family determining finite phase measures -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.Compactness

theorem positivePhaseTest_smooth (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (positivePhaseTest j) :=
  (positivePhaseSeq (Nat.unpair j).1 (Nat.unpair j).2).2.1

theorem positivePhaseTest_compact (j : ℕ) : HasCompactSupport (positivePhaseTest j) :=
  (isCompact_closedBall (0 : Velocity × Velocity) ((Nat.unpair j).1+1 : ℝ)).of_isClosed_subset
    (isClosed_tsupport _) (positivePhaseSeq (Nat.unpair j).1 (Nat.unpair j).2).2.2.1

theorem positivePhaseTest_nonneg (j : ℕ) (p : Velocity × Velocity) :
    0 ≤ positivePhaseTest j p :=
  (positivePhaseSeq (Nat.unpair j).1 (Nat.unpair j).2).2.2.2 p

theorem finite_phase_measure_eq_of_countable_tests
    (μ ν : Measure (Velocity × Velocity)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ j, ∫ p, positivePhaseTest j p ∂μ = ∫ p, positivePhaseTest j p ∂ν) : μ = ν := by
  apply finite_measure_eq_of_positive_smooth_tests μ ν
  intro φ hφ hc hn
  obtain ⟨R,_hR,hball⟩ := hc.isBounded.subset_ball_lt 0 (0 : Velocity × Velocity)
  obtain ⟨n,hnR⟩ := exists_nat_gt R
  have hsupp : tsupport φ ⊆ Metric.closedBall (0 : Velocity × Velocity) (n+1 : ℝ) := by
    intro p hp
    have hpR : ‖p‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hball hp
    rw [Metric.mem_closedBall,dist_zero_right]
    linarith
  let t : PositivePhaseTest n := ⟨⟨φ,hφ.continuous⟩,hφ,hsupp,hn⟩
  have hd : DenseRange (positivePhaseSeq n) :=
    TopologicalSpace.denseRange_denseSeq (PositivePhaseTest n)
  obtain ⟨a,ha,hat⟩ := mem_closure_iff_seq_limit.mp (hd t)
  choose b hb using ha
  have hat' : Tendsto (fun m => (positivePhaseSeq n (b m)).1) atTop (𝓝 t.1) := by
    have he : (fun m => positivePhaseSeq n (b m)) = a := funext hb
    have hseq : Tendsto (fun m => positivePhaseSeq n (b m)) atTop (𝓝 t) := by
      rw [he]
      exact hat
    exact continuous_subtype_val.continuousAt.tendsto.comp hseq
  have hμ := tendsto_integral_mul_common_support (integrable_const (1 : ℝ) (μ := μ))
    (isCompact_closedBall (0 : Velocity × Velocity) (n+1 : ℝ))
    (fun m => (positivePhaseSeq n (b m)).2.2.1) hsupp hat'
  have hν := tendsto_integral_mul_common_support (integrable_const (1 : ℝ) (μ := ν))
    (isCompact_closedBall (0 : Velocity × Velocity) (n+1 : ℝ))
    (fun m => (positivePhaseSeq n (b m)).2.2.1) hsupp hat'
  simp only [mul_one] at hμ hν
  have heq (m) : (∫ p, (positivePhaseSeq n (b m)).1 p ∂μ) =
      ∫ p, (positivePhaseSeq n (b m)).1 p ∂ν := by
    have hj := h (Nat.pair n (b m))
    unfold positivePhaseTest at hj
    rw [Nat.unpair_pair] at hj
    exact hj
  simp_rw [heq] at hμ
  exact tendsto_nhds_unique hμ hν

end BoltzmannNonuniqueness.Compactness

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalMomentIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.branchingAt_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventAfterWait_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightFamily_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.flightKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.freeFlightKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.historyStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.jumpAfterWait_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.rawEventStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.renewalStep_pow_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.waitingTime_isSFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Volume domination by the selected two-collision angular window -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem localTwoCollisionLaw_volume_domination :
    ∃ (δ : ℝ) (B : ℝ≥0∞), 0 < δ ∧ δ ≤ 1/4 ∧ B ≠ 0 ∧ B ≠ ⊤ ∧
      ∀ v ∈ ball beamAxis δ,
        volume.restrict (ball (0 : V) δ) ≤ B •
          localTwoCollisionLaw v := by
  obtain ⟨d,C,hd,hC0,hCt,hout,hin⟩ := paired_parameterSphere_dominated
  obtain ⟨ε,hε,hεsmall,hgood⟩ := collision_window_good
  obtain ⟨a,δ,K,_ha,hab,hδ,hδa,hK,hvolume⟩ :=
    uniform_family_window_volume (lt_min hd hε)
  have had := hab.trans (min_le_left _ _)
  have haε := hab.trans (min_le_right _ _)
  have hδsmall := hδa.trans (haε.trans hεsmall)
  let I := ENNReal.ofReal (2*δ)
  let B := I⁻¹ * (K : ℝ≥0∞)^3 * (C^2)
  have hI0 : I ≠ 0 := by dsimp [I] <;> positivity
  have hIt : I ≠ ⊤ := ENNReal.ofReal_ne_top
  have hKn : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
  have hB0 : B ≠ 0 := mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr hIt)
    (pow_ne_zero 3 hKn)) (pow_ne_zero 2 hC0)
  have hBt : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hI0) (ENNReal.pow_ne_top ENNReal.coe_ne_top))
    (ENNReal.pow_ne_top hCt)
  refine ⟨δ,B,hδ,hδsmall,hB0,hBt,?_⟩
  intro v hv
  have hupper := familyWindowMap_local_le haε hδa had hCt hgood hout hin hv
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.restrict_apply hA,Measure.smul_apply,smul_eq_mul]
  have hlower := hvolume v hv (A ∩ ball (0 : V) δ) (hA.inter measurableSet_ball) inter_subset_right
  have hAupper : ((familyWindowMeasure a δ).map (familyWindowMap v)) (A ∩ ball (0 : V) δ) ≤
      (C^2) * localTwoCollisionLaw v A := by
    exact (hupper _).trans (by
      rw [Measure.smul_apply,smul_eq_mul]
      exact mul_le_mul' le_rfl (measure_mono inter_subset_left))
  have htotal : I * volume (A ∩ ball (0 : V) δ) ≤ (K : ℝ≥0∞)^3 *
      ((C^2) * localTwoCollisionLaw v A) := by
    exact hlower.trans (by gcongr)
  calc
    volume (A ∩ ball (0 : V) δ) = I⁻¹ * (I * volume (A ∩ ball (0 : V) δ)) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel hI0 hIt,one_mul]
    _ ≤ I⁻¹ * ((K : ℝ≥0∞)^3 *
        ((C^2) * localTwoCollisionLaw v A)) := by gcongr
    _ = B * localTwoCollisionLaw v A := by simp only [B,mul_assoc]

end BoltzmannNonuniqueness.ReferenceGeometry

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

theorem accessAngles_positive : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧
    ∀ κ ρ : ℝ, 0 < κ → 0 < ρ → κ+ρ ≤ δ →
      0 < (sphereProbability.prod sphereProbability) (accessAngles κ ρ) := by
  obtain ⟨δ,B,hδ,hδsmall,_hB0,_hBt,hvolume⟩ := localTwoCollisionLaw_volume_domination
  refine ⟨δ,hδ,hδsmall,?_⟩
  intro κ ρ hκ hρ hκρ
  have hsub : ball (κ • firstAxis) ρ ⊆ ball (0 : V) δ := by
    intro v hv
    have ht := dist_triangle v (κ • firstAxis) 0
    simp only [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hκ,axis_norms.1,mul_one] at ht
    change dist v 0 < δ
    rw [dist_zero_right]
    have hv' : dist v (κ • firstAxis) < ρ := hv
    linarith
  have hv := hvolume beamAxis (mem_ball_self hδ) (ball (κ • firstAxis) ρ)
  rw [Measure.restrict_apply measurableSet_ball,inter_eq_left.mpr hsub,
    Measure.smul_apply,smul_eq_mul] at hv
  have hp : 0 < volume (ball (κ • firstAxis) ρ) := measure_ball_pos volume _ hρ
  have hl : 0 < localTwoCollisionLaw beamAxis (ball (κ • firstAxis) ρ) := by
    by_contra hz
    have hz' : localTwoCollisionLaw beamAxis (ball (κ • firstAxis) ρ) = 0 :=
      bot_unique (not_lt.mp hz)
    rw [hz',mul_zero] at hv
    exact (not_le_of_gt hp) hv
  simpa only [localTwoCollisionLaw,Measure.map_apply (twoCollisionMap_measurable beamAxis)
    measurableSet_ball,Measure.restrict_apply
      ((twoCollisionMap_measurable beamAxis) measurableSet_ball),accessAngles] using hl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BackgroundCappedLoss
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

theorem frequency_nonneg (θ η l K α γ t : ℝ) (x : JetPrototype.Space) (v : Velocity) :
    0 ≤ frequency θ η l K α γ t x v :=
  mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _))

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

private theorem cell_distance_measurable {K α γ μ : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) :
    Measurable (fun p : (ℝ × ℝ) × Velocity =>
      ∫ w, ‖p.2-w‖ ∂AxialBackground.cell K α γ μ (max 0 p.1.1) p.1.2) := by
  have ha (σ : ℝ) : Measurable (fun p : (ℝ × ℝ) × Velocity =>
      AxialBackground.weight K α γ μ (max 0 p.1.1) σ p.1.2 *
        ‖p.2-PlaneChart.join 0 (AxialFlow.velocity σ α γ μ (max 0 p.1.1) p.1.2)‖) := by
    have hw := (AxialBackground.clamped_weight_measurable hα hγ hμ K σ).comp
      (measurable_fst : Measurable (fun p : (ℝ × ℝ) × Velocity => p.1))
    have hv := (AxialFlow.clamped_velocity_continuous (σ := σ) hα hγ hμ).measurable.comp
      (measurable_fst : Measurable (fun p : (ℝ × ℝ) × Velocity => p.1))
    have hj : Measurable (fun p : (ℝ × ℝ) × Velocity =>
        PlaneChart.join 0 (AxialFlow.velocity σ α γ μ (max 0 p.1.1) p.1.2)) :=
      VelocityWeight.split.symm.measurable.comp (hv.prodMk measurable_const)
    exact hw.mul ((measurable_snd.sub hj).norm)
  have he : (fun p : (ℝ × ℝ) × Velocity =>
      ∫ w, ‖p.2-w‖ ∂AxialBackground.cell K α γ μ (max 0 p.1.1) p.1.2) =
      (fun p => AxialBackground.weight K α γ μ (max 0 p.1.1) 1 p.1.2 *
        ‖p.2-PlaneChart.join 0 (AxialFlow.velocity 1 α γ μ (max 0 p.1.1) p.1.2)‖ +
        AxialBackground.weight K α γ μ (max 0 p.1.1) (-1) p.1.2 *
        ‖p.2-PlaneChart.join 0 (AxialFlow.velocity (-1) α γ μ (max 0 p.1.1) p.1.2)‖) := by
    funext p
    exact AxialBackground.integral_cell hK hα hγ hμ (le_max_left 0 p.1.1) p.1.2 _
  rw [he]
  exact (ha 1).add (ha (-1))

theorem clamped_frequency_measurable {θ K α γ : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (η l : ℝ) :
    Measurable (fun p : (ℝ × JetPrototype.Space) × Velocity =>
      frequency θ η l K α γ (max 0 p.1.1) p.1.2 p.2) := by
  let f : ℤ × ((ℝ × ℝ) × Velocity) → ℝ := fun p =>
    ∫ w, ‖p.2.2-w‖ ∂AxialBackground.cell K α γ (GeometricMesh.point θ η p.1)
      (max 0 p.2.1.1) p.2.1.2
  have hf : Measurable f := by
    apply measurable_from_prod_countable_right
    intro k
    change Measurable (fun p : (ℝ × ℝ) × Velocity =>
      ∫ w, ‖p.2-w‖ ∂AxialBackground.cell K α γ (GeometricMesh.point θ η k)
        (max 0 p.1.1) p.1.2)
    exact cell_distance_measurable (K := K) (α := α) (γ := γ)
      (μ := GeometricMesh.point θ η k) hK hα hγ (GeometricMesh.point_pos hθ η k)
  have hi : Measurable (fun p : (ℝ × JetPrototype.Space) × Velocity =>
      (GeometricMesh.index (‖p.1.2.1‖/θ) η,((p.1.1,p.1.2.2),p.2))) := by
    unfold GeometricMesh.index
    fun_prop
  have ha : MeasurableSet {p : (ℝ × JetPrototype.Space) × Velocity |
      active θ η l p.1.2.1} :=
    (active_measurableSet θ η l).preimage measurable_fst.snd.fst
  have he : (fun p : (ℝ × JetPrototype.Space) × Velocity =>
      frequency θ η l K α γ (max 0 p.1.1) p.1.2 p.2) =
      (fun p => 2*Real.pi * {p : (ℝ × JetPrototype.Space) × Velocity |
        active θ η l p.1.2.1}.indicator
          (fun p => f (GeometricMesh.index (‖p.1.2.1‖/θ) η,((p.1.1,p.1.2.2),p.2))) p) := by
    funext p
    by_cases hp : active θ η l p.1.2.1 <;> simp [frequency,background,hp,f,scale]
  rw [he]
  exact ((hf.comp hi).indicator ha).const_mul (2*Real.pi)

end BoltzmannNonuniqueness.GeometricBackground

end

end

section

/-! # Gaussian moment of the finite atomic limiting medium -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.GeometricBackground

theorem gaussian_moment_bound {θ η l K α γ t : ℝ}
    (hθ : 0 < θ) (hl : 0 ≤ l) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (ht : 0 < t)
    (x : JetPrototype.Space) :
    (∫⁻ v, ENNReal.ofReal (weight v) ∂background θ η l K α γ t x) ≤
      ENNReal.ofReal (2*((1/4)*((K*max 1 (α*γ)⁻¹)/(l+t)))*
        Real.exp ((1+α)^2/2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_test θ η l K α γ t x weight) (ae_of_all _ (fun v => (weight_pos v).le))]
  apply ENNReal.ofReal_le_ofReal
  apply (le_abs_self _).trans
  classical
  by_cases ha : active θ η l x.1
  · rw [background,ite_eq_left ha]
    apply (AxialBackground.integral_cell_abs_le hK hα hγ (scale_pos hθ η x.1)
      ht.le x.2 weight (C := Real.exp ((1+α)^2/2)) ?_).trans
    · apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one))
        (by linarith) (by linarith [ha.1])
    · intro v hv
      rw [abs_of_pos (weight_pos v)]
      apply Real.exp_le_exp.mpr
      nlinarith [norm_nonneg v]
  · rw [background,ite_eq_right ha,integral_zero_measure,abs_zero]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (mul_nonneg (by norm_num)
        (div_nonneg (mul_nonneg hK (le_max_of_le_left zero_le_one)) (by linarith))))
      (Real.exp_pos _).le

end BoltzmannNonuniqueness.GeometricBackground

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

end BoltzmannNonuniqueness.Cap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CharacteristicCoordinates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrating characteristic test identities in physical spacetime -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem characteristic_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving characteristicEquiv
      (μ.prod (volume : Measure (Velocity × Velocity)))
      ((μ.prod (volume : Measure Velocity)).prod volume) := by
  have hs : MeasurePreserving (fun z : ℝ × (Velocity × Velocity) => (z.1,flight z.1 z.2))
      (μ.prod (volume : Measure (Velocity × Velocity))) (μ.prod volume) :=
    (MeasurePreserving.id μ).skew_product (μc := (volume : Measure (Velocity × Velocity)))
      (μd := (volume : Measure (Velocity × Velocity)))
      (by unfold flight; fun_prop) (ae_of_all _ (fun t => (flight_measurePreserving t).map_eq))
  convert (measurePreserving_prodAssoc μ (volume : Measure Velocity)
    (volume : Measure Velocity)).symm.comp hs using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  rfl

end BoltzmannNonuniqueness.EuclideanFlight

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

section

/-! # Zero extension of rescaled hot densities beyond their physical horizons -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem eventually_extendedHot_eq (S : AttainedCapSequence F) (hs₀ : 0 < s₀)
    {κ : ℕ → ℕ} {U : ℝ≥0∞}
    (hU : Tendsto (fun n => S.normalizedHorizon (κ n)) atTop (𝓝 U))
    {A : ℝ} (hA : ENNReal.ofReal A < U) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) A, ∀ p,
      S.extendedHot (κ n) (t,p) = S.rescaledHot (κ n) (t,p) := by
  filter_upwards [S.eventually_scaled_slab hs₀ hU hA] with n hn
  intro t ht p
  exact indicator_of_mem (show (t,p) ∈ S.hotTimeDomain (κ n) from hn t ht) _

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakTimeLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A locally integrable weakly time-constant function is constant on an interval -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem exists_normalized_test {a b : ℝ} (hab : a < b) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Ioo a b ∧ (∫ t, ρ t) = 1 := by
  let c := (a+b)/2
  let β : ContDiffBump c := ⟨(b-a)/8,(b-a)/4,by linarith,by linarith⟩
  refine ⟨β.normed volume,β.contDiff_normed,β.hasCompactSupport_normed,?_,β.integral_normed⟩
  rw [β.tsupport_normed_eq]
  intro t ht
  rw [Metric.mem_closedBall,Real.dist_eq,abs_le] at ht
  dsimp [β,c] at ht
  constructor <;> linarith [ht.1,ht.2]

theorem weakly_constant_test_integral {a b : ℝ} {f ρ : ℝ → ℝ}
    (hf : LocallyIntegrable f)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Ioo a b) (hρi : (∫ t, ρ t) = 1)
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ t, deriv ψ t*f t) = 0)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ Ioo a b) :
    (∫ t, φ t*f t) = (∫ t, φ t)*(∫ t, ρ t*f t) := by
  let k : ℝ → ℝ := fun t => φ t-(∫ s, φ s)*ρ t
  have hkc : HasCompactSupport k := hφc.sub (hρc.mul_left (f := fun _ => ∫ s, φ s))
  have hks : tsupport k ⊆ Ioo a b :=
    (tsupport_sub φ (fun t => (∫ s, φ s)*ρ t)).trans
      (union_subset hφs (tsupport_mul_subset_right.trans hρs))
  have hki : (∫ t, k t) = 0 := by
    change (∫ t, φ t-(∫ s, φ s)*ρ t) = 0
    rw [integral_sub (hφ.continuous.integrable_of_hasCompactSupport hφc)
        ((hρ.continuous.integrable_of_hasCompactSupport hρc).const_mul _)]
    rw [integral_const_mul,hρi,mul_one,sub_self]
  have hkd : ContDiff ℝ (⊤ : ℕ∞) k := by dsimp only [k]; fun_prop
  obtain ⟨ψ,hψ,hψc,hψs,hψd⟩ := exists_test_primitive hkd hkc hks hki
  have hz := hw ψ hψ hψc hψs
  rw [hψd] at hz
  have hiφ : Integrable (fun t => φ t*f t) :=
    hf.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  have hiρ : Integrable (fun t => ρ t*f t) :=
    hf.integrable_smul_left_of_hasCompactSupport hρ.continuous hρc
  have he : (∫ t, k t*f t) = (∫ t, φ t*f t)-(∫ s, φ s)*(∫ t, ρ t*f t) := by
    calc
      _ = ∫ t, φ t*f t-(∫ s, φ s)*(ρ t*f t) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun t => by dsimp only [k] <;> ring)
      _ = _ := by rw [integral_sub hiφ (hiρ.const_mul _),integral_const_mul]
  linarith

theorem ae_eq_const_of_weak_deriv_zero {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : LocallyIntegrable f)
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ t, deriv ψ t*f t) = 0) :
    ∃ c : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a b → f t = c := by
  obtain ⟨ρ,hρ,hρc,hρs,hρi⟩ := exists_normalized_test hab
  let c := ∫ t, ρ t*f t
  have hcc : LocallyIntegrable (fun _ : ℝ => c) (volume : Measure ℝ) :=
    continuous_const.locallyIntegrable
  have hfc : LocallyIntegrableOn (fun t => f t-c) (Ioo a b) :=
    (hf.sub hcc).locallyIntegrableOn _
  have he := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hfc
    (fun φ hφ hφc hφs => ?_)
  · exact ⟨c,he.mono (fun t ht hmem => sub_eq_zero.mp (ht hmem))⟩
  have hiφ : Integrable (fun t => φ t*f t) :=
    hf.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  have hiφc : Integrable (fun t => φ t*c) (volume : Measure ℝ) :=
    (hφ.continuous.integrable_of_hasCompactSupport hφc).mul_const c
  have hh := weakly_constant_test_integral hf hρ hρc hρs hρi hw hφ hφc hφs
  change (∫ t, φ t*(f t-c)) = 0
  calc
    _ = (∫ t, φ t*f t)-(∫ t, φ t)*c := by
      simp_rw [mul_sub]
      rw [integral_sub hiφ hiφc,integral_mul_const]
    _ = 0 := by change (∫ t, φ t*f t)-(∫ t, φ t)*(∫ t, ρ t*f t) = 0; linarith

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CumulativeIntervalBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A finite source measure and its weak time primitive -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem cumulative_monotone (μ : Measure ℝ) [IsFiniteMeasure μ] : Monotone (cumulative μ) := by
  intro s t hst
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Iic_subset_Iic.mpr hst))

theorem cumulative_locallyIntegrable (μ : Measure ℝ) [IsFiniteMeasure μ] :
    LocallyIntegrable (cumulative μ) := (cumulative_monotone μ).locallyIntegrable

theorem cumulative_weak_derivative (μ : Measure ℝ) [IsFiniteMeasure μ]
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ t, deriv φ t*cumulative μ t) = -(∫ t, φ t ∂μ) := by
  let F : ℝ × ℝ → ℝ := {z : ℝ × ℝ | z.1 ≤ z.2}.indicator (fun z => deriv φ z.2)
  have hi : Integrable (deriv φ) (volume : Measure ℝ) :=
    (hφ.continuous_deriv (by simp)).integrable_of_hasCompactSupport hc.deriv
  have hF : Integrable F (μ.prod volume) :=
    (hi.comp_snd μ).indicator (measurableSet_le measurable_fst measurable_snd)
  have hright (t : ℝ) : (∫ s, F (s,t) ∂μ) = deriv φ t*cumulative μ t := by
    change (∫ s, (Iic t).indicator (fun _ => deriv φ t) s ∂μ) = _
    rw [integral_indicator measurableSet_Iic,integral_const]
    simp only [Measure.real,Measure.restrict_apply MeasurableSet.univ,univ_inter,
      smul_eq_mul,cumulative]
    exact mul_comm _ _
  have hleft (s : ℝ) : (∫ t, F (s,t)) = -φ s := by
    change (∫ t, (Ici s).indicator (deriv φ) t) = _
    rw [integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi]
    exact hc.integral_Ioi_deriv_eq (hφ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) s
  calc
    _ = ∫ t, ∫ s, F (s,t) ∂μ ∂volume := by simp only [hright]
    _ = ∫ s, ∫ t, F (s,t) ∂volume ∂μ :=
      (integral_integral_swap (f := fun s t : ℝ => F (s,t)) hF).symm
    _ = -(∫ s, φ s ∂μ) := by simp only [hleft,integral_neg]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Positive source increments between almost every pair of times -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem cumulative_increment (μ : Measure ℝ) [IsFiniteMeasure μ]
    {s t : ℝ} (hst : s ≤ t) :
    cumulative μ t-cumulative μ s = μ.real (Ioc s t) := by
  rw [cumulative,cumulative,← measureReal_sdiff (Iic_subset_Iic.mpr hst) measurableSet_Iic]
  congr 1
  ext x
  simp only [mem_sdiff,mem_Iic,mem_Ioc,not_le]
  tauto

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakTimeBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reconstructing a time balance from finite gain and loss measures -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem ae_cumulative_balance {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : LocallyIntegrable f) (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b →
      (∫ t, deriv ψ t*f t)+(∫ t, ψ t ∂μ)-(∫ t, ψ t ∂ν) = 0) :
    ∃ c : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a b → f t = c+cumulative μ t-cumulative ν t := by
  let g : ℝ → ℝ := fun t => f t-cumulative μ t+cumulative ν t
  have hg : LocallyIntegrable g :=
    (hf.sub (cumulative_locallyIntegrable μ)).add (cumulative_locallyIntegrable ν)
  have hgw : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioo a b → (∫ t, deriv ψ t*g t) = 0 := by
    intro ψ hψ hc hs
    have hd := hψ.continuous_deriv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hfi : Integrable (fun t => deriv ψ t*f t) :=
      hf.integrable_smul_left_of_hasCompactSupport hd hc.deriv
    have hμi : Integrable (fun t => deriv ψ t*cumulative μ t) :=
      (cumulative_locallyIntegrable μ).integrable_smul_left_of_hasCompactSupport hd hc.deriv
    have hνi : Integrable (fun t => deriv ψ t*cumulative ν t) :=
      (cumulative_locallyIntegrable ν).integrable_smul_left_of_hasCompactSupport hd hc.deriv
    have hisub : Integrable (fun t => deriv ψ t*f t-deriv ψ t*cumulative μ t) := hfi.sub hμi
    have he : (∫ t, deriv ψ t*g t) =
        (∫ t, deriv ψ t*f t)-(∫ t, deriv ψ t*cumulative μ t)+
          (∫ t, deriv ψ t*cumulative ν t) := by
      calc
        _ = ∫ t, (deriv ψ t*f t-deriv ψ t*cumulative μ t)+deriv ψ t*cumulative ν t := by
          apply integral_congr_ae
          exact ae_of_all _ (fun t => by dsimp only [g] <;> ring)
        _ = _ := by rw [integral_add hisub hνi,integral_sub hfi hμi]
    rw [he,cumulative_weak_derivative μ hψ hc,cumulative_weak_derivative ν hψ hc]
    linarith [hw ψ hψ hc hs]
  obtain ⟨c,hc⟩ := ae_eq_const_of_weak_deriv_zero hab hg hgw
  refine ⟨c,hc.mono (fun t ht hmem => ?_)⟩
  have h := ht hmem
  dsimp only [g] at h
  linarith

end BoltzmannNonuniqueness.WeakTime

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TruncatedExponential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded exponential weights on a time slab -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem slabExponential_measurable (a b C : ℝ) : Measurable (slabExponential a b C) :=
  (by fun_prop : Measurable (fun t : ℝ => Real.exp (C*t))).indicator measurableSet_Ioo

theorem slabExponential_nonneg (a b C t : ℝ) : 0 ≤ slabExponential a b C t :=
  indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

theorem slabExponential_bound (a b : ℝ) {C : ℝ} (hC : 0 ≤ C) (t : ℝ) :
    |slabExponential a b C t| ≤ Real.exp (C*b) := by
  by_cases ht : t ∈ Ioo a b
  · rw [slabExponential,indicator_of_mem ht,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2.le hC)
  · rw [slabExponential,indicator_of_notMem ht,abs_zero]
    exact (Real.exp_pos _).le

theorem slabExponential_test {a b C : ℝ} {ψ : ℝ → ℝ}
    (hs : tsupport ψ ⊆ Ioo a b) (t : ℝ) :
    Real.exp (C*t)*ψ t = ψ t*slabExponential a b C t := by
  by_cases ht : t ∈ Ioo a b
  · rw [slabExponential,indicator_of_mem ht,mul_comm]
  · have hz : ψ t = 0 := image_eq_zero_of_notMem_tsupport (fun h => ht (hs h))
    rw [hz,mul_zero,zero_mul]

theorem slabExponential_test_derivative {a b C : ℝ} {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : tsupport ψ ⊆ Ioo a b) (t : ℝ) :
    deriv (fun r => Real.exp (C*r)*ψ r) t =
      deriv ψ t*slabExponential a b C t+C*(ψ t*slabExponential a b C t) := by
  have hd := (((hasDerivAt_id t).const_mul C).exp.mul
    (hψ.differentiable (by simp) t).hasDerivAt).deriv
  change deriv (fun r => Real.exp (C*r)*ψ r) t =
    Real.exp (C*t)*(C*1)*ψ t+Real.exp (C*t)*deriv ψ t at hd
  rw [hd]
  have h₁ := slabExponential_test hs (C := C) t
  have h₂ := slabExponential_test (tsupport_deriv_subset.trans hs) (C := C) t
  nlinarith only [congrArg (fun x : ℝ => C*x) h₁,h₂]

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapLabelFreeLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The exact affine cap passes to the weak hot limit -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem hotWindow_time_mem (A R : ℝ) :
    ∀ᵐ z ∂hotWindowVolume A R, z.1.1 ∈ Icc (0:ℝ) A := by
  exact Measure.quasiMeasurePreserving_fst.ae
    (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotWindowGeometry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Restriction and compatibility of the nested hot-density windows -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

theorem hotWindowSet_measurable (A R : ℝ) : MeasurableSet (hotWindowSet A R) :=
  (measurableSet_Icc.prod measurableSet_closedBall).prod MeasurableSet.univ

theorem hotWindowVolume_eq (A R : ℝ) :
    hotWindowVolume A R = volume.restrict (hotWindowSet A R) := by
  rw [hotWindowVolume,Measure.prod_restrict,← Measure.volume_eq_prod,
    Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod]
  rfl

theorem hotWindowSet_mono {A B R S : ℝ} (hA : A ≤ B) (hR : R ≤ S) :
    hotWindowSet A R ⊆ hotWindowSet B S := by
  rintro z ⟨⟨ht,hx⟩,hv⟩
  exact ⟨⟨⟨ht.1,ht.2.trans hA⟩,Metric.closedBall_subset_closedBall hR hx⟩,hv⟩

theorem hotWindowVolume_restrict {A B R S : ℝ} (hA : A ≤ B) (hR : R ≤ S) :
    (hotWindowVolume B S).restrict (hotWindowSet A R) = hotWindowVolume A R := by
  rw [hotWindowVolume_eq,hotWindowVolume_eq]
  exact Measure.restrict_restrict_of_subset (hotWindowSet_mono hA hR)

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.compatible (E : HotLimitExtraction S) {j k : ℕ} (hjk : j ≤ k) :
    E.profile k =ᵐ[hotWindowVolume (j+1) (j+1)] E.profile j := by
  have hle : (j:ℝ)+1 ≤ (k:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hjk 1
  have hk := (E.weak k).restrict (hotWindowSet_measurable (j+1) (j+1))
  rw [hotWindowVolume_restrict hle hle] at hk
  exact hk.unique (E.weak j)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapHotUndamped
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A single measurable hot limit from the compatible local weak limits -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.hotLimit_measurable (E : HotLimitExtraction S) :
    Measurable E.hotLimit :=
  measurable_const.max (Measurable.liminf (fun j => (E.weak j).1))

theorem HotLimitExtraction.hotLimit_nonneg (E : HotLimitExtraction S) (z : HotKineticPhase) :
    0 ≤ E.hotLimit z := le_max_left _ _

theorem HotLimitExtraction.hotLimit_eq_local (E : HotLimitExtraction S) (j : ℕ) :
    E.hotLimit =ᵐ[hotWindowVolume (j+1) (j+1)] E.profile j := by
  have he (k : ℕ) : ∀ᵐ z ∂hotWindowVolume (j+1) (j+1), j ≤ k → E.profile k z = E.profile j z := by
    by_cases hjk : j ≤ k
    · exact (E.compatible hjk).mono (fun _ hz _ => hz)
    · exact ae_of_all _ (fun _ h => (hjk h).elim)
  filter_upwards [ae_all_iff.mpr he,E.nonneg j] with z hz hn
  have hevent : (fun k => E.profile k z) =ᶠ[atTop] (fun _ => E.profile j z) := by
    filter_upwards [eventually_ge_atTop j] with k hk
    exact hz k hk
  have ht : Tendsto (fun k => E.profile k z) atTop (𝓝 (E.profile j z)) :=
    (tendsto_congr' hevent).mpr tendsto_const_nhds
  exact (congrArg (max (0:ℝ)) ht.liminf_eq).trans (max_eq_right hn)

theorem HotLimitExtraction.hotLimit_weak (E : HotLimitExtraction S) (A R : ℝ) :
    Published.WeakL1Converges (hotWindowVolume A R)
      (fun n => S.hotDensity (E.indices n)) E.hotLimit := by
  obtain ⟨j,hj⟩ := exists_nat_gt (max A R)
  have hA : A ≤ (j:ℝ)+1 := by have := (le_max_left A R).trans_lt hj; linarith
  have hR : R ≤ (j:ℝ)+1 := by have := (le_max_right A R).trans_lt hj; linarith
  have hjw := (E.weak j).congr_limit E.hotLimit_measurable (E.hotLimit_eq_local j).symm
  have h := hjw.restrict (hotWindowSet_measurable A R)
  rw [hotWindowVolume_restrict hA hR] at h
  exact h

theorem HotLimitExtraction.hotLimit_cap (E : HotLimitExtraction S) (A R : ℝ) :
    ∀ᵐ z ∂hotWindowVolume A R, E.hotLimit z ≤ (z.1.1+E.fraction)*H q z.2 := by
  obtain ⟨j,hj⟩ := exists_nat_gt (max A R)
  have hA : A ≤ (j:ℝ)+1 := by have := (le_max_left A R).trans_lt hj; linarith
  have hR : R ≤ (j:ℝ)+1 := by have := (le_max_right A R).trans_lt hj; linarith
  have hb : ∀ᵐ z ∂hotWindowVolume (j+1) (j+1),
      E.hotLimit z ≤ (z.1.1+E.fraction)*H q z.2 := by
    filter_upwards [E.hotLimit_eq_local j,E.cap j] with z he hc
    exact he ▸ hc
  have h := ae_restrict_of_ae (s := hotWindowSet A R) hb
  rw [hotWindowVolume_restrict hA hR] at h
  exact h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

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

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem HotLimitExtraction.physical_weak (S : AttainedCapSequence F)
    (E : HotLimitExtraction S) (hs₀ : 0 < s₀) {A : ℝ}
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    Published.WeakL1Converges (hotWindowVolume A R)
      (fun n => S.physicalHotDensity (E.indices n)) E.hotLimit := by
  apply (E.hotLimit_weak A R).congr_eventually
  filter_upwards [S.eventually_extendedHot_eq hs₀ E.horizon_limit hA] with n hn
  filter_upwards [hotWindow_time_mem A R] with z hz
  exact hn z.1.1 hz (z.1.2,z.2)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot-limit representative and its geometric background bounds -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.cappedHot_measurable (E : HotLimitExtraction S) :
    Measurable E.cappedHot :=
  E.hotLimit_measurable.min ((measurable_const.max (measurable_fst.fst.add_const _)).mul
    ((ChartKernel.measurable_H q).comp measurable_snd))

theorem HotLimitExtraction.cappedHot_nonneg (E : HotLimitExtraction S) (z : HotKineticPhase) :
    0 ≤ E.cappedHot z :=
  le_min (E.hotLimit_nonneg z) (mul_nonneg (le_max_left _ _) (H_nonneg q z.2))

theorem HotLimitExtraction.cappedHot_eq (E : HotLimitExtraction S) (A R : ℝ) :
    E.cappedHot =ᵐ[hotWindowVolume A R] E.hotLimit := by
  filter_upwards [E.hotLimit_cap A R] with z hz
  apply min_eq_left
  exact hz.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (H_nonneg q z.2))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual limiting cold--hot product kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.hotKernel_apply (E : HotLimitExtraction S) (x : ℝ × JetPrototype.Space) :
    E.hotKernel x = volume.withDensity (fun v => ENNReal.ofReal (E.cappedHot (x,v))) := by
  exact Kernel.withDensity_apply _ E.cappedHot_measurable.ennreal_ofReal x

theorem HotLimitExtraction.mixedKernel_apply (E : HotLimitExtraction S) {a : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (x : ℝ × JetPrototype.Space) :
    E.mixedKernel ha hK hα hγ x =
      (E.background (max a x.1) x.2).prod (E.hotKernel x) := by
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  exact Kernel.prod_apply _ _ x

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Finite mixed cold--hot measures on bounded spacetime windows -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.hotKernel_integral (E : HotLimitExtraction S)
    (x : ℝ × JetPrototype.Space) (ψ : Velocity → ℝ) :
    (∫ v, ψ v ∂E.hotKernel x) = ∫ v, E.cappedHot (x,v)*ψ v := by
  rw [E.hotKernel_apply,integral_withDensity_eq_integral_toReal_smul]
  · simp_rw [ENNReal.toReal_ofReal (E.cappedHot_nonneg _),smul_eq_mul]
  · exact (E.cappedHot_measurable.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Product Gaussian moment of the actual limiting mixed measure -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityMoment

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.hotKernel_gaussian_moment (E : HotLimitExtraction S)
    (x : ℝ × JetPrototype.Space) :
    (∫⁻ v, ENNReal.ofReal (weight v) ∂E.hotKernel x) =
      moment (fun v => E.cappedHot (x,v)) := by
  have hm : Measurable (fun v : Velocity => ENNReal.ofReal (E.cappedHot (x,v))) :=
    (E.cappedHot_measurable.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hw : Measurable (fun v : Velocity => ENNReal.ofReal (weight v)) := by unfold weight; fun_prop
  rw [E.hotKernel_apply,lintegral_withDensity_eq_lintegral_mul _ hm hw]
  apply lintegral_congr
  intro v
  rw [Pi.mul_apply,← ENNReal.ofReal_mul (E.cappedHot_nonneg _),mul_comm]

theorem HotLimitExtraction.mixedKernel_gaussian_moment (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (x : ℝ × JetPrototype.Space) :
    (∫⁻ p, ENNReal.ofReal (weight p.1*weight p.2) ∂E.mixedKernel ha hK hα hγ x) =
      (∫⁻ v, ENNReal.ofReal (weight v) ∂E.background (max a x.1) x.2)*
        moment (fun v => E.cappedHot (x,v)) := by
  let _ := GeometricBackground.background_finite E.phase η E.fraction K α γ (max a x.1) x.2
  have hw : Measurable (fun v : Velocity => ENNReal.ofReal (weight v)) := by unfold weight; fun_prop
  rw [E.mixedKernel_apply]
  simp_rw [ENNReal.ofReal_mul (weight_pos _).le]
  rw [lintegral_prod_mul hw.aemeasurable hw.aemeasurable,E.hotKernel_gaussian_moment]

theorem HotLimitExtraction.mixedMeasure_gaussian_bound (E : HotLimitExtraction S)
    {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) (ρ : Measure (ℝ × JetPrototype.Space)) [SFinite ρ]
    (ht : ∀ᵐ x ∂ρ, x.1 ≤ A) :
    (∫⁻ z, ENNReal.ofReal (weight z.2.1*weight z.2.2)
      ∂E.mixedMeasure ha hK hα hγ ρ) ≤
      ENNReal.ofReal ((2*((1/4)*((K*max 1 (α*γ)⁻¹)/a))*
        Real.exp ((1+α)^2/2))*((A+1)*hotConstant q))*ρ univ := by
  rw [mixedMeasure,Measure.lintegral_compProd (by unfold weight; fun_prop)]
  calc
    _ ≤ ∫⁻ _x : ℝ × JetPrototype.Space, ENNReal.ofReal (2*((1/4)*((K*max 1 (α*γ)⁻¹)/a))*
        Real.exp ((1+α)^2/2))*ENNReal.ofReal ((A+1)*hotConstant q) ∂ρ := by
      apply lintegral_mono_ae
      filter_upwards [ht] with x hx
      rw [E.mixedKernel_gaussian_moment ha hK hα hγ]
      apply mul_le_mul'
      · apply (GeometricBackground.gaussian_moment_bound
          (zero_lt_one.trans_le E.phase_mem.1) E.fraction_mem.1 hK hα hγ
          (ha.trans_le (le_max_left a x.1)) x.2).trans
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact div_le_div_of_nonneg_left (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha
          (by linarith [le_max_left a x.1,E.fraction_mem.1])
      · apply (moment_mono (fun v => min_le_right _ _)).trans
        rw [hot_moment hq (le_max_left 0 (x.1+E.fraction))]
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ (hotConstant_nonneg q)
        exact max_le (by linarith) (by linarith [E.fraction_mem.2])
    _ = _ := by
      rw [lintegral_const,← ENNReal.ofReal_mul]
      exact mul_nonneg
        (mul_nonneg (by norm_num) (mul_nonneg (by norm_num)
          (div_nonneg (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha.le)))
        (Real.exp_pos _).le

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ColdCentralVanishing
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The cold cylinders are measurable restrictions of the hot windows -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

theorem cold_spatial_box_eq_ball (R : ℝ) :
    (Metric.closedBall (0 : VelocityWeight.Transverse) R ×ˢ Icc (-R) R) =
      Metric.closedBall (0 : JetPrototype.Space) R := by
  ext x
  simp only [mem_prod,Metric.mem_closedBall,dist_zero_right,mem_Icc]
  change (‖x.1‖ ≤ R ∧ -R ≤ x.2 ∧ x.2 ≤ R) ↔ max ‖x.1‖ ‖x.2‖ ≤ R
  rw [max_le_iff,Real.norm_eq_abs,abs_le]

theorem coldCylinderSet_measurable (a A R : ℝ) : MeasurableSet (coldCylinderSet a A R) :=
  (measurableSet_Icc.prod measurableSet_closedBall).prod MeasurableSet.univ

theorem coldCylinderVolume_eq (a A R : ℝ) :
    (coldCylinderVolume a A R).prod (volume : Measure Velocity) =
      (volume : Measure HotKineticPhase).restrict (coldCylinderSet a A R) := by
  rw [coldCylinderVolume,cold_spatial_box_eq_ball,
    show JetPrototype.spaceVolume = (volume : Measure JetPrototype.Space) from
      (Measure.volume_eq_prod VelocityWeight.Transverse ℝ).symm,
    Measure.prod_restrict,← Measure.volume_eq_prod,
    Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod]
  rfl

theorem coldCylinderVolume_eq_hot_restrict {a A R : ℝ} (ha : 0 ≤ a) :
    (coldCylinderVolume a A R).prod (volume : Measure Velocity) =
      (hotWindowVolume A R).restrict {z | a ≤ z.1.1} := by
  rw [coldCylinderVolume_eq,hotWindowVolume_eq,
    Measure.restrict_restrict (measurableSet_le measurable_const measurable_fst.fst)]
  congr 1
  ext z
  simp only [coldCylinderSet,hotWindowSet,mem_prod,mem_Icc,mem_univ,and_true,
    mem_inter_iff,mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hat,htA⟩,hx⟩
    exact ⟨hat,⟨⟨ha.trans hat,htA⟩,hx⟩⟩
  · rintro ⟨hat,⟨⟨_,htA⟩,hx⟩⟩
    exact ⟨⟨hat,htA⟩,hx⟩

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}

theorem HotLimitExtraction.physical_weak_cylinder (S : AttainedCapSequence F)
    (E : HotLimitExtraction S) (hs₀ : 0 < s₀) {a A : ℝ} (ha : 0 ≤ a)
    (hA : ENNReal.ofReal A < E.horizon) (R : ℝ) :
    Published.WeakL1Converges ((coldCylinderVolume a A R).prod volume)
      (fun n => S.physicalHotDensity (E.indices n)) E.hotLimit := by
  rw [coldCylinderVolume_eq_hot_restrict ha]
  exact (E.physical_weak S hs₀ hA R).restrict
    (measurableSet_le measurable_const measurable_fst.fst)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotChartHomeomorph
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integral transfer between physical cold cylinders and Euclidean hot tests -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem hotChart_global_measurePreserving : MeasurePreserving hotChart volume volume := by
  have hs : MeasurePreserving spaceEquiv (volume : Measure Velocity) volume := by
    convert JetPeriodicDatum.spatialMap_measurePreserving using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact spaceEquiv_apply x
  have hp : MeasurePreserving hotChart
      (((volume : Measure ℝ).prod (volume : Measure Velocity)).prod volume)
      (((volume : Measure ℝ).prod (volume : Measure JetPrototype.Space)).prod volume) :=
    ((MeasurePreserving.id (volume : Measure ℝ)).prod hs).prod
      (MeasurePreserving.id (volume : Measure Velocity))
  convert hp using 1
  all_goals try with_reducible_and_instances rfl

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CharacteristicProductTest
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Time and phase test products in characteristic coordinates -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem timePhaseTest_contDiff {θ : ℝ → ℝ} {φ : Velocity × Velocity → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (timePhaseTest θ φ) :=
  (hθ.comp contDiff_fst).mul (hφ.comp contDiff_snd)

theorem timePhaseTest_support (θ : ℝ → ℝ) (φ : Velocity × Velocity → ℝ) :
    tsupport (timePhaseTest θ φ) ⊆ tsupport θ ×ˢ tsupport φ := by
  apply closure_minimal _ ((isClosed_tsupport θ).prod (isClosed_tsupport φ))
  intro z hz
  change θ z.1*φ z.2 ≠ 0 at hz
  exact ⟨subset_tsupport θ (mul_ne_zero_iff.mp hz).1,
    subset_tsupport φ (mul_ne_zero_iff.mp hz).2⟩

theorem timePhaseTest_compact {θ : ℝ → ℝ} {φ : Velocity × Velocity → ℝ}
    (hθ : HasCompactSupport θ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (timePhaseTest θ φ) :=
  (hθ.isCompact.prod hφ.isCompact).of_isClosed_subset (isClosed_tsupport _)
    (timePhaseTest_support θ φ)

theorem timeDerivative_timePhaseTest {θ : ℝ → ℝ} {φ : Velocity × Velocity → ℝ}
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (z : CharacteristicPhase) : timeDerivative (timePhaseTest θ φ) z = deriv θ z.1*φ z.2 := by
  have h₁ : HasDerivAt (fun s : ℝ => timePhaseTest θ φ (s,z.2))
      (timeDerivative (timePhaseTest θ φ) z) z.1 := by
    exact ((timePhaseTest_contDiff hθ hφ).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z).hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
  exact h₁.unique ((hθ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) z.1).hasDerivAt.mul_const (φ z.2))

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TimeSourceCumulative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite time measures obtained by testing characteristic phase -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeakTime

theorem timeSource_finite (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ]
    {φ : Phase → ℝ} (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p)
    {B : ℝ} (hB : ∀ p, |φ p| ≤ B) : IsFiniteMeasure (timeSource μ φ) := by
  have hi : Integrable (fun z : ℝ × Phase => φ z.2) μ :=
    (integrable_const B).mono' (hφ.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ (fun z => hB _))
  let _ := positiveDensityMeasure_finite hi (ae_of_all _ (fun z => hn z.2))
  unfold timeSource
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem timeSource_integral (μ : Measure (ℝ × Phase)) {φ : Phase → ℝ}
    (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p) {θ : ℝ → ℝ} (hθ : Measurable θ) :
    (∫ t, θ t ∂timeSource μ φ) = ∫ z, θ z.1*φ z.2 ∂μ := by
  rw [timeSource,integral_map measurable_fst.aemeasurable hθ.aestronglyMeasurable]
  have hm : AEMeasurable (fun z : ℝ × Phase => φ z.2) μ :=
    (hφ.comp measurable_snd).aemeasurable
  exact positiveDensityMeasure_integral hm (ae_of_all _ (fun z => hn z.2)) (fun z => θ z.1)

theorem phaseProjection_integrable {F : ℝ × Phase → ℝ}
    (hF : Integrable F (volume : Measure (ℝ × Phase))) {φ : Phase → ℝ}
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ p, |φ p| ≤ B) :
    Integrable (phaseProjection F φ) := by
  have hi := hF.bdd_mul (hφ.comp measurable_snd).aestronglyMeasurable
    (ae_of_all _ (fun z => hB z.2))
  change Integrable (fun t => ∫ p, φ p*F (t,p))
  exact hi.integral_prod_left

theorem phaseProjection_test_integral {F : ℝ × Phase → ℝ}
    (hF : Integrable F (volume : Measure (ℝ × Phase))) {φ : Phase → ℝ}
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ p, |φ p| ≤ B)
    {θ : ℝ → ℝ} (hθ : Measurable θ) {C : ℝ} (hC : ∀ t, |θ t| ≤ C) :
    (∫ t, θ t*phaseProjection F φ t) = ∫ z, (θ z.1*φ z.2)*F z := by
  have hi := hF.bdd_mul (hφ.comp measurable_snd).aestronglyMeasurable
    (ae_of_all _ (fun z => hB z.2))
  have hit := hi.bdd_mul (hθ.comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => hC z.1))
  change Integrable (fun z : ℝ × Phase => θ z.1*(φ z.2*F z))
    ((volume : Measure ℝ).prod volume) at hit
  have hip : Integrable (fun z : ℝ × Phase => (θ z.1*φ z.2)*F z)
      ((volume : Measure ℝ).prod volume) := by
    convert hit using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    ring
  change (∫ t, θ t*phaseProjection F φ t) =
    ∫ z, (θ z.1*φ z.2)*F z ∂(volume : Measure ℝ).prod volume
  rw [integral_prod _ hip]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    simp only [phaseProjection]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun p => by ring))

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PhaseSourceMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Characteristic phase measures and their time-slab increments -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem phaseSlice_finite {F : ℝ × Phase → ℝ} {t : ℝ}
    (hi : Integrable (fun p => F (t,p))) (hn : ∀ᵐ p ∂volume, 0 ≤ F (t,p)) :
    IsFiniteMeasure (phaseSlice F t) := positiveDensityMeasure_finite hi hn

theorem phaseSlice_integral {F : ℝ × Phase → ℝ} {t : ℝ}
    (hm : AEMeasurable (fun p => F (t,p)) volume)
    (hn : ∀ᵐ p ∂volume, 0 ≤ F (t,p)) (φ : Phase → ℝ) :
    (∫ p, φ p ∂phaseSlice F t) = phaseProjection F φ t :=
  positiveDensityMeasure_integral hm hn φ

theorem phaseIncrement_integral (μ : Measure (ℝ × Phase)) (s t : ℝ)
    {φ : Phase → ℝ} (hφ : Measurable φ) :
    (∫ p, φ p ∂phaseIncrement μ s t) =
      ∫ z, (Ioc s t).indicator (fun _ => (1 : ℝ)) z.1*φ z.2 ∂μ := by
  rw [phaseIncrement,integral_map measurable_snd.aemeasurable hφ.aestronglyMeasurable,
    ← integral_indicator (measurable_fst measurableSet_Ioc)]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    by_cases hz : z.1 ∈ Ioc s t <;> simp [hz])

theorem phaseIncrement_timeSource (μ : Measure (ℝ × Phase)) (s t : ℝ)
    {φ : Phase → ℝ} (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p) :
    (∫ p, φ p ∂phaseIncrement μ s t) = (timeSource μ φ).real (Ioc s t) := by
  rw [phaseIncrement_integral μ s t hφ,← integral_indicator_one measurableSet_Ioc]
  exact (timeSource_integral μ hφ hn (measurable_const.indicator measurableSet_Ioc)).symm

end BoltzmannNonuniqueness.WeakTime

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ProjectedTimeBalance
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a phase-tested weak kinetic equation in time -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem projected_cumulative_balance {a b : ℝ} (hab : a < b)
    {F : ℝ × Phase → ℝ} (hF : Integrable F (volume : Measure (ℝ × Phase)))
    {φ : Phase → ℝ} (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p)
    {B : ℝ} (hB : ∀ p, |φ p| ≤ B)
    (μ ν : Measure (ℝ × Phase)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hw : ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
      tsupport θ ⊆ Ioo a b →
      (∫ z, (deriv θ z.1*φ z.2)*F z)+
        (∫ z, θ z.1*φ z.2 ∂μ)-(∫ z, θ z.1*φ z.2 ∂ν) = 0) :
    ∃ c : ℝ, ∀ᵐ t ∂volume, t ∈ Ioo a b →
      phaseProjection F φ t = c+cumulative (timeSource μ φ) t-cumulative (timeSource ν φ) t := by
  let _ := timeSource_finite μ hφ hn hB
  let _ := timeSource_finite ν hφ hn hB
  apply ae_cumulative_balance hab (phaseProjection_integrable hF hφ hB).locallyIntegrable
    (timeSource μ φ) (timeSource ν φ)
  intro θ hθ hc hs
  obtain ⟨C,hC⟩ := (hθ.continuous_deriv (by simp)).bounded_above_of_compact_support hc.deriv
  rw [phaseProjection_test_integral hF hφ hB (hθ.continuous_deriv (by simp)).measurable hC,
    timeSource_integral μ hφ hn hθ.continuous.measurable,
    timeSource_integral ν hφ hn hθ.continuous.measurable]
  exact hw θ hθ hc hs

end BoltzmannNonuniqueness.WeakTime

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakEntropyMarginal
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A common almost-everywhere measure balance from smooth weak tests -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Compactness

namespace BoltzmannNonuniqueness.WeakTime

theorem ae_measure_interval_balance {a b : ℝ} (hab : a < b)
    {F : ℝ × Phase → ℝ} (hi : Integrable F (volume : Measure (ℝ × Phase)))
    (hn : ∀ᵐ z ∂volume, 0 ≤ F z)
    (μ ν : Measure (ℝ × Phase)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hw : ∀ φ : Phase → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ p, 0 ≤ φ p) → ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
      (∫ z, (deriv θ z.1*φ z.2)*F z)+
        (∫ z, θ z.1*φ z.2 ∂μ)-(∫ z, θ z.1*φ z.2 ∂ν) = 0) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      phaseSlice F t+phaseIncrement ν s t = phaseSlice F s+phaseIncrement μ s t := by
  have hscalar (j : ℕ) : ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      phaseProjection F (positivePhaseTest j) t+
        (timeSource ν (positivePhaseTest j)).real (Ioc s t) =
      phaseProjection F (positivePhaseTest j) s+
        (timeSource μ (positivePhaseTest j)).real (Ioc s t) := by
    have hj := positivePhaseTest_smooth j
    have hjc := positivePhaseTest_compact j
    have hjn := positivePhaseTest_nonneg j
    obtain ⟨B,hB⟩ := hj.continuous.bounded_above_of_compact_support hjc
    obtain ⟨c,hc⟩ := projected_cumulative_balance hab hi hj.continuous.measurable hjn hB
      μ ν (hw _ hj hjc hjn)
    let _ := timeSource_finite μ hj.continuous.measurable hjn hB
    let _ := timeSource_finite ν hj.continuous.measurable hjn hB
    filter_upwards [hc] with s hs
    filter_upwards [hc] with t ht
    intro hsa hta hst
    have hμ := cumulative_increment (timeSource μ (positivePhaseTest j)) hst
    have hν := cumulative_increment (timeSource ν (positivePhaseTest j)) hst
    linarith only [hs hsa,ht hta,hμ,hν]
  have hall : ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, ∀ j,
      s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      phaseProjection F (positivePhaseTest j) t+
        (timeSource ν (positivePhaseTest j)).real (Ioc s t) =
      phaseProjection F (positivePhaseTest j) s+
        (timeSource μ (positivePhaseTest j)).real (Ioc s t) := by
    filter_upwards [ae_all_iff.mpr hscalar] with s hs
    exact ae_all_iff.mpr hs
  have hif : ∀ᵐ t ∂volume, Integrable (fun p => F (t,p)) := hi.prod_right_ae
  have hnf : ∀ᵐ t ∂volume, ∀ᵐ p ∂volume, 0 ≤ F (t,p) := Measure.ae_ae_of_ae_prod hn
  filter_upwards [hall,hif,hnf] with s hs his hns
  filter_upwards [hs,hif,hnf] with t ht hit hnt
  intro hsa hta hst
  let _ := phaseSlice_finite his hns
  let _ := phaseSlice_finite hit hnt
  apply finite_phase_measure_eq_of_countable_tests
  intro j
  have hj := positivePhaseTest_smooth j
  have hjc := positivePhaseTest_compact j
  have hi' (m : Measure Phase) [IsFiniteMeasure m] : Integrable (positivePhaseTest j) m :=
    hj.continuous.integrable_of_hasCompactSupport hjc
  rw [integral_add_measure (hi' _) (hi' _),integral_add_measure (hi' _) (hi' _),
    phaseSlice_integral hit.aemeasurable hnt,phaseSlice_integral his.aemeasurable hns,
    phaseIncrement_timeSource ν s t hj.continuous.measurable (positivePhaseTest_nonneg j),
    phaseIncrement_timeSource μ s t hj.continuous.measurable (positivePhaseTest_nonneg j)]
  exact ht j hsa hta hst

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HotPositiveRegion
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Cylinder densities and source measures in characteristic coordinates -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem hotCharacteristic_measurePreserving :
    MeasurePreserving hotCharacteristicEquiv volume volume :=
  hotChart_global_measurePreserving.comp (characteristic_measurePreserving volume)

theorem cylinderPullback_integrable {a A R : ℝ}
    {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ}
    (hf : Integrable f ((JetCopyDatum.AttainedCapSequence.coldCylinderVolume a A R).prod volume)) :
    Integrable (cylinderPullback a A R f) volume := by
  rw [JetCopyDatum.AttainedCapSequence.coldCylinderVolume_eq] at hf
  exact hotCharacteristic_measurePreserving.integrable_comp_of_integrable
    ((integrable_indicator_iff
      (JetCopyDatum.AttainedCapSequence.coldCylinderSet_measurable a A R)).mpr hf)

theorem cylinderPullback_integral (a A R : ℝ)
    (f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ)
    (ψ : CharacteristicPhase → ℝ) :
    (∫ u, ψ u*cylinderPullback a A R f u) =
      ∫ z, ψ (hotCharacteristicEquiv.symm z)*f z
        ∂(JetCopyDatum.AttainedCapSequence.coldCylinderVolume a A R).prod volume := by
  rw [JetCopyDatum.AttainedCapSequence.coldCylinderVolume_eq,
    ← integral_indicator (JetCopyDatum.AttainedCapSequence.coldCylinderSet_measurable a A R),
    ← hotCharacteristic_measurePreserving.integral_comp']
  apply integral_congr_ae
  exact ae_of_all _ (fun u => by
    simp only [Function.comp_def,cylinderPullback]
    by_cases hu : hotCharacteristicEquiv u ∈ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R
    · simp only [indicator_of_mem hu,MeasurableEquiv.symm_apply_apply]
    · simp only [indicator_of_notMem hu,mul_zero])

theorem sourcePullback_integral (μ : Measure JetCopyDatum.AttainedCapSequence.HotKineticPhase)
    {ψ : CharacteristicPhase → ℝ} (hψ : Measurable ψ) :
    (∫ u, ψ u ∂sourcePullback μ) = ∫ z, ψ (hotCharacteristicEquiv.symm z) ∂μ := by
  exact integral_map hotCharacteristicEquiv.symm.measurable.aemeasurable hψ.aestronglyMeasurable

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LargeOutput
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LateBoxAccessMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive mass with the entry velocities eventually reaches the growing box -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem bounded_flight_lateBox {κ d a X : ℝ} (hκ : 0 < κ) (hd : 0 < d)
    (ha : 0 ≤ a) :
    ∃ T : ℝ, a ≤ T ∧ 0 < T ∧ ∀ (x v : V), ‖x‖ ≤ X →
      ‖v-κ • firstAxis‖ < d*κ/4 → ‖v‖ < 5 → ∀ t, T ≤ t →
        (x+(t-a) • v,v) ∈ lateBox κ d t := by
  let R := X+κ*a
  let T := max (max a 1) (4*R/(d*κ)+1)
  have hdk : 0 < d*κ := mul_pos hd hκ
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    ((le_max_right a 1).trans (le_max_left _ _))
  refine ⟨T,(le_max_left a 1).trans (le_max_left _ _),hT,?_⟩
  intro x v hx hv hv₅ t ht
  have hta : a ≤ t := ((le_max_left a 1).trans (le_max_left _ _)).trans ht
  have htt : 0 < t := hT.trans_le ht
  have hR : R < d*κ*t/4 := by
    have hlarge : 4*R/(d*κ)+1 ≤ t := (le_max_right _ _).trans ht
    have hdiv := (div_lt_iff₀ hdk).mp (show 4*R/(d*κ) < t by linarith)
    linarith
  have hxR : ‖x-(κ*a) • firstAxis‖ ≤ R := by
    have hb := norm_sub_le x ((κ*a) • firstAxis)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hκ.le ha),axis_norms.1,mul_one] at hb
    exact hb.trans (show ‖x‖+κ*a ≤ R from add_le_add hx le_rfl)
  have he : x+(t-a) • v-(κ*t) • firstAxis =
      (x-(κ*a) • firstAxis)+(t-a) • (v-κ • firstAxis) := by module
  refine ⟨?_,hv₅⟩
  change ‖x+(t-a) • v-(κ*t) • firstAxis‖ < d*κ*t
  rw [he]
  have hn := norm_add_le (x-(κ*a) • firstAxis) ((t-a) • (v-κ • firstAxis))
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hta)] at hn
  have hm : (t-a)*‖v-κ • firstAxis‖ ≤ (t-a)*(d*κ/4) :=
    mul_le_mul_of_nonneg_left hv.le (sub_nonneg.mpr hta)
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapActualLossDensity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite collision measures for the actual limiting cold–hot background -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.incomingRate_integrable (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) :
    Integrable incomingRate (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)) := by
  have ht : ∀ᵐ x ∂coldCylinderVolume a A R, x.1 ≤ A :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
      (fun _ hx => hx.2)
  have hm := E.mixedMeasure_gaussian_bound ha hA hK hα hγ hq (coldCylinderVolume a A R) ht
  apply incomingRate_integrable_of_gaussian
  apply hm.trans_lt
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem HotLimitExtraction.incomingGainMeasure_finite (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) :
    IsFiniteMeasure (incomingGainMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) := by
  let _ : SFinite (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)) := by
    unfold HotLimitExtraction.mixedMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact CollisionCompactness.incomingGainMeasure_finite (E.incomingRate_integrable ha hA hK hα hγ hq)

theorem HotLimitExtraction.incomingLossMeasure_finite (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) :
    IsFiniteMeasure (incomingLossMeasure (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) := by
  let _ : SFinite (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)) := by
    unfold HotLimitExtraction.mixedMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  exact CollisionCompactness.incomingLossMeasure_finite (E.incomingRate_integrable ha hA hK hα hγ hq)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Integrability of the actual limiting attenuation density -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem slab_frequency_measurable {a θ K α γ : ℝ}
    (ha : 0 < a) (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (η l : ℝ) :
    Measurable (fun z : (ℝ × JetPrototype.Space) × Velocity =>
      frequency θ η l K α γ (max a z.1.1) z.1.2 z.2) := by
  have hm := (clamped_frequency_measurable hθ hK hα hγ η l).comp
    (show Measurable (fun z : (ℝ × JetPrototype.Space) × Velocity =>
      ((max a z.1.1,z.1.2),z.2)) from by fun_prop)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  change frequency θ η l K α γ (max a z.1.1) z.1.2 z.2 =
    frequency θ η l K α γ (max 0 (max a z.1.1)) z.1.2 z.2
  rw [max_eq_right (ha.le.trans (le_max_left a z.1.1))]

end BoltzmannNonuniqueness.GeometricBackground

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.loss_density_integrable (E : HotLimitExtraction S)
    {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) (μ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure μ]
    (ht : ∀ᵐ x ∂μ, x.1 ≤ A) :
    Integrable (fun z : HotKineticPhase => E.cappedHot z*
      GeometricBackground.frequency E.phase η E.fraction K α γ (max a z.1.1) z.1.2 z.2)
      (μ.prod volume) := by
  have hv : Integrable (fun v : Velocity => (‖v‖+1+α)*H q v) := by
    convert (integrable_moment_H hq 1).add ((integrable_H hq).const_mul (1+α)) using 1
    all_goals try with_reducible_and_instances rfl
    funext v
    simp only [pow_one,Pi.add_apply]
    ring
  let C := (A+1)*(GeometricBackground.lossCoefficient K α γ/a)
  have hm := E.cappedHot_measurable.mul (GeometricBackground.slab_frequency_measurable ha
    (zero_lt_one.trans_le E.phase_mem.1) hK hα.le hγ.le η E.fraction)
  apply ((hv.const_mul C).comp_snd μ).mono' hm.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ht] with z hz
  have hc : E.cappedHot z ≤ (A+1)*H q z.2 := by
    apply (min_le_right _ _).trans
    apply mul_le_mul_of_nonneg_right _ (H_nonneg q z.2)
    exact max_le (by linarith) (by linarith [E.fraction_mem.2])
  have hf := GeometricBackground.frequency_slab_bound (η := η)
    (zero_lt_one.trans_le E.phase_mem.1) E.fraction_mem.1 hK hα hγ ha
    (le_max_left a z.1.1) z.1.2 z.2
  simp only [Pi.mul_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (E.cappedHot_nonneg z)
    (GeometricBackground.frequency_nonneg _ _ _ _ _ _ _ _ _))]
  calc
    _ ≤ ((A+1)*H q z.2)*((GeometricBackground.lossCoefficient K α γ/a)*(‖z.2‖+1+α)) :=
      mul_le_mul hc hf (GeometricBackground.frequency_nonneg _ _ _ _ _ _ _ _ _)
        (mul_nonneg (by linarith) (H_nonneg q z.2))
    _ = _ := by dsimp only [C] <;> ring

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual atomic-background loss measure has the expected density -/

noncomputable section

open MeasureTheory ProbabilityTheory
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.loss_measure_density_integral (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (μ : Measure (ℝ × JetPrototype.Space)) [SFinite μ]
    (hi : Integrable incomingRate (E.mixedMeasure ha hK hα hγ μ))
    {ψ : HotKineticPhase → ℝ} (hψ : Measurable ψ) {B : ℝ} (hB : ∀ z, |ψ z| ≤ B) :
    (∫ z, ψ z ∂incomingLossMeasure (E.mixedMeasure ha hK hα hγ μ)) =
      ∫ x, ∫ v, ψ (x,v)*E.cappedHot (x,v)*
        GeometricBackground.frequency E.phase η E.fraction K α γ (max a x.1) x.2 v ∂volume ∂μ := by
  let _ : SFinite (E.mixedMeasure ha hK hα hγ μ) := by
    unfold HotLimitExtraction.mixedMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have htest : Measurable (fun z : (ℝ × JetPrototype.Space) × (Velocity × Velocity) =>
      ψ (z.1,z.2.2)) := hψ.comp (measurable_fst.prodMk measurable_snd.snd)
  have hF : Integrable (fun z => incomingRate z*ψ (z.1,z.2.2))
      (E.mixedMeasure ha hK hα hγ μ) := by
    simpa only [mul_comm] using hi.bdd_mul htest.aestronglyMeasurable (ae_of_all _ (fun z => hB _))
  rw [incomingLossMeasure_rate_integral hi hψ hB]
  unfold HotLimitExtraction.mixedMeasure at hF ⊢
  rw [Measure.integral_compProd hF]
  apply integral_congr_ae
  filter_upwards [(Measure.integrable_compProd_iff hF.aestronglyMeasurable).mp hF |>.1] with x hx
  let _ : IsFiniteMeasure (E.background (max a x.1) x.2) :=
    GeometricBackground.background_finite E.phase η E.fraction K α γ (max a x.1) x.2
  rw [E.mixedKernel_apply] at hx ⊢
  rw [integral_prod_symm _ hx,E.hotKernel_integral]
  apply integral_congr_ae
  filter_upwards [] with v
  simp only [incomingRate]
  rw [integral_mul_const,integral_const_mul]
  simp only [norm_sub_rev]
  unfold GeometricBackground.frequency HotLimitExtraction.background
  ring

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Attenuation density on the actual positive-time cylinder -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.loss_measure_product_integral (E : HotLimitExtraction S)
    {a A : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) (μ : Measure (ℝ × JetPrototype.Space)) [IsFiniteMeasure μ]
    (ht : ∀ᵐ x ∂μ, x.1 ≤ A)
    (hiR : Integrable incomingRate (E.mixedMeasure ha hK hα hγ μ))
    {ψ : HotKineticPhase → ℝ}
    (hψ : Measurable ψ) {B : ℝ} (hB : ∀ z, |ψ z| ≤ B) :
    (∫ z, ψ z ∂incomingLossMeasure (E.mixedMeasure ha hK hα hγ μ)) =
      ∫ z, ψ z*E.cappedHot z*
        GeometricBackground.frequency E.phase η E.fraction K α γ (max a z.1.1) z.1.2 z.2
        ∂μ.prod volume := by
  have hi := E.loss_density_integrable ha hA hK hα hγ hq μ ht
  have hip : Integrable (fun z => ψ z*E.cappedHot z*
      GeometricBackground.frequency E.phase η E.fraction K α γ (max a z.1.1) z.1.2 z.2)
      (μ.prod volume) := by
    simpa only [mul_assoc] using hi.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hB)
  rw [E.loss_measure_density_integral ha hK hα hγ μ hiR hψ hB,integral_prod _ hip]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The limiting loss is hot density times the atomic-background frequency -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.loss_cylinder_ae (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 ≤ a) :
    (fun z : HotKineticPhase => E.cappedHot z*
      GeometricBackground.frequency E.phase η E.fraction K α γ (max a z.1.1) z.1.2 z.2)
    =ᵐ[(coldCylinderVolume a A R).prod volume]
      (fun z => E.hotLimit z*GeometricBackground.frequency E.phase η E.fraction K α γ
        z.1.1 z.1.2 z.2) := by
  have ht : ∀ᵐ x ∂coldCylinderVolume a A R, a ≤ x.1 :=
    (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
      (fun _ hx => hx.1)
  have he : E.cappedHot =ᵐ[(coldCylinderVolume a A R).prod volume] E.hotLimit := by
    rw [coldCylinderVolume_eq_hot_restrict ha]
    exact (E.cappedHot_eq A R).filter_mono ae_restrict_le
  filter_upwards [he,Measure.quasiMeasurePreserving_fst.ae ht] with z hz ht
  rw [hz,max_eq_right ht]

theorem HotLimitExtraction.actual_loss_cylinder_integrable (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) :
    Integrable (fun z : HotKineticPhase => E.hotLimit z*
      GeometricBackground.frequency E.phase η E.fraction K α γ z.1.1 z.1.2 z.2)
      ((coldCylinderVolume a A R).prod volume) := by
  apply (E.loss_density_integrable ha (ha.le.trans haA) hK hα hγ hq
    (coldCylinderVolume a A R) ?_).congr (E.loss_cylinder_ae ha.le)
  exact (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
    (fun _ hx => hx.2)

theorem HotLimitExtraction.actual_loss_cylinder_integral (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) {ψ : HotKineticPhase → ℝ}
    (hψ : Measurable ψ) {B : ℝ} (hB : ∀ z, |ψ z| ≤ B) :
    (∫ z, ψ z ∂incomingLossMeasure
      (E.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) =
      ∫ z, ψ z*(E.hotLimit z*GeometricBackground.frequency E.phase η E.fraction K α γ
        z.1.1 z.1.2 z.2) ∂(coldCylinderVolume a A R).prod volume := by
  rw [E.loss_measure_product_integral ha (ha.le.trans haA) hK hα hγ hq
    (coldCylinderVolume a A R)
    ((Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).mono
      (fun _ hx => hx.2))
    (E.incomingRate_integrable ha (ha.le.trans haA) hK hα hγ hq) hψ hB]
  apply integral_congr_ae
  filter_upwards [E.loss_cylinder_ae (R := R) (A := A) ha.le] with z hz
  rw [mul_assoc,hz]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CharacteristicPhysicalGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A common characteristic cylinder for tests in one compact phase set -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem exists_timePhase_cylinder_for_support (a A : ℝ) {β : Velocity × Velocity → ℝ}
    (hc : HasCompactSupport β) :
    ∃ R Rₑ : ℝ, 0 ≤ R ∧ ∀ (φ : Velocity × Velocity → ℝ), tsupport φ ⊆ tsupport β →
      ∀ (θ : ℝ → ℝ), tsupport θ ⊆ Ioo a A →
        tsupport (testPullback (timePhaseTest θ φ)) ⊆ kineticWindow a A Rₑ ∧
        (∀ z ∈ tsupport (testPullback (timePhaseTest θ φ)),
          hotChart z ∈ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R) := by
  let C := Icc a A ×ˢ tsupport β
  have hC : IsCompact C := isCompact_Icc.prod hc.isCompact
  have hE := hC.image characteristicHomeomorph.continuous
  have hH := hE.image hotHomeomorph.continuous
  obtain ⟨Rₑ,hRₑ⟩ := hE.isBounded.exists_norm_le
  obtain ⟨R,hR,hRb⟩ := hH.isBounded.exists_pos_norm_le
  refine ⟨R,Rₑ,hR.le,?_⟩
  intro φ hφ θ hs
  have hsub : tsupport (testPullback (timePhaseTest θ φ)) ⊆ characteristicEquiv.symm ⁻¹' C := by
    apply closure_minimal _ ((isClosed_Icc.prod (isClosed_tsupport β)).preimage
      characteristicHomeomorph.symm.continuous)
    intro z hz
    have hp := timePhaseTest_support θ φ (subset_tsupport _ hz)
    exact ⟨⟨(hs hp.1).1.le,(hs hp.1).2.le⟩,hφ hp.2⟩
  have himg (z) (hz : z ∈ tsupport (testPullback (timePhaseTest θ φ))) :
      z ∈ characteristicHomeomorph '' C :=
    ⟨characteristicEquiv.symm z,hsub hz,characteristicEquiv.apply_symm_apply z⟩
  constructor
  · intro z hz
    have ht := (hsub hz).1
    have hn : ‖z‖ ≤ Rₑ := hRₑ _ (himg z hz)
    exact ⟨⟨ht,(Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using (norm_snd_le z.1).trans ((norm_fst_le z).trans hn)))⟩,
      mem_univ _⟩
  · intro z hz
    have ht := (hsub hz).1
    have hn : ‖hotChart z‖ ≤ R := hRb _ ⟨z,himg z hz,rfl⟩
    exact ⟨⟨ht,(Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using
        (norm_snd_le (hotChart z).1).trans ((norm_fst_le (hotChart z)).trans hn)))⟩,
      mem_univ _⟩

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Removing a spatial cylinder from compactly phase-tested characteristics -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff
open BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem coldCylinderSet_mono_radius {a A R S : ℝ} (hRS : R ≤ S) :
    coldCylinderSet a A R ⊆ coldCylinderSet a A S := by
  intro z hz
  exact ⟨⟨hz.1.1,Metric.closedBall_subset_closedBall hRS hz.1.2⟩,hz.2⟩

theorem exists_phase_cylinder (a A : ℝ) {φ : Velocity × Velocity → ℝ}
    (hc : HasCompactSupport φ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc a A, ∀ p ∈ tsupport φ,
      hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R := by
  have hm : Continuous hotCharacteristicEquiv :=
    hotHomeomorph.continuous.comp characteristicHomeomorph.continuous
  obtain ⟨R,hR,hRb⟩ := ((isCompact_Icc.prod hc.isCompact).image hm).isBounded.exists_pos_norm_le
  refine ⟨R,hR.le,?_⟩
  intro t ht p hp
  have hb : ‖hotCharacteristicEquiv (t,p)‖ ≤ R := hRb _ ⟨(t,p),⟨ht,hp⟩,rfl⟩
  refine ⟨⟨ht,?_⟩,mem_univ _⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (norm_snd_le (hotCharacteristicEquiv (t,p)).1).trans
    ((norm_fst_le (hotCharacteristicEquiv (t,p))).trans hb)

end BoltzmannNonuniqueness.EuclideanFlight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapLimitTransport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual weak-balance cylinder also covers the full compact phase support -/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.covered_characteristic_weak_balance
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon)
    {β : Velocity × Velocity → ℝ} (hβc : HasCompactSupport β) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport β, hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ φ : WeakTime.Phase → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → (∀ p, 0 ≤ φ p) →
      tsupport φ ⊆ tsupport β → ∀ θ : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ → tsupport θ ⊆ Ioo a A →
      (∫ z, (deriv θ z.1*φ z.2)*cylinderPullback a A R E.hotLimit z)+
      (∫ z, θ z.1*φ z.2 ∂E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R)-
      (∫ z, θ z.1*φ z.2 ∂E.toHotLimitExtraction.characteristicLossMeasure ha hK hα hγ A R) = 0 := by
  obtain ⟨R₀,Rₑ,hR₀,hloc⟩ := exists_timePhase_cylinder_for_support a A hβc
  obtain ⟨R₁,_hR₁,hcover⟩ := exists_phase_cylinder a A hβc
  let R := max R₀ R₁
  have hR : 0 ≤ R := hR₀.trans (le_max_left _ _)
  refine ⟨R,hR,?_,?_⟩
  · intro t ht p hp
    exact coldCylinderSet_mono_radius (le_max_right _ _) (hcover t ht p hp)
  intro φ hφ hc _hn hφβ θ hθ hθc hθs
  have hlocθ := hloc φ hφβ θ hθs
  have hcoverθ : ∀ z ∈ tsupport (testPullback (timePhaseTest θ φ)),
      hotChart z ∈ coldCylinderSet a A R := fun z hz =>
    coldCylinderSet_mono_radius (le_max_left _ _) (hlocθ.2 z hz)
  have hb := E.characteristic_test_balance_q80 hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK hα
    hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA.le hAB hB hR
    (timePhaseTest_contDiff hθ hφ) (timePhaseTest_compact hθc hc) hlocθ.1 hcoverθ
  simp_rw [timeDerivative_timePhaseTest hθ hφ] at hb
  rw [cylinderPullback_integral]
  have hm : Measurable (fun z : CharacteristicPhase => θ z.1*φ z.2) :=
    (hθ.continuous.measurable.comp measurable_fst).mul
      (hφ.continuous.measurable.comp measurable_snd)
  change _ + (∫ z, θ z.1*φ z.2 ∂((2 : ℝ≥0) • sourcePullback _))-
    (∫ z, θ z.1*φ z.2 ∂sourcePullback _) = 0
  rw [integral_smul_nnreal_measure,sourcePullback_integral _ hm,sourcePullback_integral _ hm]
  change (∫ z, (deriv θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2)*
      E.hotLimit z ∂(coldCylinderVolume a A R).prod volume)+
    (2*(∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingGainMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))))-
    (∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingLossMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))) = 0
  change (∫ z, (deriv θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2)*
      E.hotLimit z ∂(coldCylinderVolume a A R).prod volume)+
    ((2*(∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingGainMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R))))-
    (∫ z, θ (hotCharacteristicEquiv.symm z).1*φ (hotCharacteristicEquiv.symm z).2
      ∂incomingLossMeasure (E.toHotLimitExtraction.mixedMeasure ha hK hα hγ (coldCylinderVolume a A R)))) = 0 at hb
  linarith only [hb]


end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

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

/-! # Constant damping exposes a positive measure source -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.WeakTime

theorem timeWeightedDensity_integrable {a b C : ℝ} (hC : 0 ≤ C)
    {F : ℝ × Phase → ℝ} (hi : Integrable F) : Integrable (timeWeightedDensity a b C F) :=
  hi.bdd_mul ((slabExponential_measurable a b C).comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => slabExponential_bound a b hC z.1))

theorem timeWeightedSource_finite (a b : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ] : IsFiniteMeasure (timeWeightedSource a b C μ) := by
  apply positiveDensityMeasure_finite
  · exact (integrable_const (Real.exp (C*b))).mono'
      ((slabExponential_measurable a b C).comp measurable_fst).aestronglyMeasurable
      (ae_of_all _ (fun z => slabExponential_bound a b hC z.1))
  · exact ae_of_all _ (fun z => slabExponential_nonneg a b C z.1)

private theorem time_phase_integrable {F : ℝ × Phase → ℝ} (hi : Integrable F)
    {φ : Phase → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ)
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθc : HasCompactSupport θ) :
    Integrable (fun z => (θ z.1*φ z.2)*F z) := by
  obtain ⟨B,hB⟩ := hφ.bounded_above_of_compact_support hc
  obtain ⟨D,hD⟩ := hθ.bounded_above_of_compact_support hθc
  have hp := hi.bdd_mul (hφ.measurable.comp measurable_snd).aestronglyMeasurable
    (ae_of_all _ (fun z => hB z.2))
  simpa only [mul_assoc,Function.comp_def] using hp.bdd_mul
    (hθ.measurable.comp measurable_fst).aestronglyMeasurable (ae_of_all _ (fun z => hD z.1))

theorem ae_damped_measure_interval_balance {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C)
    {F L : ℝ × Phase → ℝ} (hi : Integrable F (volume : Measure (ℝ × Phase)))
    (hL : Integrable L (volume : Measure (ℝ × Phase))) (hn : ∀ᵐ z ∂volume, 0 ≤ F z)
    (hbound : ∀ᵐ z ∂volume, z.1 ∈ Ioo a b → L z ≤ C*F z)
    (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ]
    (hw : ∀ φ : Phase → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ p, 0 ≤ φ p) → ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
      (∫ z, (deriv θ z.1*φ z.2)*F z)+
        (∫ z, θ z.1*φ z.2 ∂μ)-(∫ z, (θ z.1*φ z.2)*L z) = 0) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      phaseSlice (timeWeightedDensity a b C F) t =
        phaseSlice (timeWeightedDensity a b C F) s+
          phaseIncrement (timeWeightedSource a b C μ+
            positiveDensityMeasure volume (dampedResidual a b C F L)) s t := by
  let W := slabExponential a b C
  let r := dampedResidual a b C F L
  have hW : Measurable W := slabExponential_measurable a b C
  have hr : Integrable r := timeWeightedDensity_integrable hC ((hi.const_mul C).sub hL)
  have hrn : ∀ᵐ z ∂volume, 0 ≤ r z := by
    filter_upwards [hbound] with z hz
    by_cases hm : z.1 ∈ Ioo a b
    · exact mul_nonneg (slabExponential_nonneg a b C z.1) (sub_nonneg.mpr (hz hm))
    · simp [r,dampedResidual,slabExponential,hm]
  let _ := positiveDensityMeasure_finite hr hrn
  let _ := timeWeightedSource_finite a b hC μ
  let ρ := timeWeightedSource a b C μ+positiveDensityMeasure volume r
  have hFi := timeWeightedDensity_integrable (a := a) (b := b) hC hi
  have hFn : ∀ᵐ z ∂volume, 0 ≤ timeWeightedDensity a b C F z :=
    hn.mono (fun z hz => mul_nonneg (slabExponential_nonneg a b C z.1) hz)
  have hb := ae_measure_interval_balance hab hFi hFn ρ 0 ?_
  · simpa only [phaseIncrement,Measure.restrict_zero,Measure.map_zero,add_zero] using hb
  intro φ hφ hc hφn ψ hψ hψc hψs
  let θ : ℝ → ℝ := fun t => Real.exp (C*t)*ψ t
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := by dsimp only [θ]; fun_prop
  have hθc : HasCompactSupport θ := hψc.mul_left
  have hθs : tsupport θ ⊆ Ioo a b := tsupport_mul_subset_right.trans hψs
  have hθeq (t : ℝ) : θ t = ψ t*W t := slabExponential_test hψs t
  have hdθ (t : ℝ) : deriv θ t = deriv ψ t*W t+C*(ψ t*W t) :=
    slabExponential_test_derivative hψ hψs t
  have hleft := time_phase_integrable hi hφ.continuous hc
    (hθ.continuous_deriv (by simp)) hθc.deriv
  have hloss := time_phase_integrable hL hφ.continuous hc hθ.continuous hθc
  have hright := time_phase_integrable hFi hφ.continuous hc
    (hψ.continuous_deriv (by simp)) hψc.deriv
  have hres := time_phase_integrable hr hφ.continuous hc hψ.continuous hψc
  have he : (∫ z, (deriv θ z.1*φ z.2)*F z)-(∫ z, (θ z.1*φ z.2)*L z) =
      (∫ z, (deriv ψ z.1*φ z.2)*timeWeightedDensity a b C F z)+
      (∫ z, (ψ z.1*φ z.2)*r z) := by
    rw [← integral_sub hleft hloss,← integral_add hright hres]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      dsimp only
      rw [hdθ,hθeq]
      dsimp only [timeWeightedDensity,r,dampedResidual,W]
      ring)
  have htest (m : Measure (ℝ × Phase)) [IsFiniteMeasure m] :
      Integrable (fun z : ℝ × Phase => ψ z.1*φ z.2) m :=
    (timePhaseTest_contDiff hψ hφ).continuous.integrable_of_hasCompactSupport
      (timePhaseTest_compact hψc hc)
  have hWm : AEMeasurable (fun z : ℝ × Phase => W z.1) μ := by
    simpa only [Function.comp_def] using (hW.comp measurable_fst).aemeasurable (μ := μ)
  have hh := hw φ hφ hc hφn θ hθ hθc hθs
  have hμeq : (∫ z, θ z.1*φ z.2 ∂μ) = ∫ z, (ψ z.1*φ z.2)*W z.1 ∂μ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by dsimp only; rw [hθeq]; ring)
  rw [hμeq] at hh
  simp only [integral_zero_measure,sub_zero]
  change _+(∫ z, ψ z.1*φ z.2 ∂(timeWeightedSource a b C μ+positiveDensityMeasure volume r)) = 0
  rw [integral_add_measure (htest _) (htest _)]
  change _+((∫ z, ψ z.1*φ z.2 ∂positiveDensityMeasure μ (fun z => W z.1))+
    (∫ z, ψ z.1*φ z.2 ∂positiveDensityMeasure volume r)) = 0
  rw [positiveDensityMeasure_integral hWm
      (ae_of_all _ (fun z => slabExponential_nonneg a b C z.1)),
    positiveDensityMeasure_integral hr.aemeasurable hrn]
  linarith only [he,hh]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Removing the exponential weight from a positive measure balance -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

theorem positiveDensityMeasure_const_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    positiveDensityMeasure μ (fun x => c*f x) = ENNReal.ofReal c • positiveDensityMeasure μ f := by
  unfold positiveDensityMeasure
  have he : (fun x => ENNReal.ofReal (c*f x)) = ENNReal.ofReal c • (fun x => ENNReal.ofReal (f x)) := by
    funext x
    exact ENNReal.ofReal_mul hc
  rw [he]
  exact withDensity_smul' _ _ ENNReal.ofReal_ne_top

theorem timeWeighted_phaseSlice (a b C : ℝ) (F : ℝ × Phase → ℝ) (t : ℝ) :
    phaseSlice (timeWeightedDensity a b C F) t =
      ENNReal.ofReal (slabExponential a b C t) • phaseSlice F t := by
  change positiveDensityMeasure volume (fun p : Phase => slabExponential a b C t*F (t,p)) =
    ENNReal.ofReal (slabExponential a b C t) • positiveDensityMeasure volume (fun p => F (t,p))
  exact positiveDensityMeasure_const_mul (X := Phase) volume (fun p => F (t,p))
    (c := slabExponential a b C t) (slabExponential_nonneg a b C t)

theorem undamp_measure_balance {a b C s t : ℝ} (F : ℝ × Phase → ℝ)
    (μ : Measure Phase) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (h : phaseSlice (timeWeightedDensity a b C F) t =
      phaseSlice (timeWeightedDensity a b C F) s+μ) :
    phaseSlice F t = ENNReal.ofReal (Real.exp (C*(s-t))) • phaseSlice F s+
      ENNReal.ofReal (Real.exp (-C*t)) • μ := by
  rw [timeWeighted_phaseSlice,timeWeighted_phaseSlice,
    slabExponential,indicator_of_mem ht,indicator_of_mem hs] at h
  have hh := congrArg (fun m : Measure Phase => ENNReal.ofReal (Real.exp (-C*t)) • m) h
  rw [smul_add,smul_smul,smul_smul,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add,← Real.exp_add] at hh
  have hzero : -C*t+C*t = 0 := by ring
  have he : -C*t+C*s = C*(s-t) := by ring
  simpa only [hzero,he,Real.exp_zero,ENNReal.ofReal_one,one_smul] using hh

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # One positive source for the undamped characteristic renewal equation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

theorem timeWeightedSource_add (a b C : ℝ) (μ ν : Measure (ℝ × Phase)) :
    timeWeightedSource a b C (μ+ν) = timeWeightedSource a b C μ+timeWeightedSource a b C ν := by
  exact withDensity_add_measure _ _ _

theorem timeWeightedSource_density (a b C : ℝ) (μ : Measure (ℝ × Phase))
    {f : ℝ × Phase → ℝ} (hf : AEMeasurable f μ) :
    timeWeightedSource a b C (positiveDensityMeasure μ f) =
      positiveDensityMeasure μ (fun z => slabExponential a b C z.1*f z) := by
  have hw : Measurable (fun z : ℝ × Phase => slabExponential a b C z.1) :=
    (slabExponential_measurable a b C).comp measurable_fst
  unfold timeWeightedSource positiveDensityMeasure
  rw [← withDensity_mul₀ hf.ennreal_ofReal hw.aemeasurable.ennreal_ofReal]
  congr 1
  funext z
  change ENNReal.ofReal (f z)*ENNReal.ofReal (slabExponential a b C z.1) = _
  rw [mul_comm,ENNReal.ofReal_mul (slabExponential_nonneg a b C z.1)]

theorem dampedResidual_source {a b C : ℝ} {F L : ℝ × Phase → ℝ}
    (hF : AEMeasurable F volume) (hL : AEMeasurable L volume) :
    positiveDensityMeasure volume (dampedResidual a b C F L) =
      timeWeightedSource a b C (positiveDensityMeasure volume (fun z => C*F z-L z)) :=
  (timeWeightedSource_density a b C volume ((aemeasurable_const.mul hF).sub hL)).symm

theorem undamp_combined_source_balance {a b C s t : ℝ} {F L : ℝ × Phase → ℝ}
    (μ : Measure (ℝ × Phase)) (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (hF : AEMeasurable F volume) (hL : AEMeasurable L volume)
    (h : phaseSlice (timeWeightedDensity a b C F) t =
      phaseSlice (timeWeightedDensity a b C F) s+
        phaseIncrement (timeWeightedSource a b C μ+
          positiveDensityMeasure volume (dampedResidual a b C F L)) s t) :
    phaseSlice F t = ENNReal.ofReal (Real.exp (C*(s-t))) • phaseSlice F s+
      dampedSourceIncrement a b C s t
        (μ+positiveDensityMeasure volume (fun z => C*F z-L z)) := by
  rw [dampedResidual_source hF hL,← timeWeightedSource_add] at h
  exact undamp_measure_balance F _ hs ht h

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalGlobalRenormalized
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The positive physical entry histories reach the late growth box -/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem velocityPhaseBall_measurable (κ ρ : ℝ) : MeasurableSet (velocityPhaseBall κ ρ) :=
  measurable_snd measurableSet_ball

theorem velocityPhaseBall_subset_entry {κ ρ d : ℝ} (hκ : 0 ≤ κ) (hρd : ρ ≤ d*κ/4)
    (hρ₅ : κ+ρ ≤ 5) : velocityPhaseBall κ ρ ⊆ entryVelocityRegion κ d := by
  intro p hp
  change dist p.2 (κ • firstAxis) < ρ at hp
  rw [dist_eq_norm] at hp
  refine ⟨hp.trans_le hρd,?_⟩
  have hb : ‖p.2‖ ≤ ‖p.2-κ • firstAxis‖+κ := by
    calc
      ‖p.2‖ = ‖(p.2-κ • firstAxis)+κ • firstAxis‖ := by congr 1; module
      _ ≤ ‖p.2-κ • firstAxis‖+‖κ • firstAxis‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hκ,axis_norms.1,mul_one]
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedGeometricBlock
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A nonzero density has a bounded positive portion away from the velocity axis -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem seedPortion_measurable (n : ℕ) : MeasurableSet (seedPortion n) := by
  unfold seedPortion
  measurability

end BoltzmannNonuniqueness

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

/-! # Local measure balances with one fixed phase cutoff -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem phaseWeight_integrable {β : Phase → ℝ} (hβ : Continuous β)
    (hc : HasCompactSupport β) {F : ℝ × Phase → ℝ} (hi : Integrable F) :
    Integrable (phaseWeight β F) := by
  obtain ⟨C,hC⟩ := hβ.bounded_above_of_compact_support hc
  exact hi.bdd_mul (hβ.measurable.comp measurable_snd).aestronglyMeasurable
    (ae_of_all _ (fun z => hC z.2))

theorem weightedPhaseSource_finite (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ]
    {β : Phase → ℝ} (hβ : Continuous β) (hc : HasCompactSupport β) (hn : ∀ p, 0 ≤ β p) :
    IsFiniteMeasure (weightedPhaseSource μ β) := by
  obtain ⟨C,hC⟩ := hβ.bounded_above_of_compact_support hc
  apply positiveDensityMeasure_finite
  · exact (integrable_const C).mono' (hβ.measurable.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ (fun z => hC z.2))
  · exact ae_of_all _ (fun z => hn z.2)

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Constant damping for weak evolution localized in characteristic phase -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem ae_localized_damped_measure_balance {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C)
    {F L : ℝ × Phase → ℝ} (hi : Integrable F (volume : Measure (ℝ × Phase)))
    (hL : Integrable L (volume : Measure (ℝ × Phase))) (hn : ∀ᵐ z ∂volume, 0 ≤ F z)
    (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ]
    {β : Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
    (hbound : ∀ᵐ z ∂volume, z.1 ∈ Ioo a b → β z.2*L z ≤ C*(β z.2*F z))
    (hw : ∀ φ : Phase → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ p, 0 ≤ φ p) → tsupport φ ⊆ tsupport β →
      ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
      (∫ z, (deriv θ z.1*φ z.2)*F z)+
        (∫ z, θ z.1*φ z.2 ∂μ)-(∫ z, (θ z.1*φ z.2)*L z) = 0) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      phaseSlice (timeWeightedDensity a b C (phaseWeight β F)) t =
        phaseSlice (timeWeightedDensity a b C (phaseWeight β F)) s+
          phaseIncrement (timeWeightedSource a b C (weightedPhaseSource μ β)+
            positiveDensityMeasure volume
              (dampedResidual a b C (phaseWeight β F) (phaseWeight β L))) s t := by
  let _ := weightedPhaseSource_finite μ hβ.continuous hβc hβn
  apply ae_damped_measure_interval_balance hab hC
    (phaseWeight_integrable hβ.continuous hβc hi)
    (phaseWeight_integrable hβ.continuous hβc hL)
    (hn.mono (fun z hz => mul_nonneg (hβn z.2) hz)) hbound
  intro φ hφ _hc hφn θ hθ hθc hθs
  have hp := hw (fun p => φ p*β p) (hφ.mul hβ) hβc.mul_left
    (fun p => mul_nonneg (hφn p) (hβn p)) tsupport_mul_subset_right θ hθ hθc hθs
  have hβm : AEMeasurable (fun z : ℝ × Phase => β z.2) μ := by
    simpa only [Function.comp_def] using
      (hβ.continuous.measurable.comp measurable_snd).aemeasurable (μ := μ)
  rw [show weightedPhaseSource μ β = positiveDensityMeasure μ (fun z => β z.2) from rfl,
    positiveDensityMeasure_integral hβm (ae_of_all _ (fun z => hβn z.2))]
  simpa only [phaseWeight,mul_assoc] using hp

end BoltzmannNonuniqueness.WeakTime

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

/-! # Uniform free-flight escape of the bounded nonaxial seed -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem seed_flight_bounds {n : ℕ} {p : Velocity × Velocity}
    (hp : p ∈ seedPortion n) {t : ℝ} (ht : 0 ≤ t) :
    t/((n : ℝ)+1)-(n : ℝ) ≤ ‖transverse (p.1+t • p.2)‖ ∧
      ‖p.1+t • p.2‖ ≤ (n : ℝ)*(1+t) := by
  have he : transverse (p.1+t • p.2) = transverse p.1+t • transverse p.2 := by
    apply (WithLp.ext_iff 2).mpr
    funext i
    rfl
  have hv := mul_le_mul_of_nonneg_left hp.2.2 ht
  have hn := norm_sub_norm_le (t • transverse p.2) (-transverse p.1)
  rw [sub_neg_eq_add,add_comm,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,norm_neg] at hn
  have hx := (LargeOutput.transverse_norm_le p.1).trans hp.1
  have hupper := norm_add_le p.1 (t • p.2)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht] at hupper
  have htv := mul_le_mul_of_nonneg_left hp.2.1 ht
  refine ⟨?_,by nlinarith [hp.1]⟩
  rw [he]
  have hd : t*(1/((n : ℝ)+1)) = t/((n : ℝ)+1) := by ring
  rw [hd] at hv
  linarith

theorem seed_flight_radius_linear {n : ℕ} {p : Velocity × Velocity}
    (hp : p ∈ seedPortion n) {t : ℝ}
    (ht : max 1 (2*(n : ℝ)*((n : ℝ)+1)) ≤ t) :
    t/(2*((n : ℝ)+1)) ≤ ‖transverse (p.1+t • p.2)‖ := by
  have ht0 : 0 ≤ t := (show (0:ℝ) ≤ 1 by norm_num).trans ((le_max_left _ _).trans ht)
  have hl := (seed_flight_bounds hp ht0).1
  have hn : 0 < (n : ℝ)+1 := by positivity
  have hlarge := (le_max_right _ _).trans ht
  have hnle : (n : ℝ) ≤ t/(2*((n : ℝ)+1)) :=
    (le_div_iff₀ (by positivity)).mpr (by nlinarith)
  have he : t/((n : ℝ)+1) = 2*(t/(2*((n : ℝ)+1))) := by field_simp
  rw [he] at hl
  linarith

theorem seed_flight_outside (n : ℕ) (L : ℝ) : ∃ T : ℝ, 0 < T ∧
    ∀ t, T ≤ t → ∀ p ∈ seedPortion n, L < ‖transverse (p.1+t • p.2)‖ := by
  let T := max (max 1 (2*(n : ℝ)*((n : ℝ)+1))) (2*((n : ℝ)+1)*(|L|+1))
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ)<1)
    ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨T,hT,?_⟩
  intro t ht p hp
  have hl := seed_flight_radius_linear hp ((le_max_left _ _).trans ht)
  have hh : |L|+1 ≤ t/(2*((n : ℝ)+1)) :=
    (le_div_iff₀ (by positivity)).mpr (by
      have hh := (le_max_right _ _).trans ht
      nlinarith)
  linarith [le_abs_self L]

end BoltzmannNonuniqueness

end

end

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

theorem seedPhaseCutoff_one {n : ℕ} {p : WeakTime.Phase} (hp : p ∈ seedPortion n) :
    seedPhaseCutoff n p = 1 := by
  apply (seedPhaseBump n).one_of_mem_closedBall
  rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff]
  exact ⟨hp.1.trans (by dsimp [seedPhaseBump] <;> linarith),
    hp.2.1.trans (by dsimp [seedPhaseBump] <;> linarith)⟩

theorem phaseSlice_weight_le {F : ℝ × WeakTime.Phase → ℝ} {β : WeakTime.Phase → ℝ}
    (hF : ∀ z, 0 ≤ F z) (hβ : ∀ p, β p ≤ 1) (t : ℝ) :
    WeakTime.phaseSlice (WeakTime.phaseWeight β F) t ≤ WeakTime.phaseSlice F t := by
  apply withDensity_mono
  apply ae_of_all
  intro p
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_of_le_one_left (hF _) (hβ p)

theorem phaseSlice_weight_apply_eq {F : ℝ × WeakTime.Phase → ℝ}
    {β : WeakTime.Phase → ℝ} {S : Set WeakTime.Phase} (hS : MeasurableSet S)
    (hβ : ∀ p ∈ S, β p = 1) (t : ℝ) :
    WeakTime.phaseSlice (WeakTime.phaseWeight β F) t S = WeakTime.phaseSlice F t S := by
  unfold WeakTime.phaseSlice positiveDensityMeasure
  rw [withDensity_apply _ hS,withDensity_apply _ hS]
  apply setLIntegral_congr_fun hS
  intro p hp
  change ENNReal.ofReal (β p*F (t,p)) = ENNReal.ofReal (F (t,p))
  rw [hβ p hp,one_mul]

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

theorem seed_mass_escapes {s : ℝ} {n : ℕ} (μ : ℝ → Measure (Velocity × Velocity))
    (hseed : ∀ᵐ t ∂volume, s ≤ t → 0 < μ t (seedPortion n)) :
    ∀ L : ℝ, ∃ T : ℝ, 0 < T ∧ ∀ᵐ t ∂volume, T ≤ t →
      0 < (μ t).map (flight t) (seedEscapeRegion n L t) := by
  intro L
  obtain ⟨T₀,hT₀,hout⟩ := seed_flight_outside n L
  let T := max s T₀
  refine ⟨T,hT₀.trans_le (le_max_right _ _),?_⟩
  filter_upwards [hseed] with t ht
  intro hTt
  have hs : s ≤ t := (le_max_left _ _).trans hTt
  have hT : T₀ ≤ t := (le_max_right _ _).trans hTt
  have ht0 : 0 ≤ t := (hT₀.trans_le hT).le
  rw [Measure.map_apply (flight_measurePreserving t).measurable
    (seedEscapeRegion_measurable n L t)]
  apply (ht hs).trans_le
  apply measure_mono
  intro p hp
  exact ⟨hout t hT p hp,(seed_flight_bounds hp ht0).2,hp.2.1⟩

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedEntryPortion
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded portions of the entry velocities have one uniform late-box arrival time -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem entryPhasePortion_measurable (κ ρ : ℝ) (n : ℕ) :
    MeasurableSet (entryPhasePortion κ ρ n) :=
  (velocityPhaseBall_measurable κ ρ).inter (measurableSet_le measurable_id.norm measurable_const)

theorem entryPhasePortion_union (κ ρ : ℝ) :
    (⋃ n, entryPhasePortion κ ρ n) = velocityPhaseBall κ ρ := by
  ext p
  constructor
  · intro hp
    obtain ⟨n,hn⟩ := mem_iUnion.mp hp
    exact hn.1
  · intro hp
    obtain ⟨n,hn⟩ := exists_nat_gt ‖p‖
    exact mem_iUnion.mpr ⟨n,hp,hn.le⟩

theorem exists_positive_entryPortion {κ ρ : ℝ} (μ : Measure WeakTime.Phase)
    (hμ : 0 < μ (velocityPhaseBall κ ρ)) :
    ∃ n, 0 < μ (entryPhasePortion κ ρ n) := by
  apply exists_measure_pos_of_not_measure_iUnion_null
  rw [entryPhasePortion_union]
  exact ne_of_gt hμ

theorem entryPhasePortion_cutoff {κ ρ : ℝ} {n : ℕ} {p : WeakTime.Phase}
    (hp : p ∈ entryPhasePortion κ ρ n) : seedPhaseCutoff n p = 1 := by
  apply (seedPhaseBump n).one_of_mem_closedBall
  rw [Metric.mem_closedBall,dist_zero_right]
  dsimp [seedPhaseBump]
  have hb : ‖p‖ ≤ (n:ℝ) := hp.2
  linarith

theorem entryPhasePortion_eventually_lateBox {κ ρ d : ℝ} (hκ : 0 < κ) (hd : 0 < d)
    (hρd : ρ ≤ d*κ/4) (hρ₅ : κ+ρ ≤ 5) (n : ℕ) :
    ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t → ∀ p ∈ entryPhasePortion κ ρ n,
      flight t p ∈ lateBox κ d t := by
  obtain ⟨T,_hT₀,hT,hbound⟩ := bounded_flight_lateBox (a := 0) (X := (n:ℝ)) hκ hd le_rfl
  refine ⟨T,hT,?_⟩
  intro t ht p hp
  have hv := velocityPhaseBall_subset_entry hκ.le hρd hρ₅ hp.1
  have hx := (norm_fst_le p).trans hp.2
  simpa only [sub_zero,flight] using hbound p.1 p.2 hx hv.1 hv.2 t ht

theorem positive_entryPortion_eventually_lateBox {κ ρ d : ℝ} (hκ : 0 < κ) (hd : 0 < d)
    (hρd : ρ ≤ d*κ/4) (hρ₅ : κ+ρ ≤ 5) (n : ℕ) (s : ℝ)
    (μ : ℝ → Measure WeakTime.Phase)
    (hμ : ∀ᵐ t ∂volume, s ≤ t → 0 < μ t (entryPhasePortion κ ρ n)) :
    ∃ T : ℝ, 0 < T ∧ ∀ᵐ t ∂volume, T ≤ t → 0 < μ t (flight t ⁻¹' lateBox κ d t) := by
  obtain ⟨T,hT,hbound⟩ := entryPhasePortion_eventually_lateBox hκ hd hρd hρ₅ n
  refine ⟨max s T,hT.trans_le (le_max_right _ _),?_⟩
  filter_upwards [hμ] with t ht
  intro htt
  exact (ht ((le_max_left _ _).trans htt)).trans_le
    (measure_mono (hbound t ((le_max_right _ _).trans htt)))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapCoveredDamping
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The characteristic loss source has an integrable time density -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicLossDensity_integrable (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) : Integrable (E.characteristicLossDensity a A R) volume :=
  cylinderPullback_integrable (E.actual_loss_cylinder_integrable ha haA hK hα hγ hq)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual characteristic loss measure has its physical density -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicLossDensity_nonneg (E : HotLimitExtraction S)
    (a A R : ℝ) (u : CharacteristicPhase) : 0 ≤ E.characteristicLossDensity a A R u := by
  change 0 ≤ (coldCylinderSet a A R).indicator (fun z => E.hotLimit z*
    GeometricBackground.frequency E.phase η E.fraction K α γ z.1.1 z.1.2 z.2)
      (hotCharacteristicEquiv u)
  apply indicator_nonneg _ _
  intro z _
  exact mul_nonneg (E.hotLimit_nonneg z) (GeometricBackground.frequency_nonneg ..)

theorem HotLimitExtraction.characteristicLoss_integral (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) {ψ : CharacteristicPhase → ℝ} (hψ : Measurable ψ)
    {B : ℝ} (hB : ∀ z, |ψ z| ≤ B) :
    (∫ u, ψ u ∂E.characteristicLossMeasure ha hK hα hγ A R) =
      ∫ u, ψ u*E.characteristicLossDensity a A R u := by
  have hm : Measurable (fun z : HotKineticPhase => ψ (hotCharacteristicEquiv.symm z)) :=
    hψ.comp hotCharacteristicEquiv.symm.measurable
  change (∫ u, ψ u ∂sourcePullback _) = _
  rw [sourcePullback_integral _ hψ,
    E.actual_loss_cylinder_integral ha haA hK hα hγ hq hm (fun z => hB _)]
  exact (cylinderPullback_integral a A R _ ψ).symm

theorem HotLimitExtraction.characteristicLossMeasure_eq (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (haA : a ≤ A) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : q < 2) :
    E.characteristicLossMeasure ha hK hα hγ A R =
      positiveDensityMeasure volume (E.characteristicLossDensity a A R) := by
  let _ := E.incomingLossMeasure_finite (R := R) ha (ha.le.trans haA) hK hα hγ hq
  have : IsFiniteMeasure (E.characteristicLossMeasure ha hK hα hγ A R) := by
    unfold HotLimitExtraction.characteristicLossMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hi := E.characteristicLossDensity_integrable (R := R) ha haA hK hα hγ hq
  have hn := ae_of_all volume (E.characteristicLossDensity_nonneg a A R)
  let _ := positiveDensityMeasure_finite hi hn
  apply Compactness.finite_measure_eq_of_positive_smooth_tests
  intro ψ hψ hc _hψn
  obtain ⟨B,hB⟩ := hψ.continuous.bounded_above_of_compact_support hc
  rw [E.characteristicLoss_integral ha haA hK hα hγ hq hψ.continuous.measurable hB,
    positiveDensityMeasure_integral hi.aemeasurable hn]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Positive retained-source balance for the actual hot limit -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicLossDensity_factor (E : HotLimitExtraction S)
    (a A R : ℝ) (u : CharacteristicPhase) :
    E.characteristicLossDensity a A R u =
      cylinderPullback a A R E.hotLimit u*E.characteristicFrequency u := by
  by_cases hu : hotCharacteristicEquiv u ∈ coldCylinderSet a A R
  · simp only [HotLimitExtraction.characteristicLossDensity,cylinderPullback,Function.comp_def,
      indicator_of_mem hu,HotLimitExtraction.characteristicFrequency]
  · simp only [HotLimitExtraction.characteristicLossDensity,cylinderPullback,Function.comp_def,
      indicator_of_notMem hu,zero_mul]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

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

section

/-! # Free-flight survival for compact portions of the actual hot density -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.characteristic_free_flight_survival
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon)
    {β : Velocity × Velocity → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      ENNReal.ofReal (Real.exp (C*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight β
          (E.hotLimit ∘ hotCharacteristicEquiv)) s ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight β
          (E.hotLimit ∘ hotCharacteristicEquiv)) t := by
  obtain ⟨R,_hR,hcover,hweak⟩ := E.covered_characteristic_weak_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hβc
  obtain ⟨C,hC,hfreq⟩ := E.toHotLimitExtraction.characteristic_frequency_compact_bound
    ha hK hα hγ hβc
  have hfrequency (u : CharacteristicPhase) (hu : u.1 ∈ Ioo a A)
      (hp : u.2 ∈ tsupport β) : E.toHotLimitExtraction.characteristicFrequency u ≤ C :=
    hfreq u hu.1.le hp
  let _ := E.toHotLimitExtraction.incomingGainMeasure_finite
    (R := R) ha (ha.le.trans haA.le) hK hα hγ hq₂
  have : IsFiniteMeasure (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) := by
    unfold HotLimitExtraction.characteristicGainMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hi := (E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le
    ((ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB) R).2.1
  have hLi := E.toHotLimitExtraction.characteristicLossDensity_integrable (R := R)
    ha haA.le hK hα hγ hq₂
  have hn (u : CharacteristicPhase) : 0 ≤ cylinderPullback a A R E.hotLimit u :=
    indicator_nonneg (fun z _ => E.toHotLimitExtraction.hotLimit_nonneg z) _
  have hbound : ∀ᵐ u : CharacteristicPhase ∂volume, u.1 ∈ Ioo a A →
      β u.2*E.toHotLimitExtraction.characteristicLossDensity a A R u ≤
        C*(β u.2*cylinderPullback a A R E.hotLimit u) := by
    apply ae_of_all
    intro u hu
    by_cases hz : β u.2 = 0
    · simp only [hz,zero_mul,mul_zero,le_refl]
    rw [E.toHotLimitExtraction.characteristicLossDensity_factor]
    have hb := hfrequency u hu (subset_tsupport β hz)
    have hp : 0 ≤ β u.2*cylinderPullback a A R E.hotLimit u := mul_nonneg (hβn _) (hn u)
    nlinarith only [mul_le_mul_of_nonneg_left hb hp]
  have hbalance := WeakTime.ae_localized_damped_measure_balance haA hC
    (cylinderPullback_integrable hi) hLi (ae_of_all _ hn)
    (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) hβ hβc hβn hbound
    (by
      intro φ hφ hc hφn hφβ θ hθ hθc hθs
      have hb := hweak φ hφ hc hφn hφβ θ hθ hθc hθs
      rw [E.toHotLimitExtraction.characteristicLossMeasure_eq ha haA.le hK hα hγ hq₂,
        positiveDensityMeasure_integral hLi.aemeasurable
          (ae_of_all _ (E.toHotLimitExtraction.characteristicLossDensity_nonneg a A R))] at hb
      exact hb)
  have hF := (WeakTime.phaseWeight_integrable hβ.continuous hβc
    (cylinderPullback_integrable hi)).aemeasurable
  have hL := (WeakTime.phaseWeight_integrable hβ.continuous hβc hLi).aemeasurable
  have heq (t : ℝ) (ht : t ∈ Ioo a A) :
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t =
      WeakTime.phaseSlice (WeakTime.phaseWeight β (E.hotLimit ∘ hotCharacteristicEquiv)) t := by
    unfold WeakTime.phaseSlice positiveDensityMeasure
    congr 1
    funext p
    unfold WeakTime.phaseWeight
    by_cases hp : β p = 0
    · simp only [hp,zero_mul]
    · have hz := hcover t ⟨ht.1.le,ht.2.le⟩ p (subset_tsupport β hp)
      simp only [cylinderPullback,Function.comp_def,indicator_of_mem hz]
  refine ⟨C,hC,?_⟩
  filter_upwards [hbalance] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst
  have hh := WeakTime.undamp_combined_source_balance _ hsa hta hF hL (ht hsa hta hst)
  rw [heq s hsa,heq t hta] at hh
  rw [hh]
  exact le_add_of_nonneg_right bot_le

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # One bounded nonaxial seed survives at almost every later finite time -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.persisting_seed (E : HotPairExtraction S)
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hU : E.horizon = ⊤) :
    ∃ s ∈ Ioc (0:ℝ) 1, ∃ n : ℕ, ∀ᵐ t ∂volume, s ≤ t →
      0 < WeakTime.phaseSlice (E.hotLimit ∘ hotCharacteristicEquiv) t (seedPortion n) := by
  let start (m : ℕ) : ℝ := 1/((m : ℝ)+2)
  have hstart (m : ℕ) : 0 < start m ∧ start m ≤ 1 := by
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    exact ⟨by dsimp [start] <;> positivity,
      (div_le_iff₀ (show 0 < (m : ℝ)+2 by positivity)).mpr (by linarith)⟩
  have hsurvival (n m N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo (start m) ((N : ℝ)+2) → t ∈ Ioo (start m) ((N : ℝ)+2) → s ≤ t →
      ENNReal.ofReal (Real.exp (C*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) s ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) t := by
    apply E.characteristic_free_flight_survival hDP hcarleman hGLPS
      hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ (hstart m).1
      (B := (N : ℝ)+3)
    · have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith [(hstart m).2]
    · linarith
    · rw [hU]
      exact ENNReal.ofReal_lt_top
    · exact seedPhaseCutoff_smooth n
    · exact seedPhaseCutoff_compact n
    · exact fun p => (seedPhaseCutoff_mem n p).1
  choose C hC htrace using hsurvival
  have hgood : ∀ᵐ s ∂volume, ∀ n m N : ℕ, ∀ᵐ t ∂volume,
      s ∈ Ioo (start m) ((N : ℝ)+2) → t ∈ Ioo (start m) ((N : ℝ)+2) → s ≤ t →
      ENNReal.ofReal (Real.exp (C n m N*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) s ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) t :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun m => ae_all_iff.mpr fun N => htrace n m N
  obtain ⟨s,hs,hsg,n,hn⟩ := E.toHotLimitExtraction.exists_positive_seed_q80 hcarleman hMityagin
    hs₀ hsmax hη hηmax hK hα (hαmax.trans (by norm_num)) hγ hd₀ hdmax hsmall hq₁ hq₂ hgood
  obtain ⟨m,hm⟩ := exists_nat_gt (1/s)
  have hms : start m < s := by
    have hm' := (div_lt_iff₀ hs.1).mp hm
    apply (div_lt_iff₀ (show 0 < (m : ℝ)+2 by positivity)).mpr
    nlinarith [hs.1]
  refine ⟨s,hs,n,?_⟩
  filter_upwards [ae_all_iff.mpr (fun N => hsg n m N)] with t ht
  intro hst
  obtain ⟨N,hN⟩ := exists_nat_gt t
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hi := ht N ⟨hms,by linarith [hs.2]⟩ ⟨hms.trans_le hst,by linarith⟩ hst
  have hle := hi.trans (phaseSlice_weight_le
    (fun z => E.toHotLimitExtraction.hotLimit_nonneg (hotCharacteristicEquiv z))
    (fun p => (seedPhaseCutoff_mem n p).2) t)
  have hh := hle (seedPortion n)
  rw [Measure.smul_apply,smul_eq_mul,phaseSlice_weight_apply_eq (seedPortion_measurable n)
    (fun p hp => seedPhaseCutoff_one hp)] at hh
  have hp : 0 < ENNReal.ofReal (Real.exp (C n m N*(s-t)))*
      WeakTime.phaseSlice (E.hotLimit ∘ hotCharacteristicEquiv) s (seedPortion n) :=
    pos_iff_ne_zero.mpr (mul_ne_zero
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) (ne_of_gt hn))
  exact hp.trans_le hh

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual hot density reaches bounded regions beyond the cold hole -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.escaping_seed (E : HotPairExtraction S)
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hdmax : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hU : E.horizon = ⊤) :
    ∃ n : ℕ, ∀ L : ℝ, ∃ T : ℝ, 0 < T ∧ ∀ᵐ t ∂volume, T ≤ t →
      0 < (WeakTime.phaseSlice (E.hotLimit ∘ hotCharacteristicEquiv) t).map (flight t)
        (seedEscapeRegion n L t) := by
  obtain ⟨s,_hs,n,hseed⟩ := E.persisting_seed hDP hcarleman hGLPS hMityagin
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hdmax hsmall hq₁ hq₂ hU
  exact ⟨n,seed_mass_escapes _ hseed⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

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

/-! # The nonzero actual hot solution acquires the entry velocities at a good finite time -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.exists_actual_entry
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters) (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hH : E.horizon = ⊤)
    {κ ρ ε : ℝ} (hκ : 0 ≤ κ) (hκmax : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1/12) (hαε : α ≤ ε/2) (hερ : 6*ε ≤ ρ)
    (haccess : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    {G : Set ℝ} (hG : ∀ᵐ t ∂volume, t ∈ G) :
    ∃ t : ℝ, 0 < t ∧ t ∈ G ∧ 0 < hotPhaseSlice E.hotLimit t (velocityPhaseBall κ ρ) := by
  obtain ⟨n,hn⟩ := E.escaping_seed hDP hcarleman hGLPS hMityagin
    hs₀ hsmax hη hηmax hK.le hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hH
  obtain ⟨T,hT,hseed⟩ := hn (Real.exp η*E.fraction+2)
  let a := max T 1
  let U := a+1
  have ha : 0 < a := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_right _ _)
  have haU : a < U := by dsimp [U] <;> linarith
  have hgrowth := E.entry_window_q80 hDP hcarleman hGLPS hs₀ hsmax hη hηmax hK hα hαmax
    hγ hd₀ hd₀max hsmall hq₁ hq₂ hκ hκmax hρ hε hεmax hαε hερ haccess
    ha haU (show U < U+1 by linarith) (by rw [hH]; exact ENNReal.ofReal_lt_top) n
  have hpos : (volume : Measure ℝ) (Ioo a U) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr haU))
  obtain ⟨s,hs,hsgrowth,hsseed⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos
    (ae_restrict_of_ae (hgrowth.and hseed))
  have hm : 0 < hotPhaseSlice E.hotLimit s
      (flight s ⁻¹' seedEscapeRegion n (Real.exp η*E.fraction+2) s) := by
    have hh := hsseed ((le_max_left _ _).trans hs.1.le)
    rw [Measure.map_apply (flight_measurePreserving s).measurable
      (seedEscapeRegion_measurable n _ s)] at hh
    exact hh
  let b := min U (s+1/((n:ℝ)+6))
  have hden : 0 < (n:ℝ)+6 := by positivity
  have hsb : s < b := lt_min hs.2 (by linarith [one_div_pos.mpr hden])
  have hp : (volume : Measure ℝ) (Ioo s b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hsb))
  obtain ⟨t,ht,htgrowth,htG⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hp (ae_restrict_of_ae (hsgrowth.and hG))
  have htU : t < U := ht.2.trans_le (min_le_left _ _)
  have hshort : ((n:ℝ)+6)*(t-s) ≤ 1 := by
    have hh : t-s < 1/((n:ℝ)+6) := by linarith [ht.2.trans_le (min_le_right _ _)]
    have hh' := (lt_div_iff₀ hden).mp hh
    nlinarith
  exact ⟨t,ha.trans (hs.1.trans ht.1),htG,
    htgrowth hs ⟨hs.1.trans ht.1,htU⟩ (sub_pos.mpr ht.1) hshort hm⟩

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A bounded portion of actual entry mass survives on every later finite time window -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.persisting_entry
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters) (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hH : E.horizon = ⊤)
    {κ ρ ε : ℝ} (hκ : 0 ≤ κ) (hκmax : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1/12) (hαε : α ≤ ε/2) (hερ : 6*ε ≤ ρ)
    (haccess : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2))) :
    ∃ s : ℝ, 0 < s ∧ ∃ n : ℕ, ∀ᵐ t ∂volume, s ≤ t →
      0 < hotPhaseSlice E.hotLimit t (entryPhasePortion κ ρ n) := by
  let start (m : ℕ) : ℝ := 1/((m:ℝ)+2)
  have hstart (m : ℕ) : 0 < start m ∧ start m ≤ 1 := by
    have hm : 0 ≤ (m:ℝ) := Nat.cast_nonneg m
    exact ⟨by dsimp [start] <;> positivity,
      (div_le_iff₀ (show 0 < (m:ℝ)+2 by positivity)).mpr (by linarith)⟩
  have hsurvival (n m N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo (start m) ((N:ℝ)+2) → t ∈ Ioo (start m) ((N:ℝ)+2) → s ≤ t →
      ENNReal.ofReal (Real.exp (C*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) s ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) t := by
    apply E.characteristic_free_flight_survival hDP hcarleman hGLPS
      hs₀ hsmax hη hηmax hK.le hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ (hstart m).1
      (B := (N:ℝ)+3)
    · have hN : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
      linarith [(hstart m).2]
    · linarith
    · rw [hH]; exact ENNReal.ofReal_lt_top
    · exact seedPhaseCutoff_smooth n
    · exact seedPhaseCutoff_compact n
    · exact fun p => (seedPhaseCutoff_mem n p).1
  choose C hC htrace using hsurvival
  have hgood : ∀ᵐ s ∂volume, ∀ n m N : ℕ, ∀ᵐ t ∂volume,
      s ∈ Ioo (start m) ((N:ℝ)+2) → t ∈ Ioo (start m) ((N:ℝ)+2) → s ≤ t →
      ENNReal.ofReal (Real.exp (C n m N*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) s ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight (seedPhaseCutoff n)
          (E.hotLimit ∘ hotCharacteristicEquiv)) t :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun m => ae_all_iff.mpr fun N => htrace n m N
  obtain ⟨s,hs,hsg,hentry⟩ := E.exists_actual_entry hDP hcarleman hGLPS hMityagin
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hH
    hκ hκmax hρ hε hεmax hαε hερ haccess hgood
  obtain ⟨n,hn⟩ := exists_positive_entryPortion _ hentry
  obtain ⟨m,hm⟩ := exists_nat_gt (1/s)
  have hms : start m < s := by
    have hm' := (div_lt_iff₀ hs).mp hm
    apply (div_lt_iff₀ (show 0 < (m:ℝ)+2 by positivity)).mpr
    nlinarith
  refine ⟨s,hs,n,?_⟩
  filter_upwards [ae_all_iff.mpr (fun N => hsg n m N)] with t ht
  intro hst
  obtain ⟨N,hN⟩ := exists_nat_gt t
  have hi := ht N ⟨hms,by linarith⟩ ⟨hms.trans_le hst,by linarith⟩ hst
  have hle := hi.trans (phaseSlice_weight_le
    (fun z => E.toHotLimitExtraction.hotLimit_nonneg (hotCharacteristicEquiv z))
    (fun p => (seedPhaseCutoff_mem n p).2) t)
  have hh := hle (entryPhasePortion κ ρ n)
  rw [Measure.smul_apply,smul_eq_mul,phaseSlice_weight_apply_eq (entryPhasePortion_measurable κ ρ n)
    (fun p hp => entryPhasePortion_cutoff hp)] at hh
  have hp : 0 < ENNReal.ofReal (Real.exp (C n m N*(s-t)))*
      hotPhaseSlice E.hotLimit s (entryPhasePortion κ ρ n) :=
    pos_iff_ne_zero.mpr (mul_ne_zero
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) (ne_of_gt hn))
  exact hp.trans_le hh

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AccessAngularFubini
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Compatible velocity-entry and positive-growth parameters -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem exists_access_growth_parameters : ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧
    (referenceClock : ℝ)*κ < referenceGrowth ∧
    ∀ d : ℝ, 0 < d → d ≤ 1/2 → ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/12 ∧
      6*ε ≤ d*κ/4 ∧
      0 < (sphereProbability.prod sphereProbability) (accessAngles κ (d*κ/8)) := by
  obtain ⟨δ,hδ,_hδsmall,haccess⟩ := accessAngles_positive
  let κ := min (δ/4) (1/1000)
  have hκ : 0 < κ := lt_min (by positivity) (by norm_num)
  have hκbound : κ ≤ (1:ℝ)/1000 := min_le_right _ _
  have hκδ : κ ≤ δ/4 := min_le_left _ _
  have hκ1 : κ < 1 := hκbound.trans_lt (by norm_num)
  have hg : (referenceClock : ℝ)*κ < referenceGrowth := by
    change (48*Real.pi)*κ < 11*Real.pi/6
    have hh := mul_le_mul_of_nonneg_left hκbound (show 0 ≤ 48*Real.pi by positivity)
    nlinarith [Real.pi_pos]
  refine ⟨κ,hκ,hκ1,hg,?_⟩
  intro d hd hdsmall
  let ε := min (1/12) (d*κ/24)
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hεb : ε ≤ 1/12 := min_le_left _ _
  have hεr : 6*ε ≤ d*κ/4 := by
    have hh : ε ≤ d*κ/24 := min_le_right _ _
    linarith
  refine ⟨ε,hε,hεb,hεr,haccess κ (d*κ/8) hκ (by positivity) ?_⟩
  have hdκ := mul_le_mul_of_nonneg_right hdsmall hκ.le
  linarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapUniformFiniteHorizon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual nonzero hot limit has positive mass in all sufficiently late growth boxes -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.unbounded_horizon_lateBox_positive
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters) (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hH : E.horizon = ⊤)
    {κ ρ ε d : ℝ} (hκ : 0 < κ) (hκmax : κ ≤ 1) (hρ : ρ ≤ 1)
    (hε : 0 < ε) (hεmax : ε ≤ 1/12) (hαε : α ≤ ε/2) (hερ : 6*ε ≤ ρ)
    (haccess : 0 < (sphereProbability.prod sphereProbability) (accessAngles κ (ρ/2)))
    (hd : 0 < d) (hρd : ρ ≤ d*κ/4) (hρ₅ : κ+ρ ≤ 5) :
    ∃ T : ℝ, 0 < T ∧ ∀ᵐ t ∂volume, T ≤ t → 0 < hotLateBoxMass E.hotLimit κ d t := by
  obtain ⟨s,_hs,n,hpersist⟩ := E.persisting_entry hDP hcarleman hGLPS hMityagin
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hH
    hκ.le hκmax hρ hε hεmax hαε hερ haccess
  exact positive_entryPortion_eventually_lateBox hκ hd hρd hρ₅ n s
    (hotPhaseSlice E.hotLimit) hpersist

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Fixed geometric parameters force every actual extracted dilated horizon to be finite -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

theorem uniform_finite_horizon_parameters :
    ∃ κ d A₀ ε γ₀ : ℝ, 0 < κ ∧ κ < 1 ∧ 0 < d ∧ d ≤ 1/32 ∧
      0 < A₀ ∧ 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
        {S : AttainedCapSequence F},
      Published.DunfordPettis1940HotPairWindows → Published.GPV2009CarlemanInput →
      Published.GLPS1988Proposition3 → Published.Mityagin2020FiveGainParameters →
      ∀ E : HotPairExtraction S,
      0 < s₀ → s₀ ≤ 1/8 → 0 < η → η ≤ Real.log 2 →
      0 < K → 0 < α → α ≤ 1/4 → 0 < γ → 0 < d₀ → d₀ ≤ 1 →
      JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1 → 1 < q → q < 2 →
      η ≤ Real.log (1+ε/20) → α ≤ ε → γ ≤ γ₀ → 480*(8*A₀) ≤ ε*K →
      E.horizon < ⊤ := by
  obtain ⟨κ,hκ,hκmax,hgrowth,haccess⟩ := exists_access_growth_parameters
  let d : ℝ := 1/64
  have hd : 0 < d := by norm_num [d]
  have hdsmall : d ≤ 1/32 := by norm_num [d]
  obtain ⟨εa,hεa,hεamax,hεar,ha⟩ := haccess d hd (by norm_num [d])
  obtain ⟨A₀,εg,γ₀,hA₀,hεg,hεgmax,hγ₀,hzero⟩ :=
    uniform_late_zero_parameters_q80 hd hdsmall hκ hκmax hgrowth
  let ε := min εg (εa/2)
  have hε : 0 < ε := lt_min hεg (by positivity)
  have hεg' : ε ≤ εg := min_le_left _ _
  have hεa' : ε ≤ εa/2 := min_le_right _ _
  refine ⟨κ,d,A₀,ε,γ₀,hκ,hκmax,hd,hdsmall,hA₀,hε,hεg'.trans hεgmax,hγ₀,?_⟩
  intro s₀ η K α γ d₀ q F S hDP hcarleman hGLPS hMityagin E
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    hηsmall hαsmall hγsmall hKlarge
  apply lt_top_iff_ne_top.mpr
  intro hH
  have hηg : η ≤ Real.log (1+εg/20) := hηsmall.trans
    (Real.log_le_log (by positivity) (by linarith))
  have hKg : 480*(8*A₀) ≤ εg*K := hKlarge.trans
    (mul_le_mul_of_nonneg_right hεg' hK.le)
  obtain ⟨R,hR,hz⟩ := hzero hDP hcarleman hGLPS E hs₀ hsmax hη hηmax hK hα hαmax
    hγ hd₀ hd₀max hsmall hq₁ hq₂ hηg (hαsmall.trans hεg') hγsmall hKg hH
  have hρ : d*κ/4 ≤ 1 := by nlinarith
  have hρ₅ : κ+d*κ/4 ≤ 5 := by nlinarith
  obtain ⟨T,hT,hp⟩ := E.unbounded_horizon_lateBox_positive hDP hcarleman hGLPS hMityagin
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ hH
    hκ hκmax.le hρ hεa hεamax (hαsmall.trans hεa') hεar
    (by simpa only [div_div, show (4:ℝ)*2=8 by norm_num] using ha) hd le_rfl hρ₅
  have hpos : (volume : Measure ℝ) (Ioo (max R T+1) (max R T+2)) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  obtain ⟨t,ht,htz,htp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae (hz.and hp))
  have hr : R < t := by linarith [le_max_left R T,ht.1]
  have ht' : T ≤ t := by linarith [le_max_right R T,ht.1]
  have hh := htp ht'
  rw [htz hr] at hh
  exact (lt_irrefl _ hh)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MainParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Concrete compatible parameters for the nonuniqueness construction -/
noncomputable section
open scoped ENNReal
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem exists_construction_parameters_q80_oai
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hMityagin : Published.Mityagin2020FiveGainParameters) : Nonempty ConstructionParameters := by
  obtain ⟨_,_,A₀,ε,γ₀,_,_,_,_,hA₀,hε,_,hγ₀,hfinite⟩ :=
    AttainedCapSequence.uniform_finite_horizon_parameters
  let K := 1+480*(8*A₀)/ε
  have hK : 0 < K := by dsimp [K] <;> positivity
  let C := JetComparisonCoefficient.coefficient K
  have hC : 1 ≤ C := JetComparisonCoefficient.coefficient_ge_one hK.le
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let d₀ := (2*C)⁻¹
  have hd : 0 < d₀ := inv_pos.mpr (by positivity)
  have hdmax : d₀ ≤ 1 := (inv_le_one₀ (by positivity : 0 < 2*C)).mpr (by linarith)
  have hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64 :=
    (mul_le_mul_of_nonneg_right hdmax (by positivity)).trans (by norm_num)
  have hc : C*d₀ = 1/2 := by dsimp [d₀]; field_simp
  have hsmall : JetComparisonCoefficient.coefficient K*d₀*(1/8:ℝ)^9 ≤ 1 := by
    change C*d₀*(1/8:ℝ)^9 ≤ 1
    rw [hc]
    norm_num
  let η := min (Real.log 2) (Real.log (1+ε/20))
  have hη : 0 < η := lt_min (Real.log_pos (by norm_num)) (Real.log_pos (by linarith))
  have hηmax : η ≤ Real.log 2 := min_le_left _ _
  have hηsmall : η ≤ Real.log (1+ε/20) := min_le_right _ _
  let α := min ε (1/4)
  have hα : 0 < α := lt_min hε (by norm_num)
  have hαmax : α ≤ 1/4 := min_le_right _ _
  have hKlarge : 480*(8*A₀) ≤ ε*K := by
    have he : ε*K = ε+480*(8*A₀) := by dsimp [K]; field_simp
    rw [he]
    linarith
  refine ⟨⟨1/8,η,K,α,γ₀,d₀,3/2,by norm_num,le_rfl,hη,hηmax,hK,hα,hαmax,hγ₀,
    hd,hdmax,hwidth,hsmall,by norm_num,by norm_num,?_⟩⟩
  intro F S E
  exact hfinite hDP hcarleman hGLPS hMityagin E (by norm_num) le_rfl hη hηmax hK hα hαmax
    hγ₀ hd hdmax hsmall (by norm_num) (by norm_num) hηsmall (min_le_left _ _) le_rfl hKlarge

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.exists_construction_parameters_q80_oai
