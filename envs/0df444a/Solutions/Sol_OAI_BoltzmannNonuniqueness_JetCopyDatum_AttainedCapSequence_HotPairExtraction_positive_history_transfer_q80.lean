-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.positive_history_transfer_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:21:29.026926+00:00
-- url     : https://prove2.me/submissions/b007ae63-a9cb-4038-bf7d-0d6254d1949c

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_JetCopyDatum_AttainedCapSequence_HotPairExtraction_characteristic_test_balance_q80

section
-- module Solutions.OAIQ080_BZ.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
open ProbabilityTheory MeasureTheory ENNReal in
/-- Mathlib d13f23b's `Measure.withDensity_comp`: a density on `κ ∘ₘ μ` moves into the kernel (Boltzmann
PositiveSourceFormula, q141). -/
theorem _root_.MeasureTheory.Measure.withDensity_comp {𝓧 𝓨 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {m𝓨 : MeasurableSpace 𝓨} {μ : Measure 𝓧} {κ : Kernel 𝓧 𝓨} [IsSFiniteKernel κ] {f' : 𝓨 → ℝ≥0∞}
    (hf' : Measurable f') :
    (κ ∘ₘ μ).withDensity f' = (κ.withDensity (fun _ b ↦ f' b)) ∘ₘ μ := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ Eq.symm ?_
  calc ∫⁻ b, g b ∂((κ.withDensity (fun _ b ↦ f' b)) ∘ₘ μ)
      = ∫⁻ a, ∫⁻ b, g b ∂(κ.withDensity (fun _ b ↦ f' b)) a ∂μ :=
        Measure.lintegral_bind (Kernel.measurable _).aemeasurable hg.aemeasurable
    _ = ∫⁻ a, ∫⁻ b, f' b * g b ∂κ a ∂μ := by
        congr with a
        exact Kernel.lintegral_withDensity _ (by fun_prop) _ hg
    _ = ∫⁻ b, f' b * g b ∂(κ ∘ₘ μ) :=
        (Measure.lintegral_bind (Kernel.measurable _).aemeasurable (hf'.mul hg).aemeasurable).symm
    _ = ∫⁻ b, g b ∂((κ ∘ₘ μ).withDensity f') :=
        (lintegral_withDensity_eq_lintegral_mul _ hf' hg).symm
end OAICompat434

end OAI
end

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

/-! # Collision gain as a kernel applied to the incoming hot measure -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem incomingCollisionMeasure_lintegral (μ : Measure (X × (Velocity × Velocity)))
    [SFinite μ] {f : (X × (Velocity × Velocity)) × Sphere → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂incomingCollisionMeasure μ) =
      ∫⁻ p, ∫⁻ ω, ENNReal.ofReal (collisionKernel p.2.1 p.2.2 ω)*f (p,ω)
        ∂sphereArea ∂μ := by
  have hd : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  rw [incomingCollisionMeasure,lintegral_withDensity_eq_lintegral_mul _ hd hf]
  exact lintegral_prod _ (hd.mul hf).aemeasurable

theorem normalPhaseGain_comp (μ : Measure X) [SFinite μ]
    (K H : Kernel X Velocity) [IsSFiniteKernel K] [IsSFiniteKernel H] :
    normalPhaseGainKernel K ∘ₘ (μ ⊗ₘ H) =
      (incomingCollisionMeasure (μ ⊗ₘ (K ×ₖ H))).map incomingLeft+
      (incomingCollisionMeasure (μ ⊗ₘ (K ×ₖ H))).map incomingRight := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,
    Measure.lintegral_compProd (hf.lintegral_kernel),lintegral_add_measure,
    lintegral_map hf incomingLeft_measurable,
    lintegral_map hf incomingRight_measurable,
    incomingCollisionMeasure_lintegral _ (f := fun z => f (incomingLeft z))
      (hf.comp incomingLeft_measurable),
    incomingCollisionMeasure_lintegral _ (f := fun z => f (incomingRight z))
      (hf.comp incomingRight_measurable)]
  have hr : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel normalComponent
    fun_prop
  have hL : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)*f (incomingLeft z)) := by
    exact hr.mul (hf.comp incomingLeft_measurable)
  have hR : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)*f (incomingRight z)) := by
    exact hr.mul (hf.comp incomingRight_measurable)
  rw [Measure.lintegral_compProd (hL.lintegral_prod_right' (ν := sphereArea)),
    Measure.lintegral_compProd (hR.lintegral_prod_right' (ν := sphereArea)),
    ← lintegral_add_left ((hL.lintegral_prod_right' (ν := sphereArea)).lintegral_kernel_prod_right' (κ := K ×ₖ H))]
  apply lintegral_congr
  intro x
  simp_rw [normalPhaseGainKernel_lintegral K _ hf]
  rw [lintegral_add_left]
  · congr 1
    · rw [Kernel.prod_apply,lintegral_prod_symm]
      · rfl
      · exact ((hL.lintegral_prod_right' (ν := sphereArea)).comp (measurable_const.prodMk measurable_id)).aemeasurable
    · rw [Kernel.prod_apply,lintegral_prod_symm]
      · rfl
      · exact ((hR.lintegral_prod_right' (ν := sphereArea)).comp (measurable_const.prodMk measurable_id)).aemeasurable
  · exact (((hL.lintegral_prod_right' (ν := sphereArea)).comp (measurable_const.prodMk
      (measurable_snd.prodMk measurable_fst))).lintegral_prod_right' (ν := K x))

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The normal-angle gain is linear in an arbitrary incoming partner measure -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem normalGainKernel_eq_smul_of_measure_eq
    (K : Kernel X Velocity) (L : Kernel Y Velocity) [IsSFiniteKernel K] [IsSFiniteKernel L]
    (x : X) (y : Y) (v : Velocity) (c : ℝ≥0∞) (h : K x = c • L y) :
    normalGainKernel K (x,v) = c • normalGainKernel L (y,v) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [normalGainKernel_lintegral K (x,v) hf,lintegral_smul_measure,
    normalGainKernel_lintegral L (y,v) hf,h]
  simp only [lintegral_smul_measure,smul_eq_mul,mul_add]

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

section

/-! # Finite positive measure histories below a renewal supersolution -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.PositiveMeasureHistories

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem comp_mono_measure (K : Kernel X Y) {μ ν : Measure X} (h : μ ≤ ν) :
    K ∘ₘ μ ≤ K ∘ₘ ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA K.aemeasurable,Measure.bind_apply hA K.aemeasurable]
  exact lintegral_mono' h le_rfl

theorem historySum_le (K : Kernel X X) {seed μ : Measure X}
    (h : seed+K ∘ₘ μ ≤ μ) (n : ℕ) : historySum K seed n ≤ μ := by
  induction n with
  | zero => exact bot_le
  | succ n ih => exact (add_le_add le_rfl (comp_mono_measure K ih)).trans h

theorem historySum_succ (K : Kernel X X) (seed : Measure X) (n : ℕ) :
    historySum K seed (n+1) = historySum K seed n+(K^n) ∘ₘ seed := by
  induction n with
  | zero =>
    simp only [historySum,pow_zero,zero_add]
    have hz : K ∘ₘ (0 : Measure X) = 0 := by
      ext A hA
      rw [Measure.bind_apply hA K.aemeasurable,lintegral_zero_measure]
      rfl
    rw [hz,add_zero]
    have hid : (1 : Kernel X X) = Kernel.id := rfl
    rw [hid]
    ext A hA
    rw [Measure.bind_apply hA Kernel.id.aemeasurable]
    simp only [Kernel.id_apply,Measure.dirac_apply' _ hA]
    exact (lintegral_indicator_one hA).symm
  | succ n ih =>
    change seed+K ∘ₘ historySum K seed (n+1) =
      (seed+K ∘ₘ historySum K seed n)+(K^(n+1)) ∘ₘ seed
    rw [ih,Measure.comp_add,Measure.comp_assoc]
    have he : (K ∘ₖ (K^n)) = K^(n+1) := (pow_succ' K n).symm
    rw [he]
    change seed+(K ∘ₘ historySum K seed n+(K^(n+1)) ∘ₘ seed) =
      (seed+K ∘ₘ historySum K seed n)+(K^(n+1)) ∘ₘ seed
    exact (add_assoc _ _ _).symm

theorem historySum_eq_sum (K : Kernel X X) (seed : Measure X) (n : ℕ) :
    historySum K seed n = ∑ j ∈ Finset.range n, (K^j) ∘ₘ seed := by
  induction n with
  | zero => simp [historySum]
  | succ n ih => rw [historySum_succ,Finset.sum_range_succ,ih]

theorem finite_histories_le (K : Kernel X X) {seed μ : Measure X}
    (h : seed+K ∘ₘ μ ≤ μ) (n : ℕ) :
    ∑ j ∈ Finset.range n, (K^j) ∘ₘ seed ≤ μ := by
  rw [← historySum_eq_sum]
  exact historySum_le K h n

theorem endpoint_histories_le (K : Kernel X X) (L : Kernel X Y) {seed μ : Measure X}
    (h : seed+K ∘ₘ μ ≤ μ) (n : ℕ) :
    L ∘ₘ (∑ j ∈ Finset.range n, (K^j) ∘ₘ seed) ≤ L ∘ₘ μ :=
  comp_mono_measure L (finite_histories_le K h n)

end BoltzmannNonuniqueness.PositiveMeasureHistories

end

end

section

/-! # A positive gain-and-retention kernel acting on an occupation density -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem positiveSourceKernel_comp_density (K : Kernel X X) [IsSFiniteKernel K]
    (μ : Measure X) {F b r : X → ℝ} (hF : Measurable F) (hFn : ∀ x, 0 ≤ F x)
    (hb : Measurable b) (hr : Measurable r) :
    positiveSourceKernel K b r ∘ₘ positiveDensityMeasure μ F =
      positiveDensityMeasure (K ∘ₘ positiveDensityMeasure μ F) b+
      positiveDensityMeasure μ (fun x => F x*(b x*r x)) := by
  rw [positiveSourceKernel,Measure.add_comp,← Measure.withDensity_comp hb.ennreal_ofReal,
    ← Measure.withDensity_comp (f' := fun x => ENNReal.ofReal (b x*r x))
      (hb.mul hr).ennreal_ofReal]
  have hid : Kernel.id ∘ₘ positiveDensityMeasure μ F = positiveDensityMeasure μ F := by
    rw [Kernel.id,Measure.deterministic_comp_eq_map measurable_id]
    exact Measure.map_id
  rw [hid]
  congr 1
  unfold positiveDensityMeasure
  rw [← withDensity_mul μ (f := fun x => ENNReal.ofReal (F x))
    (g := fun x => ENNReal.ofReal (b x*r x)) hF.ennreal_ofReal (hb.mul hr).ennreal_ofReal]
  congr 1
  funext x
  exact (ENNReal.ofReal_mul (hFn x)).symm

end BoltzmannNonuniqueness

end

end

section

/-! # Finite collision histories below an occupation renewal equation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.PositiveMeasureHistories

variable {X : Type*} [MeasurableSpace X]

theorem restrict_kernel_comp (K : Kernel X X) (μ : Measure X)
    {A : Set X} (hA : MeasurableSet A) :
    K.restrict hA ∘ₘ μ = (K ∘ₘ μ).restrict A := by
  ext S hS
  rw [Measure.bind_apply hS (Kernel.aemeasurable _),Measure.restrict_apply hS,
    Measure.bind_apply (hS.inter hA) K.aemeasurable]
  apply lintegral_congr
  intro x
  rw [Kernel.restrict_apply,Measure.restrict_apply hS]

theorem restricted_source_renewal (K R : Kernel X X)
    {occupation source seed : Measure X} {A : Set X} (hA : MeasurableSet A)
    (hoccupation : occupation.restrict A = R ∘ₘ (seed+source.restrict A))
    (hsource : K ∘ₘ occupation ≤ source) :
    seed+((K.restrict hA) ∘ₖ R) ∘ₘ (seed+source.restrict A) ≤ seed+source.restrict A := by
  apply add_le_add le_rfl
  rw [← Measure.comp_assoc,← hoccupation]
  calc
    K.restrict hA ∘ₘ occupation.restrict A ≤ K.restrict hA ∘ₘ occupation :=
      comp_mono_measure _ Measure.restrict_le_self
    _ = (K ∘ₘ occupation).restrict A := restrict_kernel_comp K occupation hA
    _ ≤ source.restrict A := Measure.restrict_mono_measure hsource A

end BoltzmannNonuniqueness.PositiveMeasureHistories

end

end

section

/-! # Positive density measures under restriction and characteristic transport -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem positiveDensityMeasure_restrict (μ : Measure X) (f : X → ℝ)
    {s : Set X} (hs : MeasurableSet s) :
    positiveDensityMeasure (μ.restrict s) f = positiveDensityMeasure μ (s.indicator f) := by
  unfold positiveDensityMeasure
  rw [← withDensity_indicator hs]
  congr 1
  funext x
  by_cases hx : x ∈ s <;> simp [hx]

theorem positiveDensityMeasure_map_symm (e : X ≃ᵐ Y) {μ : Measure X} {ν : Measure Y}
    (hp : MeasurePreserving e μ ν) {f : Y → ℝ} (hf : Measurable f) :
    (positiveDensityMeasure ν f).map e.symm =
      positiveDensityMeasure μ (fun x => f (e x)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg e.symm.measurable]
  unfold positiveDensityMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal
      (g := fun y => g (e.symm y)) (hg.comp e.symm.measurable),
    lintegral_withDensity_eq_lintegral_mul _ (f := fun x => ENNReal.ofReal (f (e x)))
      (hf.comp e.measurable).ennreal_ofReal hg]
  change (∫⁻ y, ENNReal.ofReal (f y)*g (e.symm y) ∂ν) =
    ∫⁻ x, ENNReal.ofReal (f (e x))*g x ∂μ
  rw [← hp.lintegral_comp (f := fun y => ENNReal.ofReal (f y)*g (e.symm y))
    (hf.ennreal_ofReal.mul (hg.comp e.symm.measurable))]
  apply lintegral_congr
  intro x
  simp only [MeasurableEquiv.symm_apply_apply]

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

theorem measure_comp_mono {K L : Kernel X Y} {μ ν : Measure X}
    (hK : K ≤ L) (hμ : μ ≤ ν) : K ∘ₘ μ ≤ L ∘ₘ ν := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA K.aemeasurable,Measure.bind_apply hA L.aemeasurable]
  exact (lintegral_mono (fun x => hK x A)).trans (lintegral_mono' hμ le_rfl)

end BoltzmannNonuniqueness.KernelHistoryOrder

end

end

section

/-! # A density-valued kernel integrated against its base measure -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem compProd_density_const (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {f : X × Y → ℝ} (hf : Measurable f) :
    μ ⊗ₘ ((Kernel.const X ν).withDensity (fun x y => ENNReal.ofReal (f (x,y)))) =
      positiveDensityMeasure (μ.prod ν) f := by
  apply Measure.ext_of_lintegral
  intro g hg
  have hd : Measurable (Function.uncurry (fun x y => ENNReal.ofReal (f (x,y)))) :=
    hf.ennreal_ofReal
  let _ : IsSFiniteKernel ((Kernel.const X ν).withDensity
      (fun x y => ENNReal.ofReal (f (x,y)))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  rw [Measure.lintegral_compProd hg,positiveDensityMeasure,
    lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal hg,
    lintegral_prod _ (hf.ennreal_ofReal.mul hg).aemeasurable]
  apply lintegral_congr
  intro x
  rw [Kernel.withDensity_apply _ hd]
  exact lintegral_withDensity_eq_lintegral_mul _
    (hf.ennreal_ofReal.comp (measurable_const.prodMk measurable_id))
    (hg.comp (measurable_const.prodMk measurable_id))

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedMediumStateCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedChildKernel_isMarkov _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumCollisionKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.mediumMarkedKernel_isSFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalChildKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual active cold measure equals the normalized two-beam measure -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem background_eq_beamMeasure {θ K α γ r t : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (ht : 0 ≤ t) (η l : ℝ) (x : Velocity) (ha : active θ η l (transverse x)) :
    background θ η l K α γ t (transverse x,axial x) =
      ENNReal.ofReal (K/(4*r)) •
        ReferenceGeometry.beamMeasure (beamCoefficients hθ hα hγ η r) (t,x) := by
  have hfactor : 0 ≤ K/(4*r) := by positivity
  have hw (σ : ℝ) : K/(4*r)*beamDensity θ η α γ r σ (t,x) =
      AxialBackground.weight K α γ (scale θ η (transverse x)) t σ (axial x) := by
    unfold beamDensity
    rw [max_eq_right ht]
    unfold AxialBackground.weight JetCoreDensity.compressed
    field_simp
  rw [background,ite_eq_left ha]
  change AxialBackground.cell K α γ (scale θ η (transverse x)) t (axial x) = _
  rw [AxialBackground.cell,ReferenceGeometry.beamMeasure,smul_add]
  congr 1
  · change ENNReal.ofReal (AxialBackground.weight K α γ (scale θ η (transverse x)) t 1 (axial x)) •
        Measure.dirac (PlaneChart.join 0 (AxialFlow.velocity 1 α γ (scale θ η (transverse x)) t (axial x))) =
      ENNReal.ofReal (K/(4*r)) • (ENNReal.ofReal (beamDensity θ η α γ r 1 (t,x)) •
        Measure.dirac (beamVelocity θ η α γ 1 (t,x)))
    rw [smul_smul,← ENNReal.ofReal_mul hfactor,hw]
    simp only [beamVelocity,max_eq_right ht]
  · change ENNReal.ofReal (AxialBackground.weight K α γ (scale θ η (transverse x)) t (-1) (axial x)) •
        Measure.dirac (PlaneChart.join 0 (AxialFlow.velocity (-1) α γ (scale θ η (transverse x)) t (axial x))) =
      ENNReal.ofReal (K/(4*r)) • (ENNReal.ofReal (beamDensity θ η α γ r (-1) (t,x)) •
        Measure.dirac (beamVelocity θ η α γ (-1) (t,x)))
    rw [smul_smul,← ENNReal.ofReal_mul hfactor,hw]
    simp only [beamVelocity,max_eq_right ht]

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

theorem ae_not_mesh_circle (θ η : ℝ) :
    ∀ᵐ y : Transverse ∂volume, ∀ k : ℤ, ‖y‖ ≠ GeometricMesh.point θ η k := by
  apply ae_all_iff.mpr
  intro k
  apply ae_iff.mpr
  have he : {y : Transverse | ¬‖y‖ ≠ GeometricMesh.point θ η k} =
      Metric.sphere 0 (GeometricMesh.point θ η k) := by
    ext y
    simp only [not_not,mem_ofPred_eq,Metric.mem_sphere,dist_zero_right]
  rw [he]
  exact Measure.addHaar_sphere volume 0 _

theorem active_ae_above_cutoff {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (l : ℝ) :
    ∀ᵐ y : Transverse ∂volume, 0 < ‖y‖ → Real.exp η*l < ‖y‖ → active θ η l y := by
  filter_upwards [ae_not_mesh_circle θ η] with y hy hpos hcut
  have hb := GeometricMesh.cell_bounds hθ hη hpos
  have hstrict : scale θ η y < ‖y‖ :=
    lt_of_le_of_ne hb.1 (hy (GeometricMesh.index (‖y‖/θ) η)).symm
  refine ⟨?_,hstrict,hb.2⟩
  exact (mul_lt_mul_iff_right₀ (Real.exp_pos η)).mp (hcut.trans hb.2)

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricDampedRetention
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamPartnerKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedDensityScaledEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedBoundedPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedDensityScaledEventKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_pow_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalBeamEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalMarkedWord_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalWaitingKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual cold frequency is controlled by the nearby two-beam clock -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem beamMeasure_integral (b : BeamCoefficients) (p : ℝ × V)
    (hp : 0 ≤ b.plusDensity p) (hm : 0 ≤ b.minusDensity p) (f : V → ℝ) :
    (∫ v, f v ∂beamMeasure b p) =
      b.plusDensity p*f (b.plusPartner p)+b.minusDensity p*f (b.minusPartner p) := by
  have hi (c : ℝ) (w : V) : Integrable f (ENNReal.ofReal c • Measure.dirac w) :=
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top
  rw [beamMeasure,integral_add_measure (hi _ _) (hi _ _)]
  simp only [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal hp,
    ENNReal.toReal_ofReal hm,smul_eq_mul]

end BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.GeometricBackground

open ReferenceGeometry

theorem frequency_eq_beamFrequency {θ K α γ r t : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hr : 0 < r)
    (ht : 0 ≤ t) (η l : ℝ) (x v : Velocity) (ha : active θ η l (transverse x)) :
    frequency θ η l K α γ t (transverse x,axial x) v =
      (K/(4*r))*mediumFrequency v
        ((beamCoefficients hθ hα hγ η r).plusPartner (t,x))
        ((beamCoefficients hθ hα hγ η r).minusPartner (t,x))
        ((beamCoefficients hθ hα hγ η r).plusDensity (t,x))
        ((beamCoefficients hθ hα hγ η r).minusDensity (t,x)) := by
  rw [frequency,background_eq_beamMeasure hθ hK hα hγ hr ht η l x ha,
    integral_smul_measure,ENNReal.toReal_ofReal (by positivity),smul_eq_mul,
    beamMeasure_integral _ _ (beamDensity_nonneg hθ hα hγ hr.le η 1 (t,x))
      (beamDensity_nonneg hθ hα hγ hr.le η (-1) (t,x))]
  unfold mediumFrequency
  ring

end BoltzmannNonuniqueness.GeometricBackground

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CharacteristicCutoffGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Transport of collision kernels into characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem transportedKernel_comp (e : X ≃ᵐ Y) (K : Kernel Y Y) (μ : Measure Y) :
    transportedKernel e K ∘ₘ μ.map e.symm = (K ∘ₘ μ).map e.symm := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    lintegral_map ((transportedKernel e K).measurable_coe hA) e.symm.measurable,
    Measure.map_apply e.symm.measurable hA,
    Measure.bind_apply (e.symm.measurable hA) K.aemeasurable]
  apply lintegral_congr
  intro y
  simp only [transportedKernel,Kernel.map_apply' _ e.symm.measurable _ hA,
    Kernel.comap_apply,MeasurableEquiv.apply_symm_apply]

end BoltzmannNonuniqueness

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveContributionsIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A cutoff equal to one preserves every collision ending in its core -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem withDensity_restrict_le_of_core (μ : Measure X) {f g : X → ℝ≥0∞}
    {A : Set X} (hA : MeasurableSet A) (hfg : ∀ x ∈ A, f x ≤ g x) :
    (μ.withDensity f).restrict A ≤ μ.withDensity g := by
  rw [restrict_withDensity hA,← withDensity_indicator hA]
  apply withDensity_mono
  exact Filter.Eventually.of_forall (fun x => by
    by_cases hx : x ∈ A
    · simpa only [indicator_of_mem hx] using hfg x hx
    · simp only [indicator_of_notMem hx]
      exact bot_le)

theorem positiveSourceKernel_restrict_le (K : Kernel X X) [IsSFiniteKernel K]
    {b r : X → ℝ} (hb : Measurable b) (hr : Measurable r) {A : Set X}
    (hA : MeasurableSet A) (hcore : ∀ x ∈ A, b x = 1) :
    (positiveSourceKernel K (fun _ => 1) r).restrict hA ≤ positiveSourceKernel K b r := by
  intro x
  rw [Kernel.restrict_apply,positiveSourceKernel,positiveSourceKernel,add_apply,add_apply,
    Measure.restrict_add]
  apply add_le_add
  · rw [Kernel.withDensity_apply (f := fun (_ : X) (_ : X) => ENNReal.ofReal (1:ℝ)) K (by fun_prop),
      Kernel.withDensity_apply (f := fun (_ : X) y => ENNReal.ofReal (b y)) K (by fun_prop)]
    apply withDensity_restrict_le_of_core _ hA
    intro y hy
    simp only [hcore y hy]
    exact le_rfl
  · rw [Kernel.withDensity_apply (f := fun (_ : X) y => ENNReal.ofReal ((1:ℝ)*r y)) Kernel.id (by fun_prop),
      Kernel.withDensity_apply (f := fun (_ : X) y => ENNReal.ofReal (b y*r y)) Kernel.id (by fun_prop)]
    apply withDensity_restrict_le_of_core _ hA
    intro y hy
    simp only [hcore y hy,one_mul]
    exact le_rfl

end BoltzmannNonuniqueness

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_OccupationSliceIntegral
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A spacetime occupation measure disintegrated into phase slices -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

theorem occupation_slice_lintegral {F : ℝ × Phase → ℝ} (hF : Measurable F)
    (s b : ℝ) {f : ℝ × Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂(positiveDensityMeasure volume F).restrict (Prod.fst ⁻¹' Ioc s b)) =
      ∫⁻ t in Ioc s b, ∫⁻ p, f (t,p) ∂phaseSlice F t := by
  have he : Prod.fst ⁻¹' Ioc s b = Ioc s b ×ˢ (univ : Set Phase) := by ext; simp
  rw [positiveDensityMeasure,restrict_withDensity (measurable_fst measurableSet_Ioc),
    Measure.volume_eq_prod,he,← Measure.restrict_prod_eq_prod_univ,
    lintegral_withDensity_eq_lintegral_mul _ hF.ennreal_ofReal hf,
    lintegral_prod _ (hF.ennreal_ofReal.mul hf).aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [phaseSlice,positiveDensityMeasure]
  exact (lintegral_withDensity_eq_lintegral_mul _
    (f := fun p => ENNReal.ofReal (F (t,p)))
    (g := fun p => f (t,p))
    (hF.ennreal_ofReal.comp (measurable_const.prodMk measurable_id))
    (hf.comp (measurable_const.prodMk measurable_id))).symm

end BoltzmannNonuniqueness.WeakTime

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

/-! # Collision-time integrals for the positive Duhamel source -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

theorem dampedSourceIncrement_lintegral (μ : Measure (ℝ × Phase))
    {a b C s t : ℝ} (hs : a < s) (ht : t < b) {ψ : Phase → ℝ≥0∞} (hψ : Measurable ψ) :
    (∫⁻ p, ψ p ∂dampedSourceIncrement a b C s t μ) =
      ∫⁻ z in Prod.fst ⁻¹' Ioc s t,
        ENNReal.ofReal (Real.exp (-C*(t-z.1)))*ψ z.2 ∂μ := by
  have hW : Measurable (fun z : ℝ × Phase => ENNReal.ofReal (slabExponential a b C z.1)) := by
    simpa only [Function.comp_def] using
      ((slabExponential_measurable a b C).comp measurable_fst).ennreal_ofReal
  have hp : Measurable (fun z : ℝ × Phase => ψ z.2) := by
    simpa only [Function.comp_def] using hψ.comp measurable_snd
  rw [dampedSourceIncrement,lintegral_smul_measure,phaseIncrement,
    lintegral_map hψ measurable_snd]
  change ENNReal.ofReal (Real.exp (-C*t))*
    (∫⁻ z in Prod.fst ⁻¹' Ioc s t, ψ z.2
      ∂positiveDensityMeasure μ (fun z => slabExponential a b C z.1)) = _
  rw [positiveDensityMeasure,restrict_withDensity (measurable_fst measurableSet_Ioc),
    lintegral_withDensity_eq_lintegral_mul _ hW hp,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurable_fst measurableSet_Ioc)] with z hz
  have hab : z.1 ∈ Ioo a b := ⟨hs.trans hz.1,hz.2.trans_lt ht⟩
  change ENNReal.ofReal (Real.exp (-C*t)) *
    (ENNReal.ofReal (slabExponential a b C z.1)*ψ z.2) = _
  rw [slabExponential,indicator_of_mem hab,← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring_nf

end BoltzmannNonuniqueness.WeakTime

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

section

/-! # Initial phase measures and their free-flight occupation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

theorem residence_seed_lintegral (C b s : ℝ) (μ : Measure Phase) [SFinite μ]
    {f : ℝ × Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f z ∂(residenceKernel C b ∘ₘ phaseSeed s μ)) =
      ∫⁻ t in Ioc s b, ENNReal.ofReal (Real.exp (C*(s-t)))*(∫⁻ p, f (t,p) ∂μ) := by
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,phaseSeed,
    lintegral_map hf.lintegral_kernel
      (show Measurable (fun p : Phase => (s,p)) from measurable_const.prodMk measurable_id)]
  simp_rw [residenceKernel_lintegral C b _ hf]
  have he : Measurable (fun q : Phase × ℝ => ENNReal.ofReal (Real.exp (C*(s-q.2)))) := by
    fun_prop
  have hm : Measurable (fun q : Phase × ℝ =>
      ENNReal.ofReal (Real.exp (C*(s-q.2)))*f (q.2,q.1)) :=
    he.mul (hf.comp measurable_swap)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t ht
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

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

theorem endpoint_source_comp (μ : Measure (ℝ × Phase))
    {a B C s t : ℝ} (hs : a < s) (ht : t < B) :
    phaseEndpointKernel C t ∘ₘ μ.restrict (Prod.fst ⁻¹' Ioc s t) =
      dampedSourceIncrement a B C s t μ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,
    dampedSourceIncrement_lintegral μ hs ht hf]
  apply setLIntegral_congr_fun (measurable_fst measurableSet_Ioc)
  intro z hz
  dsimp only
  rw [phaseEndpointKernel_lintegral C t z hf,
    show C*(z.1-t) = -C*(t-z.1) by ring]

theorem endpoint_seed_comp (C t s : ℝ) (μ : Measure Phase) :
    phaseEndpointKernel C t ∘ₘ phaseSeed s μ =
      ENNReal.ofReal (Real.exp (C*(s-t))) • μ := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable,phaseSeed,
    lintegral_map hf.lintegral_kernel
      (show Measurable (fun p : Phase => (s,p)) from measurable_const.prodMk measurable_id),
    lintegral_smul_measure,smul_eq_mul]
  simp_rw [phaseEndpointKernel_lintegral C t _ hf]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Interchanging source time and observation time in the damped flow -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.WeakTime

theorem triangular_time_integral (s b r : ℝ) (g : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc s b, (Ioc s t).indicator (fun _ => g t) r) =
      (Ioc s b).indicator (fun r => ∫⁻ t in Ioc r b, g t) r := by
  by_cases hr : r ∈ Ioc s b
  · rw [indicator_of_mem hr,← lintegral_indicator measurableSet_Ioc,
      ← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr_ae
    filter_upwards [Measure.ae_ne (volume : Measure ℝ) r] with t htr
    by_cases ht : t ∈ Ioc r b
    · have hsb : t ∈ Ioc s b := ⟨hr.1.trans ht.1,ht.2⟩
      have hst : r ∈ Ioc s t := ⟨hr.1,ht.1.le⟩
      simp [ht,hsb,hst]
    · by_cases hsb : t ∈ Ioc s b
      · have hst : r ∉ Ioc s t := by
          intro hst
          apply ht
          exact ⟨lt_of_le_of_ne hst.2 (Ne.symm htr),hsb.2⟩
        simp [ht,hsb,hst]
      · simp [ht,hsb]
  · rw [indicator_of_notMem hr]
    apply setLIntegral_eq_zero measurableSet_Ioc
    intro t ht
    have hst : r ∉ Ioc s t := fun hst => hr ⟨hst.1,hst.2.trans ht.2⟩
    simp [hst]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Time-integrated Duhamel sources are residence-kernel measures -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

theorem dampedSource_time_integral (μ : Measure (ℝ × Phase)) [SFinite μ]
    {a B C s b : ℝ} (hs : a < s) (hb : b < B)
    {f : ℝ × Phase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ t in Ioc s b, ∫⁻ p, f (t,p) ∂dampedSourceIncrement a B C s t μ) =
      ∫⁻ p, f p ∂(residenceKernel C b ∘ₘ μ.restrict (Prod.fst ⁻¹' Ioc s b)) := by
  let G : ℝ × (ℝ × Phase) → ℝ≥0∞ := fun q =>
    (Ioc s q.1).indicator
      (fun _ => ENNReal.ofReal (Real.exp (C*(q.2.1-q.1)))*f (q.1,q.2.2)) q.2.1
  have hg : Measurable G := by
    have hset : MeasurableSet {q : ℝ × (ℝ × Phase) | s < q.2.1 ∧ q.2.1 ≤ q.1} :=
      (measurableSet_lt measurable_const measurable_snd.fst).inter
        (measurableSet_le measurable_snd.fst measurable_fst)
    have hexp : Measurable (fun q : ℝ × (ℝ × Phase) =>
        ENNReal.ofReal (Real.exp (C*(q.2.1-q.1)))) := by fun_prop
    have hv : Measurable (fun q : ℝ × (ℝ × Phase) =>
        ENNReal.ofReal (Real.exp (C*(q.2.1-q.1)))*f (q.1,q.2.2)) :=
      hexp.mul (hf.comp (measurable_fst.prodMk measurable_snd.snd))
    have he : G = {q : ℝ × (ℝ × Phase) | s < q.2.1 ∧ q.2.1 ≤ q.1}.indicator
        (fun q => ENNReal.ofReal (Real.exp (C*(q.2.1-q.1)))*f (q.1,q.2.2)) := by
      funext q
      by_cases hq : s < q.2.1 ∧ q.2.1 ≤ q.1 <;> simp [G,hq]
    rw [he]
    exact hv.indicator hset
  calc
    _ = ∫⁻ t in Ioc s b, ∫⁻ z, G (t,z) ∂μ := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only
      rw [dampedSourceIncrement_lintegral μ hs (ht.2.trans_lt hb)
        (ψ := fun p => f (t,p)) (hf.comp (measurable_const.prodMk measurable_id)),
        ← lintegral_indicator (measurable_fst measurableSet_Ioc)]
      apply lintegral_congr
      intro z
      by_cases hz : z.1 ∈ Ioc s t
      · have hz' : z ∈ Prod.fst ⁻¹' Ioc s t := hz
        simp only [G,indicator_of_mem hz,indicator_of_mem hz']
        rw [show -C*(t-z.1) = C*(z.1-t) by ring]
      · have hz' : z ∉ Prod.fst ⁻¹' Ioc s t := hz
        simp only [G,indicator_of_notMem hz,indicator_of_notMem hz']
    _ = ∫⁻ z, ∫⁻ t in Ioc s b, G (t,z) ∂volume ∂μ :=
      lintegral_lintegral_swap hg.aemeasurable
    _ = ∫⁻ z in Prod.fst ⁻¹' Ioc s b,
        ∫⁻ t in Ioc z.1 b, ENNReal.ofReal (Real.exp (C*(z.1-t)))*f (t,z.2) ∂volume ∂μ := by
      rw [← lintegral_indicator (measurable_fst measurableSet_Ioc)]
      apply lintegral_congr
      intro z
      exact triangular_time_integral s b z.1 _
    _ = _ := by
      rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
      apply setLIntegral_congr_fun (measurable_fst measurableSet_Ioc)
      intro z hz
      exact (residenceKernel_lintegral C b z hf).symm

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Integrating a Duhamel trace into a positive occupation equation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

theorem occupation_eq_residence {F : ℝ × Phase → ℝ} (hF : Measurable F)
    (seed : Measure Phase) [SFinite seed] (source : Measure (ℝ × Phase)) [SFinite source]
    {a B C s b : ℝ} (hs : a < s) (hb : b < B)
    (h : ∀ᵐ t ∂volume, t ∈ Ioc s b →
      phaseSlice F t = ENNReal.ofReal (Real.exp (C*(s-t))) • seed+
        dampedSourceIncrement a B C s t source) :
    (positiveDensityMeasure volume F).restrict (Prod.fst ⁻¹' Ioc s b) =
      residenceKernel C b ∘ₘ (phaseSeed s seed+source.restrict (Prod.fst ⁻¹' Ioc s b)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [occupation_slice_lintegral hF s b hf,Measure.comp_add,lintegral_add_measure,
    residence_seed_lintegral C b s seed hf,← dampedSource_time_integral source hs hb hf]
  have he : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (C*(s-t)))) := by fun_prop
  have hm : Measurable (fun t =>
      ENNReal.ofReal (Real.exp (C*(s-t)))*(∫⁻ p, f (t,p) ∂seed)) :=
    he.mul (hf.lintegral_prod_right' (ν := seed))
  rw [← lintegral_add_left hm]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae h,ae_restrict_mem measurableSet_Ioc] with t ht htb
  rw [ht htb,lintegral_add_measure,lintegral_smul_measure,smul_eq_mul]

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Endpoint domination by every finite positive history sum -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.WeakTime

theorem endpoint_finite_histories (K R : Kernel (ℝ × Phase) (ℝ × Phase))
    (occupation source : Measure (ℝ × Phase)) (seed endpoint : Measure Phase)
    {a B C s t : ℝ} (hs : a < s) (ht : t < B)
    (hoccupation : occupation.restrict (Prod.fst ⁻¹' Ioc s t) =
      R ∘ₘ (phaseSeed s seed+source.restrict (Prod.fst ⁻¹' Ioc s t)))
    (hsource : K ∘ₘ occupation ≤ source)
    (hendpoint : endpoint = ENNReal.ofReal (Real.exp (C*(s-t))) • seed+
      dampedSourceIncrement a B C s t source) (n : ℕ) :
    phaseEndpointKernel C t ∘ₘ
      (∑ j ∈ Finset.range n,
        ((((K.restrict (measurable_fst measurableSet_Ioc :
          MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ R)^j) ∘ₘ phaseSeed s seed)) ≤ endpoint := by
  have hrenew := PositiveMeasureHistories.restricted_source_renewal K R
    (measurable_fst measurableSet_Ioc) hoccupation hsource
  have hh := PositiveMeasureHistories.endpoint_histories_le _ (phaseEndpointKernel C t) hrenew n
  rw [Measure.comp_add,endpoint_seed_comp,endpoint_source_comp source hs ht,← hendpoint] at hh
  exact hh

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

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricEntry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual beam representation holds almost everywhere along characteristics -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem active_ae_velocity {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (l : ℝ) :
    ∀ᵐ x : Velocity ∂volume, 0 < ‖transverse x‖ →
      Real.exp η*l < ‖transverse x‖ → active θ η l (transverse x) := by
  have h := (MeasureTheory.QuasiMeasurePreserving.snd
    split_measurePreserving.quasiMeasurePreserving).ae (active_ae_above_cutoff hθ hη l)
  simpa only [split_apply] using h

theorem active_ae_characteristic {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (l : ℝ) :
    ∀ᵐ z : CharacteristicPhase ∂volume,
      0 < ‖transverse (z.2.1+z.1 • z.2.2)‖ →
      Real.exp η*l < ‖transverse (z.2.1+z.1 • z.2.2)‖ →
      active θ η l (transverse (z.2.1+z.1 • z.2.2)) := by
  have ht : ∀ᵐ p : ℝ × Velocity ∂volume,
      0 < ‖transverse p.2‖ → Real.exp η*l < ‖transverse p.2‖ →
      active θ η l (transverse p.2) :=
    (Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)).ae
      (active_ae_velocity hθ hη l)
  have hk : ∀ᵐ p : Published.KineticPhase ∂volume,
      0 < ‖transverse p.1.2‖ → Real.exp η*l < ‖transverse p.1.2‖ →
      active θ η l (transverse p.1.2) :=
    (Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)).ae ht
  exact (characteristic_measurePreserving volume).quasiMeasurePreserving.ae hk

end BoltzmannNonuniqueness.GeometricBackground

end

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PhaseSliceLocalization
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing phase and spatial cutoffs from the masses in a covered box -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem cylinder_phaseSlice_le {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ}
    (hf : ∀ z, 0 ≤ f z) {β : WeakTime.Phase → ℝ}
    (hβ₁ : ∀ p, β p ≤ 1) (a A R t : ℝ) :
    WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R f)) t ≤ hotPhaseSlice f t := by
  apply withDensity_mono
  apply ae_of_all
  intro p
  apply ENNReal.ofReal_le_ofReal
  change β p*(JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R).indicator f
    (hotCharacteristicEquiv (t,p)) ≤ f (hotCharacteristicEquiv (t,p))
  by_cases hp : hotCharacteristicEquiv (t,p) ∈ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R
  · rw [indicator_of_mem hp]
    exact (mul_le_mul_of_nonneg_right (hβ₁ p) (hf _)).trans_eq (one_mul _)
  · rw [indicator_of_notMem hp,mul_zero]
    exact hf _

theorem cylinder_phaseSlice_eq_on {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ}
    {β : WeakTime.Phase → ℝ} {a A R t : ℝ} {B : Set WeakTime.Phase}
    (hB : MeasurableSet B) (hβ : ∀ p ∈ B, β p = 1)
    (hcover : ∀ p ∈ tsupport β,
      hotCharacteristicEquiv (t,p) ∈ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R) :
    WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R f)) t B =
      hotPhaseSlice f t B := by
  unfold WeakTime.phaseSlice hotPhaseSlice positiveDensityMeasure
  rw [withDensity_apply _ hB,withDensity_apply _ hB]
  apply setLIntegral_congr_fun hB
  intro p hp
  have hc := hcover p (subset_tsupport β (show β p ≠ 0 by rw [hβ p hp]; norm_num))
  simp only [WeakTime.phaseWeight,cylinderPullback,Function.comp_apply,
    indicator_of_mem hc,hβ p hp,one_mul]

end BoltzmannNonuniqueness.EuclideanFlight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveEndpointHistory
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive finite endpoint histories transfer positive seed mass to the hot trace -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace BoltzmannNonuniqueness

theorem positive_endpoint_of_pointwise
    (K : Kernel (ℝ × WeakTime.Phase) WeakTime.Phase)
    (μ ν : Measure WeakTime.Phase) (s : ℝ) {A B : Set WeakTime.Phase}
    (hA : MeasurableSet A) (hmass : 0 < μ B)
    (hdom : K ∘ₘ WeakTime.phaseSeed s μ ≤ ν)
    (hpoint : ∀ p ∈ B, 0 < K (s,p) A) : 0 < ν A := by
  have hf : Measurable (fun p : WeakTime.Phase => K (s,p) A) :=
    (K.measurable_coe hA).comp (by fun_prop)
  have hp : 0 < ∫⁻ p, K (s,p) A ∂μ := (lintegral_pos_iff_support hf).mpr
    (hmass.trans_le (measure_mono (fun p hp => ne_of_gt (hpoint p hp))))
  have hh := hdom A
  rw [Measure.bind_apply hA K.aemeasurable,WeakTime.phaseSeed,
    lintegral_map (K.measurable_coe hA) (show Measurable (fun p : WeakTime.Phase => (s,p)) by fun_prop)] at hh
  exact hp.trans_le hh

theorem single_endpoint_history_le
    (K : Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase))
    (L : Kernel (ℝ × WeakTime.Phase) WeakTime.Phase)
    (μ : Measure (ℝ × WeakTime.Phase)) (ν : Measure WeakTime.Phase) (N : ℕ)
    (hdom : L ∘ₘ (∑ j ∈ Finset.range (N+1), (K^j) ∘ₘ μ) ≤ ν) :
    (L ∘ₖ (K^N)) ∘ₘ μ ≤ ν := by
  have hterm : (K^N) ∘ₘ μ ≤ ∑ j ∈ Finset.range (N+1), (K^j) ∘ₘ μ :=
    Finset.single_le_sum (f := fun j : ℕ => (K^j) ∘ₘ μ) (fun j _ => bot_le) (Finset.mem_range.mpr (Nat.lt_succ_self N))
  rw [← Measure.comp_assoc]
  exact (KernelHistoryOrder.measure_comp_mono le_rfl hterm).trans hdom

open EuclideanFlight in
 theorem covered_hot_positive_history
    {f : JetCopyDatum.AttainedCapSequence.HotKineticPhase → ℝ} (hf : ∀ z, 0 ≤ f z)
    {β : WeakTime.Phase → ℝ} (hβ₁ : ∀ p, β p ≤ 1)
    (a U R s t : ℝ) {A B : Set WeakTime.Phase} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hβ : ∀ p ∈ B, β p = 1)
    (hcover : ∀ p ∈ tsupport β, hotCharacteristicEquiv (s,p) ∈
      JetCopyDatum.AttainedCapSequence.coldCylinderSet a U R)
    (K : Kernel (ℝ × WeakTime.Phase) (ℝ × WeakTime.Phase)) (C : ℝ) (N : ℕ)
    (hmass : 0 < hotPhaseSlice f s B)
    (hdom : WeakTime.phaseEndpointKernel C t ∘ₘ
      (∑ j ∈ Finset.range (N+1), (K^j) ∘ₘ WeakTime.phaseSeed s
        (WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a U R f)) s)) ≤
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a U R f)) t)
    (hpoint : ∀ p ∈ B, 0 < (WeakTime.phaseEndpointKernel C t ∘ₖ (K^N)) (s,p) A) :
    0 < hotPhaseSlice f t A := by
  have heq := cylinder_phaseSlice_eq_on (f := f) hB hβ hcover
  have hm : 0 < WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a U R f)) s B :=
    heq.symm ▸ hmass
  exact (positive_endpoint_of_pointwise _ _ _ s hA hm
    (single_endpoint_history_le K _ _ _ N hdom) hpoint).trans_le
      (cylinder_phaseSlice_le hf hβ₁ a U R t A)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_CapCoefficientExtraction
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual characteristic gain is the physical normal-angle kernel source -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory
open BoltzmannNonuniqueness.CollisionCompactness BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness

theorem CollisionCompactness.two_smul_incomingGain
    {X : Type*} [MeasurableSpace X] (μ : Measure (X × (Velocity × Velocity))) :
    (2 : ℝ≥0) • incomingGainMeasure μ =
      (incomingCollisionMeasure μ).map incomingLeft+
      (incomingCollisionMeasure μ).map incomingRight := by
  change (2 : ℝ≥0∞) • ((1/2 : ℝ≥0∞) •
    ((incomingCollisionMeasure μ).map incomingLeft+
      (incomingCollisionMeasure μ).map incomingRight)) = _
  rw [smul_smul,one_div,ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by simp),one_smul]

namespace JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicGain_eq_normal (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    E.characteristicGainMeasure ha hK hα hγ A R =
      sourcePullback (normalPhaseGainKernel
        (GeometricBackground.slabKernel ha (zero_lt_one.trans_le E.phase_mem.1)
          hK hα hγ η E.fraction) ∘ₘ (coldCylinderVolume a A R ⊗ₘ E.hotKernel)) := by
  let κ := GeometricBackground.slabKernel ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  rw [normalPhaseGain_comp]
  change (2 : ℝ≥0) • sourcePullback (incomingGainMeasure
    (coldCylinderVolume a A R ⊗ₘ (κ ×ₖ E.hotKernel))) = _
  rw [← two_smul_incomingGain]
  exact (Measure.map_smul (2 : ℝ≥0) _ _).symm

end JetCopyDatum.AttainedCapSequence
end BoltzmannNonuniqueness

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

/-! # The actual hot occupation measure in physical and characteristic coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.hotOccupation_eq_density (E : HotLimitExtraction S)
    (μ : Measure (ℝ × JetPrototype.Space)) [SFinite μ] :
    μ ⊗ₘ E.hotKernel = positiveDensityMeasure (μ.prod volume) E.cappedHot :=
  compProd_density_const μ volume E.cappedHot_measurable

theorem HotLimitExtraction.hotOccupation_cylinder (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 ≤ a) :
    coldCylinderVolume a A R ⊗ₘ E.hotKernel =
      positiveDensityMeasure ((coldCylinderVolume a A R).prod volume) E.hotLimit := by
  rw [E.hotOccupation_eq_density]
  apply withDensity_congr_ae
  have he : E.cappedHot =ᵐ[(coldCylinderVolume a A R).prod volume] E.hotLimit := by
    rw [coldCylinderVolume_eq_hot_restrict ha]
    exact (E.cappedHot_eq A R).filter_mono ae_restrict_le
  exact he.fun_comp ENNReal.ofReal

theorem HotLimitExtraction.hotOccupation_characteristic (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 ≤ a) :
    sourcePullback (coldCylinderVolume a A R ⊗ₘ E.hotKernel) =
      positiveDensityMeasure volume (cylinderPullback a A R E.hotLimit) := by
  rw [E.hotOccupation_cylinder ha,coldCylinderVolume_eq,
    positiveDensityMeasure_restrict _ _ (coldCylinderSet_measurable a A R)]
  exact positiveDensityMeasure_map_symm hotCharacteristicEquiv
    hotCharacteristic_measurePreserving
    (E.hotLimit_measurable.indicator (coldCylinderSet_measurable a A R))

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual characteristic collision source acts on the actual hot density -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicGain_eq_kernel (E : HotLimitExtraction S)
    {a A R : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) :
    E.characteristicGainMeasure ha hK hα hγ A R =
      E.characteristicGainKernel ha hK hα hγ ∘ₘ
        positiveDensityMeasure volume (cylinderPullback a A R E.hotLimit) := by
  rw [← E.hotOccupation_characteristic ha.le]
  exact (E.characteristicGain_eq_normal ha hK hα hγ).trans
    (transportedKernel_comp hotCharacteristicEquiv _ _).symm

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

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

section

/-! # The actual normal-angle hot source equals the active two-beam source -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem hotCharacteristic_jump (z : CharacteristicPhase) (v : Velocity) :
    hotCharacteristicEquiv.symm ((hotCharacteristicEquiv z).1,v) =
      characteristicBeamJump z v := by
  apply hotCharacteristicEquiv.injective
  rw [MeasurableEquiv.apply_symm_apply]
  change ((z.1,spaceEquiv (z.2.1+z.1 • z.2.2)),v) =
    ((z.1,spaceEquiv ((z.2.1+z.1 • z.2.2-z.1 • v)+z.1 • v)),v)
  rw [sub_add_cancel]

end BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicGainKernel_lintegral_normal
    (E : HotLimitExtraction S) {a : ℝ} (ha : 0 < a)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (z : CharacteristicPhase)
    {f : CharacteristicPhase → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂E.characteristicGainKernel ha hK hα hγ z) =
      ∫⁻ v, f (characteristicBeamJump z v)
        ∂normalGainKernel (GeometricBackground.slabKernel ha
          (zero_lt_one.trans_le E.phase_mem.1) hK hα hγ η E.fraction)
          ((hotCharacteristicEquiv z).1,z.2.2) := by
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  rw [HotLimitExtraction.characteristicGainKernel,transportedKernel_lintegral _ _ z hf,
    normalPhaseGainKernel_lintegral_gain _ _
      (f := fun y => f (hotCharacteristicEquiv.symm y)) (hf.comp hotCharacteristicEquiv.symm.measurable)]
  apply lintegral_congr
  intro v
  rw [hotCharacteristic_jump]

theorem HotLimitExtraction.characteristicGainKernel_eq_normal_beam
    (E : HotLimitExtraction S) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (z : CharacteristicPhase)
    (ht : a ≤ z.1)
    (hactive : GeometricBackground.active E.phase η E.fraction
      (transverse (z.2.1+z.1 • z.2.2))) :
    E.characteristicGainKernel ha hK hα hγ z = ENNReal.ofReal (K/(4*r)) •
      beamNormalCharacteristicKernel
        (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
          hα.le hγ.le η r) z := by
  let b := GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
    hα.le hγ.le η r
  let L := GeometricBackground.slabKernel ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction
  let _ := GeometricBackground.slabKernel_finite ha (zero_lt_one.trans_le E.phase_mem.1)
    hK hα hγ η E.fraction_mem.1
  have he : L (hotCharacteristicEquiv z).1 =
      ENNReal.ofReal (K/(4*r)) • beamPartnerKernel b (characteristicBeamPoint z) := by
    rw [beamPartnerKernel_apply]
    change GeometricBackground.background E.phase η E.fraction K α γ
      (max a z.1) (spaceEquiv (z.2.1+z.1 • z.2.2)) = _
    rw [max_eq_right ht,spaceEquiv_apply]
    exact GeometricBackground.background_eq_beamMeasure
      (zero_lt_one.trans_le E.phase_mem.1) hK hα.le hγ.le hr (ha.le.trans ht)
      η E.fraction _ hactive
  apply Measure.ext_of_lintegral
  intro f hf
  rw [E.characteristicGainKernel_lintegral_normal ha hK hα hγ z hf,
    lintegral_smul_measure,beamNormalCharacteristicKernel_lintegral _ z hf]
  rw [normalGainKernel_eq_smul_of_measure_eq L (beamPartnerKernel b)
    (hotCharacteristicEquiv z).1 (characteristicBeamPoint z) z.2.2 _ he,
    lintegral_smul_measure,smul_eq_mul]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Retaining full support coverage in the damped hot balance -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.covered_characteristic_damped_measure_balance
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B C : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hC : 0 ≤ C)
    {β : Velocity × Velocity → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport β, hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      WeakTime.phaseSlice (WeakTime.timeWeightedDensity a A C
        (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit))) t =
      WeakTime.phaseSlice (WeakTime.timeWeightedDensity a A C
        (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit))) s+
      WeakTime.phaseIncrement
        (WeakTime.timeWeightedSource a A C (WeakTime.weightedPhaseSource
          (E.toHotLimitExtraction.characteristicGainMeasure ha hK hα hγ A R) β)+
        positiveDensityMeasure volume (WeakTime.dampedResidual a A C
          (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit))
          (WeakTime.phaseWeight β (E.toHotLimitExtraction.characteristicLossDensity a A R)))) s t := by
  obtain ⟨R,hR,hcover,hweak⟩ := E.covered_characteristic_weak_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂ ha haA hAB hB hβc
  refine ⟨R,hR,hcover,?_⟩
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
  apply WeakTime.ae_localized_damped_measure_balance haA hC (cylinderPullback_integrable hi)
    hLi (ae_of_all _ hn) _ hβ hβc hβn
  · apply ae_of_all
    intro u hu
    by_cases hz : β u.2 = 0
    · simp only [hz,zero_mul,mul_zero,le_refl]
    rw [E.toHotLimitExtraction.characteristicLossDensity_factor]
    have hb := hfrequency u hu (subset_tsupport β hz)
    have hp : 0 ≤ β u.2*cylinderPullback a A R E.hotLimit u := mul_nonneg (hβn _) (hn u)
    nlinarith only [mul_le_mul_of_nonneg_left hb hp]
  · intro φ hφ hc hφn hφβ θ hθ hθc hθs
    have hb := hweak φ hφ hc hφn hφβ θ hθ hθc hθs
    rw [E.toHotLimitExtraction.characteristicLossMeasure_eq ha haA.le hK hα hγ hq₂,
      positiveDensityMeasure_integral hLi.aemeasurable
        (ae_of_all _ (E.toHotLimitExtraction.characteristicLossDensity_nonneg a A R))] at hb
    exact hb

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

/-! # A globally measurable extension of the actual slab collision frequency -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicSlabFrequency_measurable (E : HotLimitExtraction S)
    {a : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) :
    Measurable (E.characteristicSlabFrequency a) := by
  have hp : Measurable (fun z : HotKineticPhase => ((max a z.1.1,z.1.2),z.2)) := by fun_prop
  have hm := (GeometricBackground.clamped_frequency_measurable
    (zero_lt_one.trans_le E.phase_mem.1) hK hα hγ η E.fraction).comp
    (hp.comp hotCharacteristicEquiv.measurable)
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext u
  dsimp [Function.comp_def,HotLimitExtraction.characteristicSlabFrequency]
  rw [max_eq_right (ha.le.trans (le_max_left a _))]

theorem HotLimitExtraction.characteristicSlabFrequency_eq (E : HotLimitExtraction S)
    {a : ℝ} {u : CharacteristicPhase} (hu : a ≤ u.1) :
    E.characteristicSlabFrequency a u = E.characteristicFrequency u := by
  unfold HotLimitExtraction.characteristicSlabFrequency HotLimitExtraction.characteristicFrequency
  have ht : (hotCharacteristicEquiv u).1.1 = u.1 := rfl
  rw [ht,max_eq_right hu]

theorem HotLimitExtraction.characteristicLossDensity_slab_factor (E : HotLimitExtraction S)
    (a A R : ℝ) (u : CharacteristicPhase) :
    E.characteristicLossDensity a A R u =
      cylinderPullback a A R E.hotLimit u*E.characteristicSlabFrequency a u := by
  by_cases hu : hotCharacteristicEquiv u ∈ coldCylinderSet a A R
  · rw [E.characteristicLossDensity_factor,
      E.characteristicSlabFrequency_eq (show a ≤ u.1 from hu.1.1.1)]
  · simp only [HotLimitExtraction.characteristicLossDensity,cylinderPullback,Function.comp_def,
      indicator_of_notMem hu,zero_mul]

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Retaining full support coverage in the combined positive source balance -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.covered_characteristic_combined_source_balance
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B C : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hC : 0 ≤ C)
    {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport β, hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t →
      WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t =
      ENNReal.ofReal (Real.exp (C*(s-t))) •
        WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s+
      WeakTime.dampedSourceIncrement a A C s t
        (E.toHotLimitExtraction.retainedSource ha hK hα hγ A R C β) := by
  obtain ⟨R,hR,hcover,hbalance⟩ := E.covered_characteristic_damped_measure_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hfrequency
  have hFi := (E.toHotLimitExtraction.physical_weak_cylinder S hs₀ ha.le
    ((ENNReal.ofReal_le_ofReal hAB.le).trans_lt hB) R).2.1
  have hF := (WeakTime.phaseWeight_integrable hβ.continuous hβc
    (cylinderPullback_integrable hFi)).aemeasurable
  have hL := (WeakTime.phaseWeight_integrable hβ.continuous hβc
    (E.toHotLimitExtraction.characteristicLossDensity_integrable (R := R)
      ha haA.le hK hα hγ hq₂)).aemeasurable
  refine ⟨R,hR,hcover,?_⟩
  filter_upwards [hbalance] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst
  have h := WeakTime.undamp_combined_source_balance _ hsa hta hF hL (ht hsa hta hst)
  rw [E.toHotLimitExtraction.characteristicGain_eq_kernel ha hK hα hγ] at h
  exact h

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual gain and self-retention source is a positive collision kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.retainedSource_eq_kernel (E : HotLimitExtraction S)
    {a A R C : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    {β : WeakTime.Phase → ℝ} (hβ : Measurable β) :
    E.retainedSource ha hK hα hγ A R C β =
      E.retainedKernel ha hK hα hγ C β ∘ₘ
        positiveDensityMeasure volume (cylinderPullback a A R E.hotLimit) := by
  have hF : Measurable (cylinderPullback a A R E.hotLimit) :=
    (E.hotLimit_measurable.indicator (coldCylinderSet_measurable a A R)).comp
      hotCharacteristicEquiv.measurable
  have hn (z : CharacteristicPhase) : 0 ≤ cylinderPullback a A R E.hotLimit z :=
    indicator_nonneg (fun x _ => E.hotLimit_nonneg x) _
  rw [HotLimitExtraction.retainedKernel,positiveSourceKernel_comp_density _ _
    (b := fun z => β z.2) (r := fun z => C-E.characteristicSlabFrequency a z) hF hn
    (hβ.comp measurable_snd)
    (measurable_const.sub (E.characteristicSlabFrequency_measurable ha hK hα.le hγ.le))]
  unfold HotLimitExtraction.retainedSource WeakTime.weightedPhaseSource
  congr 1
  congr 1
  funext z
  rw [WeakTime.phaseWeight,WeakTime.phaseWeight,E.characteristicLossDensity_slab_factor]
  ring

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # The actual retained source equals the active normal-angle beam source -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.characteristicSlabFrequency_eq_beam
    (E : HotLimitExtraction S) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (z : CharacteristicPhase)
    (ht : a ≤ z.1)
    (hactive : GeometricBackground.active E.phase η E.fraction
      (transverse (z.2.1+z.1 • z.2.2))) :
    E.characteristicSlabFrequency a z = (K/(4*r))*characteristicBeamFrequency
      (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
        hα.le hγ.le η r) z := by
  change GeometricBackground.frequency E.phase η E.fraction K α γ
    (max a z.1) (spaceEquiv (z.2.1+z.1 • z.2.2)) z.2.2 = _
  rw [max_eq_right ht,spaceEquiv_apply]
  exact GeometricBackground.frequency_eq_beamFrequency (zero_lt_one.trans_le E.phase_mem.1)
    hK hα.le hγ.le hr (ha.le.trans ht) η E.fraction _ _ hactive

theorem HotLimitExtraction.retainedKernel_eq_normal_beam
    (E : HotLimitExtraction S) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (C : ℝ) (z : CharacteristicPhase)
    (ht : a ≤ z.1)
    (hactive : GeometricBackground.active E.phase η E.fraction
      (transverse (z.2.1+z.1 • z.2.2))) :
    E.retainedKernel ha hK hα hγ C (fun _ => 1) z =
      beamNormalRetainedKernel
        (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
          hα.le hγ.le η r) (K/(4*r)) C z := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [HotLimitExtraction.retainedKernel,positiveSourceKernel_one_lintegral _
    (r := fun u => C-E.characteristicSlabFrequency a u)
    (measurable_const.sub (E.characteristicSlabFrequency_measurable ha hK hα.le hγ.le)) z hf,
    beamNormalRetainedKernel_lintegral _ _ _ z hf,
    E.characteristicGainKernel_eq_normal_beam ha hr hK hα hγ z ht hactive,
    lintegral_smul_measure,smul_eq_mul,
    E.characteristicSlabFrequency_eq_beam ha hr hK hα hγ z ht hactive]

theorem HotLimitExtraction.retainedKernel_eq_normal_beam_ae
    (E : HotLimitExtraction S) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (C : ℝ) :
    ∀ᵐ z : CharacteristicPhase ∂volume, a ≤ z.1 →
      0 < ‖transverse (z.2.1+z.1 • z.2.2)‖ →
      Real.exp η*E.fraction < ‖transverse (z.2.1+z.1 • z.2.2)‖ →
      E.retainedKernel ha hK hα hγ C (fun _ => 1) z =
        beamNormalRetainedKernel
          (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
            hα.le hγ.le η r) (K/(4*r)) C z := by
  filter_upwards [GeometricBackground.active_ae_characteristic
    (zero_lt_one.trans_le E.phase_mem.1) hη E.fraction] with z hz ht hp hc
  exact E.retainedKernel_eq_normal_beam ha hr hK hα hγ C z ht (hz hp hc)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Localized hot occupation supplies a positive retained collision source -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.localizedOccupation_le (E : HotLimitExtraction S)
    (a A R : ℝ) {β : WeakTime.Phase → ℝ} (hβ : ∀ p, β p ≤ 1) :
    positiveDensityMeasure volume (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) ≤
      positiveDensityMeasure volume (cylinderPullback a A R E.hotLimit) := by
  apply withDensity_mono
  apply ae_of_all
  intro z
  apply ENNReal.ofReal_le_ofReal
  have hn : 0 ≤ cylinderPullback a A R E.hotLimit z :=
    indicator_nonneg (fun x _ => E.hotLimit_nonneg x) _
  exact (mul_le_mul_of_nonneg_right (hβ z.2) hn).trans_eq (one_mul _)

theorem HotLimitExtraction.retainedSource_dominates_localized (E : HotLimitExtraction S)
    {a A R C : ℝ} (ha : 0 < a) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    {β : WeakTime.Phase → ℝ} (hβ : Measurable β) (hβ₁ : ∀ p, β p ≤ 1) :
    E.retainedKernel ha hK hα hγ C β ∘ₘ
      positiveDensityMeasure volume (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) ≤
        E.retainedSource ha hK hα hγ A R C β := by
  rw [E.retainedSource_eq_kernel ha hK hα hγ hβ]
  exact PositiveMeasureHistories.comp_mono_measure _ (E.localizedOccupation_le a A R hβ₁)

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

/-! # Local normal-angle beam histories lie below the actual hot source -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight
open BoltzmannNonuniqueness.ReferenceGeometry

namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotLimitExtraction.localizedNormalBeam_le_retained_ae
    (E : HotLimitExtraction S) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hη : 0 < η) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (C : ℝ)
    {β : WeakTime.Phase → ℝ} (hβ : Measurable β)
    {B : Set CharacteristicPhase} (hB : MeasurableSet B)
    (hcore : ∀ z ∈ B, β z.2 = 1) :
    ∀ᵐ z ∂volume, localizedNormalBeamKernel
      (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
        hα.le hγ.le η r) (K/(4*r)) C a η E.fraction hB z ≤
      E.retainedKernel ha hK hα hγ C β z := by
  classical
  have hle := positiveSourceKernel_restrict_le (E.characteristicGainKernel ha hK hα hγ)
    (b := fun z => β z.2) (r := fun z => C-E.characteristicSlabFrequency a z)
    (hβ.comp measurable_snd)
    (measurable_const.sub (E.characteristicSlabFrequency_measurable ha hK hα.le hγ.le))
    hB hcore
  filter_upwards [E.retainedKernel_eq_normal_beam_ae ha hr hη hK hα hγ C] with z hz
  unfold localizedNormalBeamKernel
  rw [Kernel.piecewise_apply]
  by_cases hd : z ∈ coldCharacteristicDomain a η E.fraction
  · rw [ite_eq_left hd,Kernel.restrict_apply,
      ← hz hd.1 hd.2.1 hd.2.2,← Kernel.restrict_apply]
    exact hle z
  · rw [ite_eq_right hd]
    exact bot_le

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Retaining full support coverage in the finite positive endpoint histories -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.covered_comparison_endpoint_histories
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B C : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hC : 0 ≤ C)
    {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C)
    (Jc : Kernel CharacteristicPhase CharacteristicPhase)
    (hJc : ∀ᵐ z ∂volume, Jc z ≤ E.toHotLimitExtraction.retainedKernel ha hK hα hγ C β z) :
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport β, hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t → ∀ n : ℕ,
      WeakTime.phaseEndpointKernel C t ∘ₘ
        (∑ j ∈ Finset.range n,
          ((((Jc.restrict (measurable_fst measurableSet_Ioc :
            MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ WeakTime.residenceKernel C t)^j)) ∘ₘ
            WeakTime.phaseSeed s (WeakTime.phaseSlice
              (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s)) ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t := by
  obtain ⟨R,hR,hcover,hbalance⟩ := E.covered_characteristic_combined_source_balance hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hfrequency
  let Fh := WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)
  let J := E.toHotLimitExtraction.retainedSource ha hK hα hγ A R C β
  have hF : Measurable Fh := (hβ.continuous.measurable.comp measurable_snd).mul
    ((E.toHotLimitExtraction.hotLimit_measurable.indicator
      (coldCylinderSet_measurable a A R)).comp hotCharacteristicEquiv.measurable)
  let _ : SFinite J := by
    dsimp [J]
    rw [E.toHotLimitExtraction.retainedSource_eq_kernel ha hK hα hγ hβ.continuous.measurable]
    unfold positiveDensityMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hcomp : Jc ∘ₘ positiveDensityMeasure volume Fh ≤
      E.toHotLimitExtraction.retainedKernel ha hK hα hγ C β ∘ₘ
        positiveDensityMeasure volume Fh := by
    apply KernelHistoryOrder.measure_comp_mono_ae _ le_rfl
    exact (withDensity_absolutelyContinuous volume _).ae_le hJc
  have hsource : Jc ∘ₘ positiveDensityMeasure volume Fh ≤ J := hcomp.trans
    (E.toHotLimitExtraction.retainedSource_dominates_localized ha hK hα hγ
      hβ.continuous.measurable hβ₁)
  refine ⟨R,hR,hcover,?_⟩
  filter_upwards [hbalance] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hst n
  let _ : SFinite (WeakTime.phaseSlice Fh s) := by
    unfold WeakTime.phaseSlice positiveDensityMeasure
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hocc : (positiveDensityMeasure volume Fh).restrict (Prod.fst ⁻¹' Ioc s t) =
      WeakTime.residenceKernel C t ∘ₘ
        (WeakTime.phaseSeed s (WeakTime.phaseSlice Fh s)+J.restrict (Prod.fst ⁻¹' Ioc s t)) := by
    apply WeakTime.occupation_eq_residence hF _ J hsa.1 hta.2
    filter_upwards [hs] with r hr
    intro hsr
    exact hr hsa ⟨hsa.1.trans hsr.1,hsr.2.trans_lt hta.2⟩ hsr.1.le
  exact WeakTime.endpoint_finite_histories
    Jc (WeakTime.residenceKernel C t)
    (positiveDensityMeasure volume Fh) J (WeakTime.phaseSlice Fh s) (WeakTime.phaseSlice Fh t)
    hsa.1 hta.2 hocc
    hsource (ht hsa hta hst) n

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # Retaining full support coverage in the finite positive endpoint histories -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.covered_normal_endpoint_histories
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a A B C : ℝ} (ha : 0 < a) (haA : a < A) (hAB : A < B)
    (hB : ENNReal.ofReal B < E.horizon) (hC : 0 ≤ C)
    {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a A → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C)
    {r : ℝ} (hr : 0 < r) {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω)
    (hcore : ∀ z ∈ Ω, β z.2 = 1) :
    let Jc := localizedNormalBeamKernel
      (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
        hα.le hγ.le η r) (K/(4*r)) C a η E.fraction hΩ;
    ∃ R : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport β, hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a A → t ∈ Ioo a A → s ≤ t → ∀ n : ℕ,
      WeakTime.phaseEndpointKernel C t ∘ₘ
        (∑ j ∈ Finset.range n,
          ((((Jc.restrict (measurable_fst measurableSet_Ioc :
            MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ WeakTime.residenceKernel C t)^j)) ∘ₘ
            WeakTime.phaseSeed s (WeakTime.phaseSlice
              (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) s)) ≤
        WeakTime.phaseSlice (WeakTime.phaseWeight β (cylinderPullback a A R E.hotLimit)) t := by
  exact E.covered_comparison_endpoint_histories hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haA hAB hB hC hβ hβc hβn hβ₁ hfrequency _
    (E.toHotLimitExtraction.localizedNormalBeam_le_retained_ae ha hr hη hK hα hγ C
      hβ.continuous.measurable hΩ hcore)

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

section

/-! # A positive finite localized history produces positive actual hot mass -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.EuclideanFlight BoltzmannNonuniqueness.ReferenceGeometry
namespace BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence
variable {s₀ η K α γ d₀ q : ℝ} {F : ShrinkingCapFamily s₀ η K α γ d₀ q}
  {S : AttainedCapSequence F}

theorem HotPairExtraction.positive_history_transfer_q80_oai
    (hDP : Published.DunfordPettis1940HotPairWindows)
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (E : HotPairExtraction S)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {a U V C r : ℝ} (ha : 0 < a) (haU : a < U) (hUV : U < V)
    (hV : ENNReal.ofReal V < E.horizon) (hC : 0 ≤ C) (hr : 0 < r)
    {β : WeakTime.Phase → ℝ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) (hβn : ∀ p, 0 ≤ β p) (hβ₁ : ∀ p, β p ≤ 1)
    (hfrequency : ∀ u : CharacteristicPhase, u.1 ∈ Ioo a U → u.2 ∈ tsupport β →
      E.toHotLimitExtraction.characteristicFrequency u ≤ C)
    {Ω : Set CharacteristicPhase} (hΩ : MeasurableSet Ω) (hcore : ∀ z ∈ Ω, β z.2 = 1)
    (A B : ℝ → Set WeakTime.Phase) (hA : ∀ t, MeasurableSet (A t))
    (hB : ∀ s, MeasurableSet (B s))
    (hstart : ∀ s ∈ Ioo a U, ∀ p ∈ B s, β p = 1)
    (N : ℕ) (P : ℝ → ℝ → Prop)
    (horder : ∀ s ∈ Ioo a U, ∀ t ∈ Ioo a U, P s t → s ≤ t)
    (hpoint : ∀ s ∈ Ioo a U, ∀ t ∈ Ioo a U, P s t → ∀ p ∈ B s,
      0 < (WeakTime.phaseEndpointKernel C t ∘ₖ
        ((((localizedNormalBeamKernel
          (GeometricBackground.beamCoefficients (zero_lt_one.trans_le E.phase_mem.1)
            hα.le hγ.le η r) (K/(4*r)) C a η E.fraction hΩ).restrict
          (measurable_fst measurableSet_Ioc : MeasurableSet (Prod.fst ⁻¹' Ioc s t))) ∘ₖ
            WeakTime.residenceKernel C t)^N)) (s,p) (A t)) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, s ∈ Ioo a U → t ∈ Ioo a U → P s t →
      0 < hotPhaseSlice E.hotLimit s (B s) → 0 < hotPhaseSlice E.hotLimit t (A t) := by
  obtain ⟨R,_hR,hcover,hist⟩ := E.covered_normal_endpoint_histories hDP hcarleman hGLPS
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall hq₁ hq₂
    ha haU hUV hV hC hβ hβc hβn hβ₁ hfrequency hr hΩ hcore
  filter_upwards [hist] with s hs
  filter_upwards [hs] with t ht
  intro hsa hta hp hm
  apply covered_hot_positive_history E.toHotLimitExtraction.hotLimit_nonneg hβ₁
    a U R s t (hA t) (hB s) (hstart s hsa) (hcover s ⟨hsa.1.le,hsa.2.le⟩)
    _ C N hm (ht hsa hta (horder s hsa t hta hp) (N+1))
  exact hpoint s hsa t hta hp

end BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.positive_history_transfer_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotPairExtraction.positive_history_transfer_q80_oai
