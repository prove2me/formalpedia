-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.JetCopyDatum.origin_scale_five_tendsto_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T20:57:59.853715+00:00
-- url     : https://prove2.me/submissions/f1a76030-e996-459c-943e-4e7cf51bca36

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

section
-- module Solutions.OAIQ080_BZ.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CompactParameterConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Compact uniform convergence of a jointly continuous parameter family -/

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.GainPullback

theorem uniform_on_compact_of_joint_continuous
    {P Q R : Type*} [TopologicalSpace P] [TopologicalSpace Q] [T2Space Q]
    [UniformSpace R] {F : P × Q → R} (hF : Continuous F)
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀))
    {K : Set Q} (hK : IsCompact K) :
    TendstoUniformlyOn (fun n q => F (p n,q)) (fun q => F (p₀,q)) atTop K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G : C(P × K,R) := ⟨fun x => F (x.1,x.2),
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))⟩
  have ht := (G.curry.continuous.tendsto p₀).comp hp
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp ht
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  exact hu

theorem uniform_on_compact_of_joint_restriction
    {P Q R : Type*} [TopologicalSpace P] [TopologicalSpace Q] [T2Space Q]
    [UniformSpace R] {F : P × Q → R} {K : Set Q} (hK : IsCompact K)
    (hF : Continuous (fun p : P × K => F (p.1,p.2.val)))
    {p : ℕ → P} {p₀ : P} (hp : Tendsto p atTop (𝓝 p₀)) :
    TendstoUniformlyOn (fun n q => F (p n,q)) (fun q => F (p₀,q)) atTop K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hu := uniform_on_compact_of_joint_continuous hF hp (K := Set.univ) isCompact_univ
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (tendstoUniformlyOn_univ.mp hu)

end BoltzmannNonuniqueness.GainPullback


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

theorem foot_characteristic {σ α γ s t z : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) :
    foot σ α γ s t (characteristic σ α γ s t z) = z := by
  apply (characteristic_strictMono hα hγ hs ht).injective
  exact characteristic_foot hα

end BoltzmannNonuniqueness.AxialFlow

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityWeight
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.TransverseAverage.circleArea_isFiniteMeasure _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AnalyticTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Analyticity of the existing inverse from the analytic inverse theorem -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.AnalyticInverse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem localInverse_analytic {f : E → F} {x : E} (A : E ≃L[ℝ] F)
    (ha : AnalyticAt ℝ f x) (hf : HasStrictFDerivAt f A.toContinuousLinearMap x) :
    AnalyticAt ℝ (hf.localInverse f A x) (f x) := by
  obtain ⟨p,hp⟩ := ha
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℝ E F).symm A.toContinuousLinearMap := by
    apply (continuousMultilinearCurryFin1 ℝ E F).injective
    rw [(continuousMultilinearCurryFin1 ℝ E F).apply_symm_apply]
    exact hp.hasFDerivAt.unique hf.hasFDerivAt
  exact ((hf.toOpenPartialHomeomorph f).hasFPowerSeriesAt_symm
    hf.mem_toOpenPartialHomeomorph_source hp hcoeff).analyticAt

theorem analytic_of_eventually_left_inverse {f : E → F} {g : F → E} {x : E}
    (A : E ≃L[ℝ] F) (ha : AnalyticAt ℝ f x)
    (hf : HasStrictFDerivAt f A.toContinuousLinearMap x)
    (hg : ∀ᶠ y in 𝓝 x, g (f y) = y) : AnalyticAt ℝ g (f x) := by
  exact (localInverse_analytic A ha hf).congr (Filter.EventuallyEq.symm (hf.localInverse_unique hg))

end BoltzmannNonuniqueness.AnalyticInverse

end

end

section

/-! # Analyticity of the determinant of a finite-dimensional operator -/

noncomputable section

namespace BoltzmannNonuniqueness

theorem determinant_analyticAt {X E : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {A : X → E →L[ℝ] E} {x : X} (hA : AnalyticAt ℝ A x) :
    AnalyticAt ℝ (fun y => (A y).toLinearMap.det) x := by
  classical
  let b := Module.finBasis ℝ E
  have hc (i j : Fin (Module.finrank ℝ E)) :
      AnalyticAt ℝ (fun y => b.coord i (A y (b j))) x :=
    ((b.coord i).toContinuousLinearMap.analyticAt _).comp
      (((ContinuousLinearMap.apply ℝ E (b j)).analyticAt _).comp hA)
  have he : (fun y => (A y).toLinearMap.det) =
      (fun y => (LinearMap.toMatrix b b (A y).toLinearMap).det) := by
    funext y
    exact (LinearMap.det_toMatrix b (A y).toLinearMap).symm
  rw [he]
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro p _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  simpa only [LinearMap.toMatrix_apply,Module.Basis.coord_apply] using! hc (p i) i

end BoltzmannNonuniqueness

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

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AxialJointAnalytic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Analyticity of the explicit cold profile and characteristic maps -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.AxialFlow BoltzmannNonuniqueness.AxialDerivative

namespace BoltzmannNonuniqueness.AxialAnalytic

theorem tanh_analytic (x : ℝ) : AnalyticAt ℝ Real.tanh x := by
  have he : Real.tanh = Real.sinh / Real.cosh :=
    funext (fun y => Real.tanh_eq_sinh_div_cosh y)
  rw [he]
  exact Real.analyticAt_sinh.div Real.analyticAt_cosh (Real.cosh_pos x).ne'

end BoltzmannNonuniqueness.AxialAnalytic

end

end

section

/-! # Joint analyticity of the cold flow in scale, time, and position -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.AxialFlow BoltzmannNonuniqueness.AxialDerivative

namespace BoltzmannNonuniqueness.AxialAnalytic

theorem jointProfile_analytic (σ α γ : ℝ) (p : FlowParameters) (hs : p.1.1 ≠ 0) :
    AnalyticAt ℝ (fun q : FlowParameters => profile σ α γ q.1.1 q.2) p := by
  have hscale : AnalyticAt ℝ (fun q : FlowParameters => q.1.1) p :=
    analyticAt_fst.comp analyticAt_fst
  have harg : AnalyticAt ℝ (fun q : FlowParameters => γ*q.2/q.1.1) p :=
    (analyticAt_const.mul analyticAt_snd).div hscale hs
  have htan := (tanh_analytic (γ*p.2/p.1.1)).comp
    (f := fun q : FlowParameters => γ*q.2/q.1.1) harg
  exact analyticAt_const.add (analyticAt_const.mul htan)

theorem jointCharacteristic_analytic (σ α γ : ℝ) (p : FlowParameters)
    (hs : p.1.1 ≠ 0) : AnalyticAt ℝ (jointCharacteristic σ α γ) p := by
  have ht : AnalyticAt ℝ (fun q : FlowParameters => q.1.2) p :=
    analyticAt_snd.comp analyticAt_fst
  exact analyticAt_fst.prod
    (analyticAt_snd.add (ht.mul (jointProfile_analytic σ α γ p hs)))

theorem jointCharacteristic_derivative_fst (σ α γ : ℝ) (p : FlowParameters)
    (hs : p.1.1 ≠ 0) (v : FlowParameters) :
    (fderiv ℝ (jointCharacteristic σ α γ) p v).1 = v.1 := by
  have hd := (jointCharacteristic_analytic σ α γ p hs).hasStrictFDerivAt.hasFDerivAt
  have he := hd.fst.unique (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  exact congrArg (fun L : FlowParameters →L[ℝ] ℝ × ℝ => L v) he

theorem jointCharacteristic_derivative_vertical (σ α γ : ℝ) (p : FlowParameters)
    (hs : p.1.1 ≠ 0) :
    (fderiv ℝ (jointCharacteristic σ α γ) p (0,1)).2 =
      1+p.1.2*A α γ p.1.1 p.2 := by
  have hd := (jointCharacteristic_analytic σ α γ p hs).hasStrictFDerivAt.hasFDerivAt
  have hline : HasDerivAt (fun z : ℝ => (p.1,z)) (0,1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have h := hd.snd.comp_hasDerivAt p.2 hline
  exact h.unique (characteristic_derivative σ α γ p.1.1 p.1.2 p.2)

theorem jointFoot_analytic {σ α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (p : FlowParameters) (hs : 0 < p.1.1) (ht : 0 < p.1.2) :
    AnalyticAt ℝ (jointFoot σ α γ) p := by
  let a := jointFoot σ α γ p
  have ha : a.1 = p.1 := rfl
  have hf := jointCharacteristic_analytic σ α γ a hs.ne'
  have hd : (fderiv ℝ (jointCharacteristic σ α γ) a (0,1)).2 ≠ 0 := by
    rw [jointCharacteristic_derivative_vertical σ α γ a hs.ne']
    have hA := A_nonneg hα hγ hs.le a.2
    change 1+p.1.2*A α γ p.1.1 a.2 ≠ 0
    positivity
  let e := triangularEquiv (fderiv ℝ (jointCharacteristic σ α γ) a)
    (jointCharacteristic_derivative_fst σ α γ a hs.ne') hd
  have hleft : ∀ᶠ q in 𝓝 a, jointFoot σ α γ (jointCharacteristic σ α γ q) = q := by
    have hS : ∀ᶠ q : FlowParameters in 𝓝 a, 0 < q.1.1 :=
      (show ContinuousAt (fun q : FlowParameters => q.1.1) a by fun_prop).eventually
        (lt_mem_nhds hs)
    have hT : ∀ᶠ q : FlowParameters in 𝓝 a, 0 < q.1.2 :=
      (show ContinuousAt (fun q : FlowParameters => q.1.2) a by fun_prop).eventually
        (lt_mem_nhds ht)
    filter_upwards [hS,hT] with q hqS hqT
    refine Prod.ext rfl ?_
    exact foot_characteristic hα hγ hqS hqT.le
  have hi := AnalyticInverse.analytic_of_eventually_left_inverse e hf
    (by simpa only [e,triangularEquiv_coe] using hf.hasStrictFDerivAt) hleft
  have he : jointCharacteristic σ α γ a = p := by
    refine Prod.ext ha ?_
    exact characteristic_foot hα
  rwa [he] at hi

theorem jointVelocity_analytic {σ α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (p : FlowParameters) (hs : 0 < p.1.1) (ht : 0 < p.1.2) :
    AnalyticAt ℝ (fun q : FlowParameters => velocity σ α γ q.1.1 q.1.2 q.2) p := by
  have h := (jointProfile_analytic σ α γ (jointFoot σ α γ p) hs.ne').comp
    (jointFoot_analytic hα hγ p hs ht)
  change AnalyticAt ℝ (fun q : FlowParameters =>
    profile σ α γ q.1.1 (foot σ α γ q.1.1 q.1.2 q.2)) p at h
  have he : (fun q : FlowParameters => profile σ α γ q.1.1
      (foot σ α γ q.1.1 q.1.2 q.2)) =
      (fun q : FlowParameters => velocity σ α γ q.1.1 q.1.2 q.2) :=
    funext (fun _ => (velocity_spec hα).symm)
  rwa [he] at h

end BoltzmannNonuniqueness.AxialAnalytic

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FiveGainRank
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The explicit nondegenerate five-collision configuration

These algebraic witnesses allow arbitrary axial cold velocities. The first
three increments are independent; after the fourth increment the final two
collision normals are not parallel. Derivative and analytic-null-set arguments
are separate from these algebraic statements.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainWitness

theorem transverseSquare_pos (R : ℝ) : 0 < transverseSquare R := by
  unfold transverseSquare
  nlinarith [sq_nonneg R]

theorem smallFactor_pos (R b : ℝ) : 0 < smallFactor R b := by
  unfold smallFactor
  have := transverseSquare_pos R
  positivity

theorem transverse_factor_pos (R b : ℝ) : 0 < 1-smallFactor R b*b := by
  have hD : 0 < 2*(1+b^2+transverseSquare R) := by
    have := transverseSquare_pos R
    positivity
  have hB : b < 2*(1+b^2+transverseSquare R) := by
    have := transverseSquare_pos R
    nlinarith [sq_nonneg (b-1)]
  have h := (div_lt_one hD).mpr hB
  unfold smallFactor
  rw [mul_comm,← div_eq_mul_inv]
  linarith

theorem first_three_det (R b : ℝ) :
    det (Matrix.of ![first,second R,third R b]) = -smallFactor R b*transverseSquare R := by
  rw [det_fin_three]
  simp [first,second,third,Matrix.of_apply,Matrix.cons_val]

theorem first_three_det_ne_zero (R b : ℝ) : det (Matrix.of ![first,second R,third R b]) ≠ 0 := by
  rw [first_three_det]
  exact mul_ne_zero (neg_ne_zero.mpr (smallFactor_pos R b).ne') (transverseSquare_pos R).ne'

theorem afterThird_transverse_pos (R b : ℝ) :
    0 < afterThirdX R b ^ 2+afterThirdY R b ^ 2 := by
  have h : 0 < (1-smallFactor R b*b)^2 * transverseSquare R :=
    mul_pos (sq_pos_of_pos (transverse_factor_pos R b)) (transverseSquare_pos R)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold afterThirdX afterThirdY transverseSquare
  ring

/-- Every perpendicular increment is produced by a redundant angular parameter. -/
theorem cross_represents {n k : V} (hn : n ≠ 0) (hk : n ⬝ᵥ k = 0) :
    n ⨯₃ ((-(n ⬝ᵥ n)⁻¹) • (n ⨯₃ k)) = k := by
  have hd : n ⬝ᵥ n ≠ 0 := fun h => hn (dotProduct_self_eq_zero.mp h)
  rw [map_smul,cross_cross_eq_smul_sub_smul',hk,zero_smul,zero_sub,smul_neg,
    ← neg_smul,neg_neg,smul_smul,inv_mul_cancel₀ hd,one_smul]

end BoltzmannNonuniqueness.FiveGainWitness

end

end

section

/-! # The actual recursive five-gain characteristic map -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.AxialFlow BoltzmannNonuniqueness.AxialAnalytic

namespace BoltzmannNonuniqueness.FiveGainMap

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cross_analytic {f g : E → V} {q : E}
    (hf : AnalyticAt ℝ f q) (hg : AnalyticAt ℝ g q) :
    AnalyticAt ℝ (fun y => f y ⨯₃ g y) q := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact ((analyticAt_pi_iff.mp hf 1).mul (analyticAt_pi_iff.mp hg 2)).sub
      ((analyticAt_pi_iff.mp hf 2).mul (analyticAt_pi_iff.mp hg 1))
  · exact ((analyticAt_pi_iff.mp hf 2).mul (analyticAt_pi_iff.mp hg 0)).sub
      ((analyticAt_pi_iff.mp hf 0).mul (analyticAt_pi_iff.mp hg 2))
  · exact ((analyticAt_pi_iff.mp hf 0).mul (analyticAt_pi_iff.mp hg 1)).sub
      ((analyticAt_pi_iff.mp hf 1).mul (analyticAt_pi_iff.mp hg 0))

theorem axis_analytic {f : E → ℝ} {q : E} (hf : AnalyticAt ℝ f q) :
    AnalyticAt ℝ (fun y => axis (f y)) q := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact analyticAt_const
  · exact analyticAt_const
  · exact hf

theorem step_analytic {σ α γ s : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s)
    {t : E → ℝ} {L : E → V} {z : E → State} {q : E}
    (ht : AnalyticAt ℝ t q) (hL : AnalyticAt ℝ L q) (hz : AnalyticAt ℝ z q)
    (htpos : 0 < t q) :
    AnalyticAt ℝ (fun y => step σ α γ s (t y) (L y) (z y)) q := by
  have hztime : AnalyticAt ℝ (fun y => (z y).1) q := analyticAt_fst.comp hz
  have hzx : AnalyticAt ℝ (fun y => (z y).2.1) q :=
    analyticAt_fst.comp (analyticAt_snd.comp hz)
  have hzv : AnalyticAt ℝ (fun y => (z y).2.2) q :=
    analyticAt_snd.comp (analyticAt_snd.comp hz)
  let x : E → V := fun y => (z y).2.1-((z y).1-t y) • (z y).2.2
  have hx : AnalyticAt ℝ x q := hzx.sub ((hztime.sub ht).smul hzv)
  have hp : AnalyticAt ℝ (fun y => ((s,t y),x y 2)) q :=
    (analyticAt_const.prod ht).prod (analyticAt_pi_iff.mp hx 2)
  have hv := (jointVelocity_analytic (σ := σ) hα hγ ((s,t q),x q 2) hs htpos).comp
    (f := fun y => ((s,t y),x y 2)) hp
  exact ht.prod (hx.prod (hzv.add (cross_analytic (hzv.sub (axis_analytic hv)) hL)))

end Analytic

theorem path_analytic {σ s : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : ∀ i, 0 < s i) (z : State) (q : Parameters) (ht : ∀ i, 0 < q.1 i) (k : ℕ) :
    AnalyticAt ℝ (fun y => path σ s α γ z y k) q := by
  induction k with
  | zero => exact analyticAt_const
  | succ k ih =>
    by_cases hk : k < 5
    · simp only [path,dite_eq_left hk]
      apply step_analytic hα hγ (hs ⟨k,hk⟩) _ _ ih (ht ⟨k,hk⟩)
      · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ)
          ⟨k,hk⟩).analyticAt _).comp analyticAt_fst
      · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => V)
          ⟨k,hk⟩).analyticAt _).comp analyticAt_snd
    · simpa only [path,dite_eq_right hk] using ih

theorem map_analytic {σ s : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : ∀ i, 0 < s i) (z : State) (q : Parameters) (ht : ∀ i, 0 < q.1 i) :
    AnalyticAt ℝ (map σ s α γ z) q := path_analytic hα hγ hs z q ht 5

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The thermal collision map, including the zero-width limit -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.AxialFlow BoltzmannNonuniqueness.AxialAnalytic

namespace BoltzmannNonuniqueness.FiveGainMap

theorem thermalCenter_zero (σ α γ s t : ℝ) (x w : V) :
    thermalCenter σ α γ s 0 t x w = axis (velocity σ α γ s t (x 2)) := by
  simp [thermalCenter,JetCoreMap.axialMap,axis]

theorem thermalStep_zero (σ α γ s t : ℝ) (L w : V) (z : State) :
    thermalStep σ α γ s 0 t L w z = step σ α γ s t L z := by
  simp only [thermalStep,thermalCenter_zero,step]

section Analytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem thermalCenter_analytic {σ α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    {s d t : E → ℝ} {x w : E → V} {q : E}
    (hs : AnalyticAt ℝ s q) (hd : AnalyticAt ℝ d q) (ht : AnalyticAt ℝ t q)
    (hx : AnalyticAt ℝ x q) (hw : AnalyticAt ℝ w q)
    (hspos : 0 < s q) (htpos : 0 < t q) :
    AnalyticAt ℝ (fun y => thermalCenter σ α γ (s y) (d y) (t y) (x y) (w y)) q := by
  have hw₂ := analyticAt_pi_iff.mp hw 2
  have hshift := (analyticAt_pi_iff.mp hx 2).sub (ht.mul (hd.mul hw₂))
  have hp := (hs.prod ht).prod hshift
  have hu := (jointVelocity_analytic (σ := σ) hα hγ
    ((s q,t q),x q 2-t q*(d q*w q 2)) hspos htpos).comp
    (f := fun y => ((s y,t y),x y 2-t y*(d y*w y 2))) hp
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact hd.mul (analyticAt_pi_iff.mp hw 0)
  · exact hd.mul (analyticAt_pi_iff.mp hw 1)
  · have h := (hd.mul hw₂).add hu
    change AnalyticAt ℝ (fun y => d y*w y 2+
      velocity σ α γ (s y) (t y) (x y 2-t y*d y*w y 2)) q
    change AnalyticAt ℝ (fun y => d y*w y 2+
      velocity σ α γ (s y) (t y) (x y 2-t y*(d y*w y 2))) q at h
    simpa only [mul_assoc] using h

theorem thermalStep_analytic {σ α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    {s d t : E → ℝ} {L w : E → V} {z : E → State} {q : E}
    (hs : AnalyticAt ℝ s q) (hd : AnalyticAt ℝ d q) (ht : AnalyticAt ℝ t q)
    (hL : AnalyticAt ℝ L q) (hw : AnalyticAt ℝ w q) (hz : AnalyticAt ℝ z q)
    (hspos : 0 < s q) (htpos : 0 < t q) :
    AnalyticAt ℝ (fun y => thermalStep σ α γ (s y) (d y) (t y) (L y) (w y) (z y)) q := by
  have hztime : AnalyticAt ℝ (fun y => (z y).1) q := analyticAt_fst.comp hz
  have hzx : AnalyticAt ℝ (fun y => (z y).2.1) q :=
    analyticAt_fst.comp (analyticAt_snd.comp hz)
  have hzv : AnalyticAt ℝ (fun y => (z y).2.2) q :=
    analyticAt_snd.comp (analyticAt_snd.comp hz)
  let x : E → V := fun y => (z y).2.1-((z y).1-t y) • (z y).2.2
  have hx : AnalyticAt ℝ x q := hzx.sub ((hztime.sub ht).smul hzv)
  have hc := thermalCenter_analytic (σ := σ) hα hγ hs hd ht hx hw hspos htpos
  exact ht.prod (hx.prod (hzv.add (cross_analytic (hzv.sub hc) hL)))

end Analytic

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Joint analytic dependence of the five thermal collision steps -/

noncomputable section

namespace BoltzmannNonuniqueness.FiveGainMap

theorem thermalPath_zero (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State)
    (q : Parameters) (w : Fin 5 → V) (k : ℕ) :
    thermalPath σ α γ (s,0,z) (q,w) k = path σ s α γ z q k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < 5
    · simpa only [thermalPath,path,dite_eq_left hk,Pi.zero_apply,thermalStep_zero] using
        congrArg (thermalStep (σ ⟨k,hk⟩) α γ (s ⟨k,hk⟩) 0
          (q.1 ⟨k,hk⟩) (q.2 ⟨k,hk⟩) (w ⟨k,hk⟩)) ih
    · simpa only [thermalPath,path,dite_eq_right hk] using ih

theorem thermalMap_zero (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State)
    (q : Parameters) (w : Fin 5 → V) :
    thermalMap σ α γ ((s,0,z),(q,w)) = map σ s α γ z q :=
  thermalPath_zero σ s α γ z q w 5

theorem thermalPath_analytic {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (p : ThermalInput)
    (hs : ∀ i, 0 < p.1.1 i) (ht : ∀ i, 0 < p.2.1.1 i) (k : ℕ) :
    AnalyticAt ℝ (fun y : ThermalInput => thermalPath σ α γ y.1 y.2 k) p := by
  have hsc : AnalyticAt ℝ (fun y : ThermalInput => y.1.1) p :=
    analyticAt_fst.comp analyticAt_fst
  have hd : AnalyticAt ℝ (fun y : ThermalInput => y.1.2.1) p :=
    analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
  have hz : AnalyticAt ℝ (fun y : ThermalInput => y.1.2.2) p :=
    analyticAt_snd.comp (analyticAt_snd.comp analyticAt_fst)
  have htime : AnalyticAt ℝ (fun y : ThermalInput => y.2.1.1) p :=
    analyticAt_fst.comp (analyticAt_fst.comp analyticAt_snd)
  have hL : AnalyticAt ℝ (fun y : ThermalInput => y.2.1.2) p :=
    analyticAt_snd.comp (analyticAt_fst.comp analyticAt_snd)
  have hw : AnalyticAt ℝ (fun y : ThermalInput => y.2.2) p :=
    analyticAt_snd.comp analyticAt_snd
  induction k with
  | zero => exact hz
  | succ k ih =>
    by_cases hk : k < 5
    · simp only [thermalPath,dite_eq_left hk]
      exact thermalStep_analytic hα hγ (analyticAt_pi_iff.mp hsc ⟨k,hk⟩)
        (analyticAt_pi_iff.mp hd ⟨k,hk⟩) (analyticAt_pi_iff.mp htime ⟨k,hk⟩)
        (analyticAt_pi_iff.mp hL ⟨k,hk⟩) (analyticAt_pi_iff.mp hw ⟨k,hk⟩) ih
        (hs ⟨k,hk⟩) (ht ⟨k,hk⟩)
    · simpa only [thermalPath,dite_eq_right hk] using ih

theorem thermalMap_analytic {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (p : ThermalInput)
    (hs : ∀ i, 0 < p.1.1 i) (ht : ∀ i, 0 < p.2.1.1 i) :
    AnalyticAt ℝ (thermalMap σ α γ) p := thermalPath_analytic hα hγ p hs ht 5

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Compact C1 convergence of the actual thermal five-gain maps -/

noncomputable section

open Filter Set
open scoped Topology

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] thermalMap

theorem thermalControl_hasFDerivAt {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (env : PositiveEnvironment)
    (q : ThermalControls) (ht : ∀ i, 0 < q.1.1 i) :
    HasFDerivAt (fun u => thermalMap σ α γ (env.val,u))
      (controlDerivative σ α γ (env.val,q)) q := by
  have hd := (thermalMap_analytic (σ := σ) hα hγ (env.val,q) env.property ht).hasStrictFDerivAt.hasFDerivAt
  have hi := (hasFDerivAt_const (𝕜 := ℝ) env.val q).prodMk (hasFDerivAt_id (𝕜 := ℝ) q)
  exact hd.comp q hi

theorem thermalMap_compact_tendsto {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) {env : ℕ → PositiveEnvironment}
    {env₀ : PositiveEnvironment} (henv : Tendsto env atTop (𝓝 env₀))
    {K : Set ThermalControls} (hK : IsCompact K)
    (hT : ∀ q ∈ K, ∀ i, 0 < q.1.1 i) :
    TendstoUniformlyOn (fun n q => thermalMap σ α γ ((env n).val,q))
      (fun q => thermalMap σ α γ (env₀.val,q)) atTop K := by
  let F : PositiveEnvironment × K → State :=
    fun p => thermalMap σ α γ (p.1.val,p.2.val)
  have hc : Continuous (fun p : PositiveEnvironment × K => (p.1.val,p.2.val)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hM : ContinuousOn (thermalMap σ α γ)
      (Set.range (fun r : PositiveEnvironment × K => (r.1.val,r.2.val))) := by
    rintro _ ⟨p,rfl⟩
    exact (thermalMap_analytic (σ := σ) hα hγ (p.1.val,p.2.val) p.1.property
      (hT p.2.val p.2.property)).continuousAt.continuousWithinAt
  have hF : Continuous F := hM.comp_continuous hc (fun p => Set.mem_range_self p)
  exact GainPullback.uniform_on_compact_of_joint_restriction
    (F := fun p : PositiveEnvironment × ThermalControls => thermalMap σ α γ (p.1.val,p.2))
    hK hF henv

theorem thermalDerivative_compact_tendsto {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) {env : ℕ → PositiveEnvironment}
    {env₀ : PositiveEnvironment} (henv : Tendsto env atTop (𝓝 env₀))
    {K : Set ThermalControls} (hK : IsCompact K)
    (hT : ∀ q ∈ K, ∀ i, 0 < q.1.1 i) :
    TendstoUniformlyOn (fun n q => controlDerivative σ α γ ((env n).val,q))
      (fun q => controlDerivative σ α γ (env₀.val,q)) atTop K := by
  let F : PositiveEnvironment × K → ThermalControls →L[ℝ] State :=
    fun p => controlDerivative σ α γ (p.1.val,p.2.val)
  have hc : Continuous (fun p : PositiveEnvironment × K => (p.1.val,p.2.val)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have hD : Continuous (fun p : PositiveEnvironment × K =>
      fderiv ℝ (thermalMap σ α γ) (p.1.val,p.2.val)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    exact (thermalMap_analytic (σ := σ) hα hγ (p.1.val,p.2.val) p.1.property
      (hT p.2.val p.2.property)).fderiv.continuousAt.comp (f := fun r : PositiveEnvironment × K => (r.1.val,r.2.val))
        hc.continuousAt
  have hF : Continuous F := hD.clm_comp_const (ContinuousLinearMap.inr ℝ _ _)
  exact GainPullback.uniform_on_compact_of_joint_restriction
    (F := fun p : PositiveEnvironment × ThermalControls => controlDerivative σ α γ (p.1.val,p.2))
    hK hF henv

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Exact reduction of the five-gain map at equal collision times -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.FiveGainMap

theorem step_same_time (σ α γ s τ : ℝ) (L x v : V) :
    step σ α γ s τ L (τ,x,v) =
      (τ,x,velocityStep (velocity σ α γ s τ (x 2)) L v) := by
  simp only [step,sub_self,zero_smul,sub_zero,velocityStep]

theorem path_equal_time (σ s : Fin 5 → ℝ) (α γ τ : ℝ) (z : State)
    (L : Fin 5 → V) {k : ℕ} (hk : 0 < k) (hk5 : k ≤ 5) :
    path σ s α γ z ((fun _ => τ),L) k =
      (τ,commonPosition τ z,
        velocityPath (equalTimeSpeeds σ s α γ τ z) L z.2.2 k) := by
  induction k with
  | zero => omega
  | succ k ih =>
    have hlt : k < 5 := by omega
    rw [path,velocityPath,dite_eq_left hlt,dite_eq_left hlt]
    cases k with
    | zero => rfl
    | succ k =>
      rw [ih (by omega) (by omega),step_same_time]
      rfl

theorem map_equal_time (σ s : Fin 5 → ℝ) (α γ τ : ℝ) (z : State)
    (L : Fin 5 → V) :
    map σ s α γ z ((fun _ => τ),L) =
      (τ,commonPosition τ z,
        velocityPath (equalTimeSpeeds σ s α γ τ z) L z.2.2 5) :=
  path_equal_time σ s α γ τ z L (by decide) (by decide)

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Position derivatives at the equal-time five-collision configuration -/

noncomputable section

open Matrix

namespace BoltzmannNonuniqueness.FiveGainWitness

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Dependence of the velocities contributes zero to the position derivative
when all formal free-flight durations vanish. -/
theorem endPosition_hasDerivAt (t₀ τ : ℝ) (x₀ v₀ : W)
    {t : ℝ → Fin 5 → ℝ} {v : ℝ → Fin 4 → W}
    {dt : Fin 5 → ℝ} {dv : Fin 4 → W}
    (ht : ∀ i, HasDerivAt (fun r => t r i) (dt i) 0)
    (hv : ∀ i, HasDerivAt (fun r => v r i) (dv i) 0)
    (heq : ∀ i, t 0 i = τ) :
    HasDerivAt (fun r => endPosition t₀ x₀ v₀ (t r) (v r))
      (positionDirection v₀ dt (v 0)) 0 := by
  have hs (i : Fin 4) : HasDerivAt
      (fun r => (t r i.castSucc-t r i.succ) • v r i)
      ((dt i.castSucc-dt i.succ) • v 0 i) 0 := by
    have h := ((ht i.castSucc).sub (ht i.succ)).smul (hv i)
    change HasDerivAt (fun r => (t r i.castSucc-t r i.succ) • v r i)
      ((t 0 i.castSucc-t 0 i.succ) • dv i +
        (dt i.castSucc-dt i.succ) • v 0 i) 0 at h
    simpa only [heq,sub_self,zero_smul,zero_add] using h
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hs i)
  have hfirst := ((hasDerivAt_const 0 t₀).sub (ht 0)).smul_const v₀
  have h := ((hasDerivAt_const 0 x₀).sub hfirst).sub hsum
  change HasDerivAt (fun r => endPosition t₀ x₀ v₀ (t r) (v r))
    (0-(0-dt 0) • v₀-∑ i, (dt i.castSucc-dt i.succ) • v 0 i) 0 at h
  simpa only [positionDirection,zero_sub,neg_smul,neg_neg] using h

end BoltzmannNonuniqueness.FiveGainWitness

end

end

section

/-! # Position formula and time derivatives for the actual collision path -/

noncomputable section

open Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

theorem path_succ_time (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State)
    (q : Parameters) (k : ℕ) (hk : k < 5) :
    (path σ s α γ z q (k+1)).1 = q.1 ⟨k,hk⟩ := by
  simp only [path,dite_eq_left hk,step]

theorem path_succ_position (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State)
    (q : Parameters) (k : ℕ) (hk : k < 5) :
    (path σ s α γ z q (k+1)).2.1 = (path σ s α γ z q k).2.1-
      ((path σ s α γ z q k).1-q.1 ⟨k,hk⟩) • (path σ s α γ z q k).2.2 := by
  simp only [path,dite_eq_left hk,step]

theorem map_position (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) :
    (map σ s α γ z q).2.1 = endPosition z.1 z.2.1 z.2.2 q.1
      (fun i : Fin 4 => (path σ s α γ z q (i.val+1)).2.2) := by
  unfold map endPosition
  rw [path_succ_position σ s α γ z q 4 (by decide),
    path_succ_position σ s α γ z q 3 (by decide),
    path_succ_position σ s α γ z q 2 (by decide),
    path_succ_position σ s α γ z q 1 (by decide),
    path_succ_position σ s α γ z q 0 (by decide),
    path_succ_time σ s α γ z q 3 (by decide),
    path_succ_time σ s α γ z q 2 (by decide),
    path_succ_time σ s α γ z q 1 (by decide),
    path_succ_time σ s α γ z q 0 (by decide)]
  rw [show path σ s α γ z q 0 = z from rfl]
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Fin.castSucc_zero,
    Fin.succ_zero_eq_one,Nat.zero_add,Finset.univ_eq_empty,Finset.sum_empty,add_zero,
    Nat.reduceAdd]
  abel

theorem map_position_hasDerivAt {σ s : Fin 5 → ℝ} {α γ τ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i) (hτ : 0 < τ)
    (z : State) {q : ℝ → Parameters} {dq : Parameters}
    (hq : HasDerivAt q dq 0) (ht : ∀ i, (q 0).1 i = τ) :
    HasDerivAt (fun r => (map σ s α γ z (q r)).2.1)
      (positionDirection z.2.2 dq.1
        (fun i : Fin 4 => (path σ s α γ z (q 0) (i.val+1)).2.2)) 0 := by
  have ha (i : Fin 4) := path_analytic (σ := σ) hα hγ hs z (q 0)
    (fun j => by rw [ht]; exact hτ) (i.val+1)
  have hv (i : Fin 4) := ((ha i).hasStrictFDerivAt.hasFDerivAt.snd.snd).comp_hasDerivAt 0 hq
  have ht' (i : Fin 5) := ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 5 => ℝ) i).hasFDerivAt).comp_hasDerivAt
    0 hq.fst
  have h := endPosition_hasDerivAt z.1 τ z.2.1 z.2.2 ht' hv ht
  change HasDerivAt (fun r => endPosition z.1 z.2.1 z.2.2 (q r).1
    (fun i : Fin 4 => (path σ s α γ z (q r) (i.val+1)).2.2))
    (positionDirection z.2.2 dq.1
      (fun i : Fin 4 => (path σ s α γ z (q 0) (i.val+1)).2.2)) 0 at h
  simpa only [map_position] using h

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Rotations about the cold velocity axis -/

noncomputable section

open Matrix
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainMap

theorem rotation_apply (c s : ℝ) (v : V) :
    rotation c s v = ![c*v 0-s*v 1,s*v 0+c*v 1,v 2] := rfl

@[simp] theorem rotation_axis (c s a : ℝ) : rotation c s (axis a) = axis a := by
  ext i
  fin_cases i <;> simp [rotation_apply,axis]

theorem rotation_cross {c s : ℝ} (hcs : c^2+s^2 = 1) (v w : V) :
    rotation c s (v ⨯₃ w) = rotation c s v ⨯₃ rotation c s w := by
  ext i
  fin_cases i
  · simp [rotation_apply,cross_apply]
    ring
  · simp [rotation_apply,cross_apply]
    ring
  · simp [rotation_apply,cross_apply]
    linear_combination -(v 0*w 1-v 1*w 0)*hcs

theorem rotation_inverse {c s : ℝ} (hcs : c^2+s^2 = 1) (v : V) :
    rotation c (-s) (rotation c s v) = v := by
  ext i
  fin_cases i
  · simp [rotation_apply]
    linear_combination v 0*hcs
  · simp [rotation_apply]
    linear_combination v 1*hcs
  · rfl

theorem rotation_surjective {c s : ℝ} (hcs : c^2+s^2 = 1) :
    Function.Surjective (rotation c s) := by
  intro v
  refine ⟨rotation c (-s) v,?_⟩
  have hn : c^2+(-s)^2 = 1 := by simpa using hcs
  simpa only [neg_neg] using rotation_inverse hn v

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Covariance of the actual five-gain map under axial rotations -/

noncomputable section

namespace BoltzmannNonuniqueness.FiveGainMap

theorem rotateState_apply (c s : ℝ) (z : State) :
    rotateState c s z = (z.1,rotation c s z.2.1,rotation c s z.2.2) := rfl

theorem rotateState_surjective {c s : ℝ} (hcs : c^2+s^2 = 1) :
    Function.Surjective (rotateState c s) := by
  rintro ⟨t,x,v⟩
  obtain ⟨x',hx'⟩ := rotation_surjective hcs x
  obtain ⟨v',hv'⟩ := rotation_surjective hcs v
  exact ⟨(t,x',v'),by simp only [rotateState_apply,hx',hv']⟩

theorem step_rotation {c s : ℝ} (hcs : c^2+s^2 = 1)
    (σ α γ μ t : ℝ) (L : V) (z : State) :
    step σ α γ μ t (rotation c s L) (rotateState c s z) =
      rotateState c s (step σ α γ μ t L z) := by
  let x := z.2.1-(z.1-t) • z.2.2
  have hx : rotation c s z.2.1-(z.1-t) • rotation c s z.2.2 = rotation c s x := by
    simp only [x,map_sub,map_smul]
  have hn (a : ℝ) : rotation c s z.2.2-axis a = rotation c s (z.2.2-axis a) := by
    simp only [map_sub,rotation_axis]
  simp only [step,rotateState_apply,hx,rotation_axial]
  refine Prod.ext rfl ?_
  refine Prod.ext rfl ?_
  rw [hn,← rotation_cross hcs,← map_add]

theorem path_rotation {c s : ℝ} (hcs : c^2+s^2 = 1)
    (σ μ : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) (k : ℕ) :
    path σ μ α γ (rotateState c s z) (rotateParameters c s q) k =
      rotateState c s (path σ μ α γ z q k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < 5
    · simp only [path,dite_eq_left hk]
      change step (σ ⟨k,hk⟩) α γ (μ ⟨k,hk⟩) (q.1 ⟨k,hk⟩)
        (rotation c s (q.2 ⟨k,hk⟩))
        (path σ μ α γ (rotateState c s z) (rotateParameters c s q) k) = _
      rw [ih,step_rotation hcs]
    · simpa only [path,dite_eq_right hk] using ih

theorem map_rotation {c s : ℝ} (hcs : c^2+s^2 = 1)
    (σ μ : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) :
    map σ μ α γ (rotateState c s z) (rotateParameters c s q) =
      rotateState c s (map σ μ α γ z q) :=
  path_rotation hcs σ μ α γ z q 5

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The connected positive-time domain of the five-gain map -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.FiveGainMap

theorem positiveDomain_eq : positiveDomain = ⋂ i : Fin 5, {q | 0 < timeProjection i q} := by
  ext q
  simp [positiveDomain,timeProjection]

theorem positiveDomain_open : IsOpen positiveDomain := by
  rw [positiveDomain_eq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (timeProjection i).continuous)

theorem positiveDomain_convex : Convex ℝ positiveDomain := by
  rw [positiveDomain_eq]
  apply convex_iInter
  intro i
  exact (convex_Ioi (0 : ℝ)).linear_preimage (timeProjection i).toLinearMap

theorem positiveDomain_preconnected : IsPreconnected positiveDomain :=
  positiveDomain_convex.isPreconnected

theorem map_analyticOnNhd {σ s : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i) (z : State) :
    AnalyticOnNhd ℝ (map σ s α γ z) positiveDomain :=
  fun q hq => map_analytic hα hγ hs z q hq

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The two final angular blocks span all three velocity directions -/

noncomputable section

open Matrix Function
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainWitness

theorem angular_pair_surjective {X Y : ℝ} (hXY : 0 < X^2+Y^2) (a b : ℝ) :
    Surjective (fun L : V × V =>
      ![X,Y,a] ⨯₃ L.1 + ![X-Y,Y+X,b] ⨯₃ L.2) := by
  intro w
  have hD : X^2+Y^2 ≠ 0 := hXY.ne'
  by_cases hX : X = 0
  · have hY : Y ≠ 0 := by
      intro hY
      simp [hX,hY] at hXY
    let v := w 1+a*w 2/Y
    refine ⟨(![-w 2/Y,0,(w 0-v)/Y],![0,0,v/Y]),?_⟩
    funext i
    fin_cases i <;> simp [cross_apply,Matrix.cons_val,hX,v] <;>
      field_simp [hY] <;> ring
  · let u := w 0+a*w 2/X
    let c := ((Y-X)*u-(X+Y)*w 1)/(X^2+Y^2)
    let d := (X*u+Y*w 1)/(X^2+Y^2)
    refine ⟨(![0,w 2/X,c],![0,0,d]),?_⟩
    funext i
    fin_cases i <;> simp [cross_apply,Matrix.cons_val,u,c,d] <;>
      field_simp [hX,hD] <;> ring

theorem final_angular_surjective (R b a₄ a₅ : ℝ) :
    Surjective (fun L : V × V =>
      ![afterThirdX R b,afterThirdY R b,a₄] ⨯₃ L.1 +
      ![afterThirdX R b-afterThirdY R b,afterThirdY R b+afterThirdX R b,a₅] ⨯₃ L.2) :=
  angular_pair_surjective (afterThird_transverse_pos R b) a₄ a₅

end BoltzmannNonuniqueness.FiveGainWitness

end

end

section

/-! # Angular parameters realizing the nondegenerate five-collision path -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

theorem witnessNormal_ne_zero {R : ℝ} (hR : 0 < R) (z : ℝ) (a : Fin 5 → ℝ)
    (i : Fin 5) : witnessNormal R z a i ≠ 0 := by
  have hX : 0 < afterThirdX R (z-a 2) :=
    mul_pos (transverse_factor_pos R _) (by linarith)
  have hXY : 0 < afterThirdX R (z-a 2)-afterThirdY R (z-a 2) := by
    have h := mul_pos (transverse_factor_pos R (z-a 2)) hR
    unfold afterThirdX afterThirdY
    nlinarith
  intro he
  have h0 := congrFun he 0
  fin_cases i <;>
    simp [witnessNormal,witnessVelocities,axis,Matrix.cons_val] at h0
  all_goals linarith

theorem witness_perpendicular (R z : ℝ) (a : Fin 5 → ℝ) (i : Fin 5) :
    witnessNormal R z a i ⬝ᵥ witnessIncrement R z a i = 0 := by
  fin_cases i <;>
    simp [witnessNormal,witnessIncrement,witnessVelocities,axis,
      Matrix.cons_val,afterThirdX,afterThirdY,transverseSquare] <;> ring

theorem witnessAngles_realize {R : ℝ} (hR : 0 < R) (z : ℝ) (a : Fin 5 → ℝ)
    (i : Fin 5) :
    witnessNormal R z a i ⨯₃ witnessAngles R z a i = witnessIncrement R z a i :=
  cross_represents (witnessNormal_ne_zero hR z a i) (witness_perpendicular R z a i)

theorem witnessAngles_last (R z : ℝ) (a : Fin 5 → ℝ) :
    witnessAngles R z a 4 = 0 := by
  simp [witnessAngles,witnessIncrement,witnessVelocities]

theorem witness_velocityPath {R : ℝ} (hR : 0 < R) (z : ℝ) (a : Fin 5 → ℝ)
    (k : ℕ) (hk : k ≤ 5) :
    velocityPath a (witnessAngles R z a) ![R,0,z] k =
      witnessVelocities R z (z-a 2) ⟨k,by omega⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlt : k < 5 := by omega
    rw [velocityPath,dite_eq_left hlt,ih (by omega)]
    change witnessVelocities R z (z-a 2) (⟨k,hlt⟩ : Fin 5).castSucc +
      witnessNormal R z a ⟨k,hlt⟩ ⨯₃ witnessAngles R z a ⟨k,hlt⟩ = _
    rw [witnessAngles_realize hR]
    unfold witnessIncrement
    abel

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The last two angular derivatives of the actual equal-time collision path -/

noncomputable section

open Matrix
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainMap

theorem cross_hasDerivAt {f g : ℝ → V} {f' g' : V} {r : ℝ}
    (hf : HasDerivAt f f' r) (hg : HasDerivAt g g' r) :
    HasDerivAt (fun y => f y ⨯₃ g y) (f' ⨯₃ g r+f r ⨯₃ g') r := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun y => f y 1*g y 2-f y 2*g y 1)
      (f' 1*g r 2-f' 2*g r 1+(f r 1*g' 2-f r 2*g' 1)) r
    convert ((hasDerivAt_pi.mp hf 1).mul (hasDerivAt_pi.mp hg 2)).sub
      ((hasDerivAt_pi.mp hf 2).mul (hasDerivAt_pi.mp hg 1)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · change HasDerivAt (fun y => f y 2*g y 0-f y 0*g y 2)
      (f' 2*g r 0-f' 0*g r 2+(f r 2*g' 0-f r 0*g' 2)) r
    convert ((hasDerivAt_pi.mp hf 2).mul (hasDerivAt_pi.mp hg 0)).sub
      ((hasDerivAt_pi.mp hf 0).mul (hasDerivAt_pi.mp hg 2)) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · change HasDerivAt (fun y => f y 0*g y 1-f y 1*g y 0)
      (f' 0*g r 1-f' 1*g r 0+(f r 0*g' 1-f r 1*g' 0)) r
    convert ((hasDerivAt_pi.mp hf 0).mul (hasDerivAt_pi.mp hg 1)).sub
      ((hasDerivAt_pi.mp hf 1).mul (hasDerivAt_pi.mp hg 0)) using 1
    all_goals try with_reducible_and_instances rfl
    ring

theorem finalVelocity_hasDerivAt (a₄ a₅ : ℝ) (v₃ L₄ A B : V) :
    HasDerivAt (fun r : ℝ => finalVelocity a₄ a₅ v₃ (L₄+r • A) (r • B))
      ((v₃-axis a₄) ⨯₃ A + (velocityStep a₄ L₄ v₃-axis a₅) ⨯₃ B) 0 := by
  have hL : HasDerivAt (fun r : ℝ => L₄+r • A) A 0 := by
    have h := (hasDerivAt_const (0 : ℝ) L₄).add
      ((hasDerivAt_id (0 : ℝ)).smul_const A)
    change HasDerivAt (fun r : ℝ => L₄+r • A) (0+1 • A) 0 at h
    simpa only [zero_add,one_smul] using h
  have h₄ : HasDerivAt (fun r : ℝ => velocityStep a₄ (L₄+r • A) v₃)
      ((v₃-axis a₄) ⨯₃ A) 0 := by
    have h := (hasDerivAt_const (0 : ℝ) v₃).add
      (cross_hasDerivAt (hasDerivAt_const (0 : ℝ) (v₃-axis a₄)) hL)
    change HasDerivAt (fun r : ℝ => velocityStep a₄ (L₄+r • A) v₃)
      (0+(0 ⨯₃ (L₄+0 • A)+(v₃-axis a₄) ⨯₃ A)) 0 at h
    simpa only [map_zero,LinearMap.zero_apply,zero_add] using h
  have hB : HasDerivAt (fun r : ℝ => r • B) B 0 := by
    have h := (hasDerivAt_id (0 : ℝ)).smul_const B
    change HasDerivAt (fun r : ℝ => r • B) (1 • B) 0 at h
    simpa only [one_smul] using h
  have h := h₄.add (cross_hasDerivAt (h₄.sub_const (axis a₅)) hB)
  change HasDerivAt (fun r : ℝ => finalVelocity a₄ a₅ v₃ (L₄+r • A) (r • B))
    ((v₃-axis a₄) ⨯₃ A+(((v₃-axis a₄) ⨯₃ A) ⨯₃ (0 • B)+
      (velocityStep a₄ (L₄+0 • A) v₃-axis a₅) ⨯₃ B)) 0 at h
  simpa only [zero_smul,add_zero,map_zero,zero_add] using h

theorem velocityPath_varyLastTwo (a : Fin 5 → ℝ) (L : Fin 5 → V) (v A B : V) (r : ℝ) :
    velocityPath a (varyLastTwo L A B r) v 5 =
      finalVelocity (a 3) (a 4) (velocityPath a L v 3) (L 3+r • A) (r • B) := by
  simp only [velocityPath,varyLastTwo,finalVelocity]
  rfl

theorem map_last_angular_hasDerivAt (σ s : Fin 5 → ℝ) (α γ τ : ℝ) (z : State)
    (L : Fin 5 → V) (A B : V) :
    let a := equalTimeSpeeds σ s α γ τ z
    let v₃ := velocityPath a L z.2.2 3
    HasDerivAt (fun r : ℝ => (map σ s α γ z
      ((fun _ => τ),varyLastTwo L A B r)).2.2)
      ((v₃-axis (a 3)) ⨯₃ A + (velocityStep (a 3) (L 3) v₃-axis (a 4)) ⨯₃ B) 0 := by
  dsimp only
  simpa only [map_equal_time,velocityPath_varyLastTwo] using
    finalVelocity_hasDerivAt (equalTimeSpeeds σ s α γ τ z 3)
      (equalTimeSpeeds σ s α γ τ z 4)
      (velocityPath (equalTimeSpeeds σ s α γ τ z) L z.2.2 3) (L 3) A B

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Derivative blocks of the actual five-gain map -/

noncomputable section

open Matrix
open scoped Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

theorem map_time (σ s : Fin 5 → ℝ) (α γ : ℝ) (z : State) (q : Parameters) :
    (map σ s α γ z q).1 = q.1 4 := path_succ_time σ s α γ z q 4 (by decide)

theorem affineParameter_derivative (q d : Parameters) :
    HasDerivAt (fun r : ℝ => q+r • d) d 0 := by
  have h := (hasDerivAt_const (0 : ℝ) q).add ((hasDerivAt_id (0 : ℝ)).smul_const d)
  change HasDerivAt (fun r : ℝ => q+r • d) (0+1 • d) 0 at h
  simpa only [zero_add,one_smul] using h

theorem apply_eq_of_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Parameters → F} {D : Parameters →L[ℝ] F} {q d : Parameters} {v : F}
    (hf : HasFDerivAt f D q) (hl : HasDerivAt (fun r : ℝ => f (q+r • d)) v 0) :
    D d = v := by
  have h := hf.comp_hasDerivAt_of_eq 0 (affineParameter_derivative q d) (by simp)
  exact h.unique hl

theorem map_derivative_time {σ s : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i)
    (z : State) (q d : Parameters) (ht : ∀ i, 0 < q.1 i) :
    (fderiv ℝ (map σ s α γ z) q d).1 = d.1 4 := by
  have hq := affineParameter_derivative q d
  have hd := (map_analytic (σ := σ) hα hγ hs z q ht).hasStrictFDerivAt.hasFDerivAt
  have hm := hd.fst.comp_hasDerivAt_of_eq 0 hq (by simp)
  have hqfst := (hasFDerivAt_fst (𝕜 := ℝ) (p := q+0 • d)).comp_hasDerivAt 0 hq
  have ht' := hasDerivAt_pi.mp hqfst 4
  change HasDerivAt (fun r => (map σ s α γ z (q+r • d)).1)
    (fderiv ℝ (map σ s α γ z) q d).1 0 at hm
  simp only [map_time] at hm
  exact hm.unique ht'

theorem map_derivative_position {σ s : Fin 5 → ℝ} {α γ τ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i) (hτ : 0 < τ)
    (z : State) (q d : Parameters) (ht : ∀ i, q.1 i = τ) :
    (fderiv ℝ (map σ s α γ z) q d).2.1 =
      positionDirection z.2.2 d.1
        (fun i : Fin 4 => (path σ s α γ z q (i.val+1)).2.2) := by
  have hq := affineParameter_derivative q d
  have hpos := map_position_hasDerivAt (σ := σ) hα hγ hs hτ z hq (by simpa using ht)
  simp only [zero_smul,add_zero] at hpos
  have hd := (map_analytic (σ := σ) hα hγ hs z q
    (fun i => by rw [ht]; exact hτ)).hasStrictFDerivAt.hasFDerivAt
  exact apply_eq_of_line hd.snd.fst hpos

theorem varyLastTwo_eq {L : Fin 5 → V} (hL : L 4 = 0) (A B : V) (r : ℝ) :
    ((fun _ => (0 : ℝ)),varyLastTwo L A B r) =
      ((fun _ => (0 : ℝ)),L)+r • lastAngularDirection A B := by
  apply Prod.ext
  · ext i
    simp [lastAngularDirection]
  · ext i j
    fin_cases i <;> simp [varyLastTwo,lastAngularDirection,vecHead,vecTail,hL]

theorem map_derivative_last_angular {σ s : Fin 5 → ℝ} {α γ τ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i) (hτ : 0 < τ)
    (z : State) (L : Fin 5 → V) (hL : L 4 = 0) (A B : V) :
    let a := equalTimeSpeeds σ s α γ τ z
    let v₃ := velocityPath a L z.2.2 3
    (fderiv ℝ (map σ s α γ z) ((fun _ => τ),L) (lastAngularDirection A B)).2.2 =
      (v₃-axis (a 3)) ⨯₃ A+(velocityStep (a 3) (L 3) v₃-axis (a 4)) ⨯₃ B := by
  dsimp only
  let q : Parameters := ((fun _ => τ),L)
  have hd := (map_analytic (σ := σ) hα hγ hs z q
    (fun _ => hτ)).hasStrictFDerivAt.hasFDerivAt
  have he (r : ℝ) : q+r • lastAngularDirection A B =
      ((fun _ => τ),varyLastTwo L A B r) := by
    apply Prod.ext
    · ext i
      simp [q,lastAngularDirection]
    · exact (congrArg Prod.snd (varyLastTwo_eq hL A B r)).symm
  have hl := map_last_angular_hasDerivAt σ s α γ τ z L A B
  simp only [← he] at hl
  exact apply_eq_of_line hd.snd.snd hl

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The first three time directions span all positions at the witness -/

noncomputable section

open Matrix Function
open scoped Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

theorem witnessPosition_surjective (R b : ℝ) : Surjective (witnessPosition R b) := by
  let M := Matrix.of ![first,second R,third R b]
  have hM : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr
    (isUnit_iff_ne_zero.mpr (first_three_det_ne_zero R b))
  have hs := (Matrix.vecMul_surjective_iff_isUnit (A := M)).mpr hM
  intro w
  obtain ⟨c,hc⟩ := hs (-w)
  refine ⟨c,?_⟩
  have he : c 0 • first+c 1 • second R+c 2 • third R b = -w := by
    rw [← hc]
    ext i
    simp [Matrix.vecMul,dotProduct,Fin.sum_univ_succ,M]
    ring
  simp only [witnessPosition,he,neg_neg]

theorem positionDirection_at_witness (R z : ℝ) (a : Fin 5 → ℝ) (c : V) :
    positionDirection ![R,0,z] (firstTimeDirection c).1
      (fun i : Fin 4 => witnessVelocities R z (z-a 2) ⟨i.val+1,by omega⟩) =
      witnessPosition R (z-a 2) c := by
  ext i
  fin_cases i <;>
    simp [positionDirection,firstTimeDirection,witnessVelocities,witnessPosition,
      first,second,third,afterThirdX,afterThirdY,Fin.sum_univ_succ] <;> ring

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Combining the time, position, and angular derivative blocks -/

noncomputable section

open Function
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainMap

theorem surjective_of_blocks (T : Parameters →L[ℝ] State)
    (ht : ∀ d, (T d).1 = d.1 4)
    (hp : Surjective (fun c => (T (firstTimeDirection c)).2.1))
    (hz : ∀ A B, (T (lastAngularDirection A B)).2.1 = 0)
    (hv : Surjective (fun p : V × V => (T (lastAngularDirection p.1 p.2)).2.2)) :
    Surjective T := by
  rintro ⟨t,x,v⟩
  let e : Parameters := (![0,0,0,0,1],0)
  let base := t • e
  obtain ⟨c,hc⟩ := hp (x-(T base).2.1)
  change (T (firstTimeDirection c)).2.1 = x-(T base).2.1 at hc
  let q := base+firstTimeDirection c
  obtain ⟨⟨A,B⟩,hAB⟩ := hv (v-(T q).2.2)
  change (T (lastAngularDirection A B)).2.2 = v-(T q).2.2 at hAB
  refine ⟨q+lastAngularDirection A B,?_⟩
  apply Prod.ext
  · rw [ht]
    simp [q,base,e,firstTimeDirection,lastAngularDirection]
  · apply Prod.ext
    · change (T (q+lastAngularDirection A B)).2.1 = x
      rw [map_add]
      change (T q).2.1+(T (lastAngularDirection A B)).2.1 = x
      rw [hz,add_zero]
      change (T (base+firstTimeDirection c)).2.1 = x
      rw [map_add]
      change (T base).2.1+(T (firstTimeDirection c)).2.1 = x
      rw [hc]
      abel
    · rw [map_add]
      change (T q).2.2+(T (lastAngularDirection A B)).2.2 = v
      rw [hAB]
      abel

end BoltzmannNonuniqueness.FiveGainMap

end

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

theorem coordinateMatrix_det {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) : (coordinateMatrix n r).det = -r := by
  have hD := (normSq_pos hr hrsq).ne'
  simp [coordinateMatrix,Matrix.det_fin_three]
  field_simp
  unfold normSq at *
  linear_combination (n 0^2+n 1^2+n 2^2)*hrsq

theorem coordinates_apply (n L : V) (r : ℝ) :
    coordinates n r L = ![n 0*L 1-n 1*L 0,
      (n 2*(n 0*L 0+n 1*L 1)-(n 0^2+n 1^2)*L 2)/r,
      (n 0*L 0+n 1*L 1+n 2*L 2)/normSq n] := by
  ext i
  fin_cases i <;> simp [coordinates,coordinateMatrix,Matrix.mulVec,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem coordinates_map_volume {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) :
    Measure.map (coordinates n r) volume = ENNReal.ofReal r⁻¹ • volume := by
  have hd := coordinateMatrix_det hr hrsq
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi (hd.trans_ne (neg_ne_zero.mpr hr.ne'))
  simpa only [coordinates,hd,inv_neg,abs_neg,abs_of_pos (inv_pos.mpr hr)] using h

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Bounded redundant parameters for bounded collision increments -/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix ENNReal

namespace BoltzmannNonuniqueness.RedundantPlane

theorem measurable_normalDensity : Measurable normalDensity :=
  measurable_const.indicator measurableSet_Icc

theorem normalDensity_le_one (x : ℝ) : normalDensity x ≤ 1 :=
  indicator_le_self' (fun _ _ => bot_le) x

theorem normalDensity_support {x : ℝ} (hx : normalDensity x ≠ 0) : x ∈ Icc 0 1 := by
  by_contra h
  exact hx (indicator_of_notMem h _)

theorem lintegral_normalDensity : ∫⁻ x, normalDensity x = 1 := by
  rw [normalDensity,lintegral_indicator_const measurableSet_Icc]
  simp

theorem cross_normSq_identity (n L : V) :
    normSq n * normSq L = normSq (n ⨯₃ L)+(n ⬝ᵥ L)^2 := by
  simp [normSq,cross_apply,vec3_dotProduct]
  ring

theorem coordinates_last (n L : V) (r : ℝ) :
    coordinates n r L 2 = (n ⬝ᵥ L)/normSq n := by
  simp [coordinates_apply,vec3_dotProduct]

theorem normSq_decomposition {n L : V} {r : ℝ} (hD : normSq n ≠ 0) :
    normSq L = normSq (n ⨯₃ L)/normSq n+
      normSq n*(coordinates n r L 2)^2 := by
  rw [coordinates_last]
  field_simp
  nlinarith only [cross_normSq_identity n L]

theorem normSq_parameter_bound {n L : V} {r δ R R₁ : ℝ}
    (hδ : 0 < δ) (hnlow : δ^2 ≤ normSq n) (hnhigh : normSq n ≤ R^2)
    (hk : normSq (n ⨯₃ L) ≤ R₁^2)
    (hcoef : |coordinates n r L 2| ≤ 1) :
    normSq L ≤ R₁^2/δ^2+R^2 := by
  have hD : 0 < normSq n := (sq_pos_of_pos hδ).trans_le hnlow
  rw [normSq_decomposition hD.ne']
  have hcoefsq : (coordinates n r L 2)^2 ≤ 1 := by
    nlinarith [sq_abs (coordinates n r L 2),abs_nonneg (coordinates n r L 2)]
  apply add_le_add
  · exact (div_le_div_of_nonneg_right hk hD.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg R₁) (sq_pos_of_pos hδ) hnlow)
  · exact (mul_le_of_le_one_right hD.le hcoefsq).trans hnhigh

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Integrating the redundant coordinate in the collision plane -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal

namespace BoltzmannNonuniqueness.RedundantPlane

theorem splitThree_measurePreserving : MeasurePreserving splitThree := by
  exact (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    ((MeasurePreserving.id volume).prod (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)))

theorem lintegral_redundant {ζ : ℝ → ℝ≥0∞} (hζ : Measurable ζ)
    (hζone : ∫⁻ u, ζ u = 1) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q : V, ζ (q 2)*F (q 0,q 1)) = ∫⁻ z : ℝ, ∫⁻ s : ℝ, F (z,s) := by
  let g : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun q => ζ q.2.2 * F (q.1,q.2.1)
  have hg : Measurable g := (hζ.comp measurable_snd.snd).mul
    (hF.comp (measurable_fst.prodMk measurable_snd.fst))
  have he : (fun q : V => ζ (q 2)*F (q 0,q 1)) = g ∘ splitThree := rfl
  rw [he]
  change (∫⁻ q : V, g (splitThree q)) = _
  rw [splitThree_measurePreserving.lintegral_comp hg]
  change (∫⁻ q, g q ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume))) = _
  rw [lintegral_prod _ hg.aemeasurable]
  apply lintegral_congr
  intro z
  change (∫⁻ q, g (z,q) ∂((volume : Measure ℝ).prod volume)) = _
  have hz : Measurable (fun q : ℝ × ℝ => g (z,q)) := hg.comp measurable_prodMk_left
  rw [lintegral_prod _ hz.aemeasurable]
  apply lintegral_congr
  intro s
  change (∫⁻ u : ℝ, ζ u * F (z,s)) = F (z,s)
  rw [lintegral_mul_const _ hζ,hζone,one_mul]

theorem redundant_coordinates_integral {n : V} {r : ℝ} (hr : 0 < r)
    (hrsq : r^2 = n 0^2+n 1^2) {ζ : ℝ → ℝ≥0∞} (hζ : Measurable ζ)
    (hζone : ∫⁻ u, ζ u = 1) {F : ℝ × ℝ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ L : V, ζ (coordinates n r L 2)*F (coordinates n r L 0,coordinates n r L 1)) =
      ENNReal.ofReal r⁻¹ * ∫⁻ z : ℝ, ∫⁻ s : ℝ, F (z,s) := by
  let g : V → ℝ≥0∞ := fun q => ζ (q 2)*F (q 0,q 1)
  have hg : Measurable g := (hζ.comp (measurable_pi_apply 2)).mul
    (hF.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1)))
  have hA : Measurable (coordinates n r) := (coordinates n r).continuous_of_finiteDimensional.measurable
  have he := lintegral_map (μ := (volume : Measure V)) hg hA
  rw [coordinates_map_volume hr hrsq,lintegral_smul_measure] at he
  simpa only [g,Function.comp_def,smul_eq_mul,lintegral_redundant hζ hζone hF] using he.symm

end BoltzmannNonuniqueness.RedundantPlane

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ChartPointLift
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

theorem measurable_density {h : Velocity → ℝ≥0∞} (hh : Measurable h) (v : Velocity) :
    Measurable (density h v) := by
  have hn : Measurable (fun y : Coordinates => normal v y.1) :=
    measurable_transverse.comp (measurable_const.sub measurable_fst)
  exact (measurable_const.mul hn.norm.inv.ennreal_ofReal).mul
    (hh.comp (measurable_point v))

theorem region_eq_measure (c : Measure Velocity) {h : Velocity → ℝ≥0∞}
    (hh : Measurable h) (v : Velocity) {S : Set Coordinates} (hS : MeasurableSet S) :
    chartRegionGain c h v S = measure c h v S := by
  classical
  rw [measure, withDensity_apply _ hS, ← lintegral_indicator hS]
  rw [lintegral_prod _ ((measurable_density hh v).indicator hS).aemeasurable]
  have hi (p : Velocity) :
      (∫⁻ zs : ℝ × ℝ, S.indicator (density h v) (p, zs) ∂(volume.prod volume)) =
        ∫⁻ z : ℝ, ∫⁻ s : ℝ, S.indicator (density h v) (p, (z, s)) :=
    lintegral_prod _ (((measurable_density hh v).indicator hS).comp
      measurable_prodMk_left).aemeasurable
  simp_rw [hi]
  have he : ∀ p z s, S.indicator (density h v) (p, (z, s)) =
      2 * (ENNReal.ofReal (‖normal v p‖⁻¹) *
        S.indicator (fun y => h (chart v y.1 y.2.1 y.2.2)) (p, (z, s))) := by
    intro p z s
    by_cases hm : (p, (z, s)) ∈ S
    · simp only [indicator_of_mem hm, density, mul_assoc]
    · simp only [indicator_of_notMem hm, mul_zero]
  simp_rw [he, lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

theorem total_eq (c : Measure Velocity) {h : Velocity → ℝ≥0∞}
    (hh : Measurable h) (v : Velocity) :
    chartGain c h v = measure c h v univ := by
  simpa only [chartRegionGain, indicator_univ, chartGain] using
    region_eq_measure c hh v MeasurableSet.univ

theorem measure_smul (a : ℝ≥0∞) (c : Measure Velocity)
    (h : Velocity → ℝ≥0∞) (v : Velocity) :
    measure (a • c) h v = a • measure c h v := by
  rw [measure, Measure.prod_smul_left, withDensity_smul_measure]
  rfl

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Joint measurability of the collision-plane chart and normalized density -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.ChartKernel

theorem measurable_joint_normalized_density (q : ℝ) :
    Measurable (fun p : Velocity × Coordinates =>
      density (fun ξ => ENNReal.ofReal (H q ξ/H q p.1)) p.1 p.2) := by
  have hn : Measurable (fun p : Velocity × Coordinates => normal p.1 p.2.1) :=
    measurable_transverse.comp (measurable_fst.sub measurable_snd.fst)
  exact (measurable_const.mul hn.norm.inv.ennreal_ofReal).mul
    (((measurable_H q).comp measurable_joint_point).div
      ((measurable_H q).comp measurable_fst)).ennreal_ofReal

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Pulling the joint chart through a kinetic base projection -/

noncomputable section
open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.ChartKernel
variable {X : Type*} [MeasurableSpace X]

theorem measurable_lifted_density (q : ℝ) :
    Measurable (fun p : (X × Velocity) × Coordinates =>
      density (fun ξ => ENNReal.ofReal (H q ξ/H q p.1.2)) p.1.2 p.2) := by
  let f : (X × Velocity) × Coordinates → Velocity × Coordinates := fun p => (p.1.2,p.2)
  have hf : Measurable f := measurable_fst.snd.prodMk measurable_snd
  simpa only [Function.comp_def,f] using (measurable_joint_normalized_density q).comp hf

end BoltzmannNonuniqueness.ChartKernel

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

/-! # The free cold core in Eulerian coordinates -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetFreeTransport

theorem measurable_free (η K α γ s d t : ℝ) (a : Bool) :
    Measurable (free η K α γ s d t a) := by
  apply (measurable_density η K α γ s d a).comp
  unfold flight transverse axial
  fun_prop

end BoltzmannNonuniqueness.JetFreeTransport

end

end

section

/-! # Joint measurability of the transported cold core -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetFreeTransport

theorem measurable_joint_free (η K α γ s d : ℝ) (a : Bool) :
    Measurable (fun p : ℝ × JetPrototype.Phase => free η K α γ s d p.1 a p.2) := by
  apply (JetPrototype.measurable_density η K α γ s d a).comp
  unfold JetBarrier.flight VelocityWeight.transverse VelocityWeight.axial
  fun_prop

theorem measurable_uncurried_free (η K α γ s d : ℝ) (a : Bool) :
    Measurable (fun p : (ℝ × JetPrototype.Space) × Velocity =>
      free η K α γ s d p.1.1 a (p.1.2,p.2)) := by
  let f : ((ℝ × JetPrototype.Space) × Velocity) → ℝ × JetPrototype.Phase :=
    fun p => (p.1.1,(p.1.2,p.2))
  have hf : Measurable f :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  simpa only [Function.comp_def,f] using (measurable_joint_free η K α γ s d a).comp hf

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedKernelAction
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The normalized Carleman gain as a measurable velocity kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

theorem coordinateKernel_apply (c : Kernel X Velocity) [IsSFiniteKernel c]
    (q : ℝ) (z : X × Velocity) :
    coordinateKernel c q z = normalizedMeasure (c z.1) q z.2 := by
  rw [coordinateKernel,Kernel.withDensity_apply _ (measurable_lifted_density q),Kernel.prod_apply]
  rfl

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # S-finiteness and integration for the normalized gain input kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

theorem inputKernel_eq_map (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) :
    inputKernel c q = (Kernel.id ×ₖ coordinateKernel c q).map
      (fun p : (X × Velocity) × Coordinates =>
        PlaneChart.chart p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  apply Kernel.ext
  intro z
  rw [Kernel.map_apply _ (measurable_lifted_point (X := X)),Kernel.prod_apply,
    Kernel.id_apply,Measure.dirac_prod,
    Measure.map_map (measurable_lifted_point (X := X)) measurable_prodMk_left]
  rfl

instance inputKernel_sFinite (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) :
    IsSFiniteKernel (inputKernel c q) := by
  rw [inputKernel_eq_map]
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem lintegral_inputKernel (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ)
    (z : X × Velocity) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ v, f v ∂inputKernel c q z) =
      ∫⁻ y, f (PlaneChart.chart z.2 y.1 y.2.1 y.2.2)
        ∂normalizedMeasure (c z.1) q z.2 := by
  change (∫⁻ v, f v ∂(coordinateKernel c q z).map
    (fun y => PlaneChart.chart z.2 y.1 y.2.1 y.2.2)) = _
  rw [lintegral_map hf (measurable_point z.2),coordinateKernel_apply]

end BoltzmannNonuniqueness.ChartKernel

end

end

section

/-! # Integrating an input against the normalized collision kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

theorem measure_weighted (c : Measure Velocity) {h f : Velocity → ℝ≥0∞}
    (hh : Measurable h) (hf : Measurable f) (v : Velocity) :
    (measure c h v).withDensity (fun y => f (PlaneChart.chart v y.1 y.2.1 y.2.2)) =
      measure c (fun ξ => h ξ*f ξ) v := by
  have ht : Measurable (fun y : Coordinates => f (PlaneChart.chart v y.1 y.2.1 y.2.2)) :=
    hf.comp (measurable_point v)
  rw [measure,← withDensity_mul _ (measurable_density hh v) ht]
  congr 1
  funext y
  unfold density
  exact mul_assoc _ _ _

theorem lintegral_normalized (c : Measure Velocity) (q : ℝ) (v : Velocity)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f (PlaneChart.chart v y.1 y.2.1 y.2.2) ∂normalizedMeasure c q v) =
      chartGain c (fun ξ => ENNReal.ofReal (H q ξ/H q v)*f ξ) v := by
  have hh := ((measurable_H q).div_const (H q v)).ennreal_ofReal
  calc
    _ = ((measure c (fun ξ => ENNReal.ofReal (H q ξ/H q v)) v).withDensity
        (fun y => f (PlaneChart.chart v y.1 y.2.1 y.2.2))) univ := by
      rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      rfl
    _ = (measure c (fun ξ => ENNReal.ofReal (H q ξ/H q v)*f ξ) v) univ :=
      congrArg (fun μ : Measure Coordinates => μ univ) (measure_weighted c hh hf v)
    _ = _ := (total_eq c (hh.mul hf) v).symm

theorem lintegral_inputKernel_eq_gain {X : Type*} [MeasurableSpace X]
    (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) (z : X × Velocity)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂inputKernel c q z) =
      chartGain (c z.1) (fun ξ => ENNReal.ofReal (H q ξ/H q z.2)*f ξ) z.2 := by
  rw [lintegral_inputKernel c q z hf,lintegral_normalized (c z.1) q z.2 hf]

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_FreeCoreGainKernel
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual free cold core supplies a normalized positive gain kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem coreKernel_apply (η K α γ s d : ℝ) (a : Bool) (p : ℝ × JetPrototype.Space) :
    coreKernel η K α γ s d a p = volume.withDensity
      (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d p.1 a (p.2,v))) :=
  Kernel.withDensity_apply _
    (JetFreeTransport.measurable_uncurried_free η K α γ s d a).ennreal_ofReal p

instance normalizedCoreKernel_sFinite (η K α γ s d q : ℝ) (a : Bool) :
    IsSFiniteKernel (normalizedCoreKernel η K α γ s d q a) :=
  ChartKernel.inputKernel_sFinite _ _

end BoltzmannNonuniqueness.JetCoreSheet

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

end BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreMap

theorem axialMap_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (σ d z w : ℝ) :
    axialMap σ α γ (r*s) d (r*t) (r*z) w = axialMap σ α γ s d t z w := by
  unfold axialMap
  rw [show r*z-r*t*d*w = r*(z-t*d*w) by ring,
    AxialFlow.velocity_dilation hr hα hγ hs ht]

end BoltzmannNonuniqueness.JetCoreMap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_JetCoreConvergence
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem sourceFoot_continuous {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (σ d z : ℝ) :
    Continuous (JetCoreMap.sourceFoot σ α γ s d t z) :=
  (AxialFlow.foot_lipschitzWith hα hγ hs ht).continuous.comp
    (continuous_const.sub (continuous_const.mul continuous_id))

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

end BoltzmannNonuniqueness.JetCoreDensity

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PullbackRegularLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Quantitative chart estimates for the finite-gain pullback

A normalized derivative within one half of the identity gives an injective
chart. A positive Jacobian lower bound then controls pullback integrals,
including arbitrary bounded measurable masks in the parameter density.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.GainPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsAddHaarMeasure μ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem chart_injective {s : Set E} (hs : Convex ℝ s)
    {f : E → E} {f' : E → E →L[ℝ] E} (A : E ≃L[ℝ] E)
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hclose : ∀ x ∈ s,
      ‖A.symm.toContinuousLinearMap.comp (f' x) - ContinuousLinearMap.id ℝ E‖ ≤ 1/2) :
    InjOn f s := by
  intro x hx y hy hxy
  have hder (z) (hz : z ∈ s) :
      HasFDerivWithinAt (fun w => A.symm (f w))
        (A.symm.toContinuousLinearMap.comp (f' z)) s z :=
    A.symm.toContinuousLinearMap.hasFDerivAt.comp_hasFDerivWithinAt z (hf z hz)
  have h := hs.norm_image_sub_le_of_norm_hasFDerivWithin_le' hder hclose hx hy
  simp only [hxy,sub_self,ContinuousLinearMap.id_apply,zero_sub,norm_neg] at h
  have hn : ‖y-x‖ = 0 := by nlinarith [norm_nonneg (y-x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm

theorem jacobian_pullback_bound {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hi : InjOn f s)
    {c : ℝ} (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(f' x).det|)
    (g : E → ℝ≥0∞) :
    ∫⁻ x in s, g (f x) ∂μ ≤ (ENNReal.ofReal c)⁻¹ * ∫⁻ y in f '' s, g y ∂μ := by
  have hbound : ENNReal.ofReal c * (∫⁻ x in s, g (f x) ∂μ) ≤
      ∫⁻ y in f '' s, g y ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hs hf hi g]
    apply setLIntegral_mono' hs
    intro x hx
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hdet x hx)) le_rfl
  calc
    _ = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * ∫⁻ x in s, g (f x) ∂μ) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel
        (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top,one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hbound

theorem masked_jacobian_pullback_bound {s : Set E} (hs : MeasurableSet s)
    {f : E → E} {f' : E → E →L[ℝ] E}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hi : InjOn f s)
    {c : ℝ} (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(f' x).det|)
    (g ρ : E → ℝ≥0∞) {B : ℝ≥0∞} (hB : B ≠ ∞) (hρ : ∀ x ∈ s, ρ x ≤ B) :
    ∫⁻ x in s, ρ x * g (f x) ∂μ ≤
      (B * (ENNReal.ofReal c)⁻¹) * ∫⁻ y in f '' s, g y ∂μ := by
  calc
    _ ≤ ∫⁻ x in s, B * g (f x) ∂μ := by
      apply setLIntegral_mono' hs
      intro x hx
      exact mul_le_mul' (hρ x hx) le_rfl
    _ = B * ∫⁻ x in s, g (f x) ∂μ := by rw [lintegral_const_mul' _ _ hB]
    _ ≤ B * ((ENNReal.ofReal c)⁻¹ * ∫⁻ y in f '' s, g y ∂μ) :=
      mul_le_mul' le_rfl (jacobian_pullback_bound hs hf hi hc hdet g)
    _ = _ := by rw [mul_assoc]

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # A regular chart persists under locally uniform convergence of derivatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem regular_derivative_neighborhood (A : E ≃L[ℝ] E)
    (hA : 0 < |A.toContinuousLinearMap.det|) :
    ∃ δ > 0, ∀ B : E →L[ℝ] E, ‖B-A.toContinuousLinearMap‖ < δ →
      ‖A.symm.toContinuousLinearMap.comp B - ContinuousLinearMap.id ℝ E‖ ≤ 1/2 ∧
      |A.toContinuousLinearMap.det|/2 ≤ |B.det| := by
  have hcomp : A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := by ext x; simp
  have hN : Continuous (fun B : E →L[ℝ] E =>
      ‖A.symm.toContinuousLinearMap.comp B - ContinuousLinearMap.id ℝ E‖) := by fun_prop
  have hD : Continuous (fun B : E →L[ℝ] E => |B.det|) :=
    ContinuousLinearMap.continuous_det.abs
  have hn := hN.continuousAt.eventually (Iio_mem_nhds (show
      ‖A.symm.toContinuousLinearMap.comp A.toContinuousLinearMap -
        ContinuousLinearMap.id ℝ E‖ < 1/2 by rw [hcomp,sub_self,norm_zero]; norm_num))
  have hd := hD.continuousAt.eventually
    (Ioi_mem_nhds (show |A.toContinuousLinearMap.det|/2 < |A.toContinuousLinearMap.det| by linarith))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hn.and hd)
  refine ⟨δ,hδ,fun B hB => ?_⟩
  have h := hball (show B ∈ ball A.toContinuousLinearMap δ by
    simpa only [mem_ball,dist_eq_norm] using hB)
  exact ⟨h.1.le,h.2.le⟩

/-- On a small ball at a regular point, all sufficiently late charts are
injective with one common positive Jacobian lower bound. -/
theorem eventually_regular_ball {O : Set E} (hO : IsOpen O) {x₀ : E} (hx₀ : x₀ ∈ O)
    {f' : E → E →L[ℝ] E} (hcont : ContinuousAt f' x₀)
    (A : E ≃L[ℝ] E) (hAt : f' x₀ = A.toContinuousLinearMap)
    (hA : 0 < |A.toContinuousLinearMap.det|)
    {F : ℕ → E → E} {F' : ℕ → E → E →L[ℝ] E}
    (hF : ∀ n, ∀ x ∈ O, HasFDerivAt (F n) (F' n x) x)
    (hconv : ∀ r > 0, ball x₀ r ⊆ O →
      TendstoUniformlyOn F' f' atTop (ball x₀ r)) :
    ∃ r > 0, ball x₀ r ⊆ O ∧
      ∀ᶠ n in atTop, InjOn (F n) (ball x₀ r) ∧
        ∀ x ∈ ball x₀ r, |A.toContinuousLinearMap.det|/2 ≤ |(F' n x).det| := by
  obtain ⟨δ,hδ,hδspec⟩ := regular_derivative_neighborhood A hA
  have hnear : ∀ᶠ x in 𝓝 x₀, ‖f' x-A.toContinuousLinearMap‖ < δ/2 := by
    have h := hcont.eventually (Metric.ball_mem_nhds (f' x₀) (half_pos hδ))
    simpa only [mem_ball,dist_eq_norm,hAt] using h
  obtain ⟨r,hr,hrspec⟩ := Metric.mem_nhds_iff.mp (hnear.and (hO.mem_nhds hx₀))
  have hsub : ball x₀ r ⊆ O := fun x hx => (hrspec hx).2
  refine ⟨r,hr,hsub,?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hconv r hr hsub)) (δ/2) (half_pos hδ)] with n hn
  have hbound (x) (hx : x ∈ ball x₀ r) : ‖F' n x-A.toContinuousLinearMap‖ < δ := by
    have h₁ : ‖F' n x-f' x‖ < δ/2 := by
      simpa only [dist_eq_norm,norm_sub_rev] using hn x hx
    have h₂ := (hrspec hx).1
    calc
      _ ≤ ‖F' n x-f' x‖+‖f' x-A.toContinuousLinearMap‖ := by
        simpa only [dist_eq_norm] using
          dist_triangle (F' n x) (f' x) A.toContinuousLinearMap
      _ < δ := by linarith
  refine ⟨chart_injective (convex_ball x₀ r) A
    (fun x hx => (hF n x (hsub hx)).hasFDerivWithinAt)
    (fun x hx => (hδspec _ (hbound x hx)).1),?_⟩
  exact fun x hx => (hδspec _ (hbound x hx)).2

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Gluing local pullback convergence outside a null critical set -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

theorem lintegral_finite_union_le {X I : Type*} [MeasurableSpace X]
    {μ : Measure X} (s : Finset I) (U : I → Set X) (f : X → ℝ≥0∞) :
    ∫⁻ x in ⋃ i ∈ s, U i, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in U i, f x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [show (⋃ j ∈ insert i s, U j) = U i ∪ ⋃ j ∈ s, U j by simp,
      Finset.sum_insert hi]
    exact (lintegral_union_le f _ _).trans (add_le_add le_rfl ih)

/-- Local integral convergence on a neighborhood of each noncritical point
suffices on a compact set, provided the integrands have a common bound. -/
theorem compact_integral_zero_of_local {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    {μ : Measure X} [OuterRegular μ] {K Z : Set X} (hK : IsCompact K)
    (hZ : μ Z = 0) {f : ℕ → X → ℝ≥0∞} {M : ℝ≥0∞} (hM : M ≠ ∞)
    (hbound : ∀ n x, x ∈ K → f n x ≤ M)
    (hlocal : ∀ x ∈ K \ Z, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      Tendsto (fun n => ∫⁻ y in U, f n y ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, f n x ∂μ) atTop (𝓝 0) := by
  classical
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hhalf : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨δ,hδ,hδsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hM hhalf.ne'
  obtain ⟨Bad,hZBad,hBad,hBadsmall⟩ := Z.exists_isOpen_lt_of_lt (μ := μ) δ (by
    rw [hZ]; exact ENNReal.coe_pos.mpr hδ)
  let R := {x // x ∈ K \ Z}
  have hchoice (x : R) := hlocal x x.2
  choose U hUopen hUmem hUlim using hchoice
  have hcover : K \ Bad ⊆ ⋃ x : R, U x := by
    intro x hx
    have hxR : x ∈ K \ Z := ⟨hx.1,fun hz => hx.2 (hZBad hz)⟩
    exact mem_iUnion.mpr ⟨⟨x,hxR⟩,hUmem ⟨x,hxR⟩⟩
  obtain ⟨I,hI⟩ := (hK.diff hBad).elim_finite_subcover U hUopen hcover
  have hsum : Tendsto (fun n => ∑ i ∈ I, ∫⁻ x in U i, f n x ∂μ) atTop (𝓝 0) := by
    have h := tendsto_finsetSum I (fun i _ => hUlim i)
    simpa using h
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hsum (ε/2) hhalf] with n hn
  have hKB : (∫⁻ x in K ∩ Bad, f n x ∂μ) ≤ M*μ Bad := by
    apply (show (∫⁻ x in K ∩ Bad, f n x ∂μ) ≤ M*μ (K ∩ Bad) from ?_).trans
      (mul_le_mul' le_rfl (measure_mono inter_subset_right))
    calc
      _ ≤ ∫⁻ _x in K ∩ Bad, M ∂μ := by
        apply setLIntegral_mono' (hK.measurableSet.inter hBad.measurableSet)
        intro x hx
        exact hbound n x hx.1
      _ = _ := by simp
  have hset : K ⊆ (K ∩ Bad) ∪ ⋃ i ∈ I, U i := by
    intro x hx
    by_cases hb : x ∈ Bad
    · exact Or.inl ⟨hx,hb⟩
    · exact Or.inr (hI ⟨hx,hb⟩)
  calc
    _ ≤ ∫⁻ x in (K ∩ Bad) ∪ ⋃ i ∈ I, U i, f n x ∂μ := lintegral_mono_set hset
    _ ≤ (∫⁻ x in K ∩ Bad, f n x ∂μ) + ∫⁻ x in ⋃ i ∈ I, U i, f n x ∂μ :=
      lintegral_union_le _ _ _
    _ ≤ M*μ Bad + ∑ i ∈ I, ∫⁻ x in U i, f n x ∂μ :=
      add_le_add hKB (lintegral_finite_union_le I U (f n))
    _ ≤ ε/2+ε/2 := add_le_add
      ((mul_le_mul' le_rfl hBadsmall.le).trans (by simpa [mul_comm] using hδsmall.le)) hn
    _ = ε := ENNReal.add_halves ε

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Pullback estimates after adjoining the unused parameter coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]

theorem product_chart_bound {s : Set (P × Q)} (hs : MeasurableSet s)
    {F : P × Q → P × Q} {F' : P × Q → (P × Q) →L[ℝ] P × Q}
    (hf : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x) (hi : InjOn F s)
    {c : ℝ} (hc : 0 < c) (hdet : ∀ x ∈ s, c ≤ |(F' x).det|)
    {W : Set Q} (hWfin : volume W ≠ ∞)
    (himage : ∀ x ∈ s, (F x).2 ∈ W)
    (g : P → ℝ≥0∞) (hg : Measurable g) (ρ : P × Q → ℝ≥0∞)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hρ : ∀ x ∈ s, ρ x ≤ B) :
    ∫⁻ x in s, ρ x * g (F x).1 ∂((volume : Measure P).prod volume) ≤
      ((B*(ENNReal.ofReal c)⁻¹)*volume W) * ∫⁻ y, g y := by
  have hmain := masked_jacobian_pullback_bound
    (μ := (volume : Measure P).prod volume) hs hf hi hc hdet
    (fun y => g y.1) ρ hB hρ
  have hsub : F '' s ⊆ (univ : Set P) ×ˢ W := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨mem_univ _,himage x hx⟩
  have hproduct : (∫⁻ y in (univ : Set P) ×ˢ W, g y.1
      ∂((volume : Measure P).prod volume)) = volume W * ∫⁻ y, g y := by
    rw [setLIntegral_prod (fun y : P × Q => g y.1) (by fun_prop)]
    simp only [lintegral_const,Measure.restrict_apply_univ,Measure.restrict_univ]
    rw [lintegral_mul_const' _ _ hWfin,mul_comm]
  calc
    _ ≤ (B*(ENNReal.ofReal c)⁻¹) * (∫⁻ y in F '' s, g y.1
        ∂((volume : Measure P).prod volume)) := hmain
    _ ≤ (B*(ENNReal.ofReal c)⁻¹) * (∫⁻ y in (univ : Set P) ×ˢ W, g y.1
        ∂((volume : Measure P).prod volume)) := mul_le_mul' le_rfl (lintegral_mono_set hsub)
    _ = _ := by rw [hproduct]; ac_rfl

theorem tendsto_product_chart_zero {s : Set (P × Q)} (hs : MeasurableSet s)
    {F : ℕ → P × Q → P × Q} {F' : ℕ → P × Q → (P × Q) →L[ℝ] P × Q}
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → P × Q → ℝ≥0∞}
    {c : ℝ} (hc : 0 < c) {B : ℝ≥0∞} (hB : B ≠ ∞)
    {W : Set Q} (hWfin : volume W ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hchart : ∀ᶠ n in atTop,
      (∀ x ∈ s, HasFDerivWithinAt (F n) (F' n x) s x) ∧
      InjOn (F n) s ∧ (∀ x ∈ s, c ≤ |(F' n x).det|) ∧
      (∀ x ∈ s, (F n x).2 ∈ W) ∧ (∀ x ∈ s, ρ n x ≤ B))
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in s, ρ n x*g n (F n x).1
      ∂((volume : Measure P).prod volume)) atTop (𝓝 0) := by
  have hfinite : (B*(ENNReal.ofReal c)⁻¹)*volume W ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hB
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hc)))) hWfin
  have hscale := ENNReal.Tendsto.const_mul (a := (B*(ENNReal.ofReal c)⁻¹)*volume W)
    hL (Or.inr hfinite)
  simp only [mul_zero] at hscale
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hchart] with n hn
  exact product_chart_bound hs hn.1 hn.2.1 hc hn.2.2.1 hWfin hn.2.2.2.1
    (g n) (hg n) (ρ n) hB hn.2.2.2.2

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Local pullback convergence after adjoining a complementary projection -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

section Derivatives
variable {E P Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem augmented_derivative_uniform {s : Set E}
    {F : ℕ → E → E →L[ℝ] P} {f : E → E →L[ℝ] P}
    (h : TendstoUniformlyOn F f atTop s) (π : E →L[ℝ] Q) :
    TendstoUniformlyOn (fun n x => (F n x).prod π) (fun x => (f x).prod π) atTop s := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h ε hε] with n hn
  intro x hx
  have he : (f x).prod π-(F n x).prod π = (f x-F n x).prod 0 := by
    ext y <;> simp
  simpa only [dist_eq_norm,he,ContinuousLinearMap.opNorm_prod,Prod.norm_def,norm_zero,
    max_eq_left (norm_nonneg _)] using hn x hx

end Derivatives

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]
local notation "E" => P × Q

theorem local_augmented_pullback_zero {O : Set E} (hO : IsOpen O) {x₀ : E} (hx₀ : x₀ ∈ O)
    {Φ : ℕ → E → P} {Φ' : ℕ → E → E →L[ℝ] P} {φ' : E → E →L[ℝ] P}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (Φ n) (Φ' n x) x)
    (hcont : ContinuousAt φ' x₀) (π : E →L[ℝ] Q) (A : E ≃L[ℝ] E)
    (hA : (φ' x₀).prod π = A.toContinuousLinearMap)
    (hconv : ∀ r > 0, ball x₀ r ⊆ O → TendstoUniformlyOn Φ' φ' atTop (ball x₀ r))
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → E → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hg : ∀ n, Measurable (g n)) (hρ : ∀ n x, x ∈ O → ρ n x ≤ B)
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    ∃ r > 0, ball x₀ r ⊆ O ∧ Tendsto
      (fun n => ∫⁻ x in ball x₀ r, ρ n x*g n (Φ n x)
        ∂((volume : Measure P).prod volume)) atTop (𝓝 0) := by
  let G (n : ℕ) (x : E) : E := (Φ n x,π x)
  let G' (n : ℕ) (x : E) : E →L[ℝ] E := (Φ' n x).prod π
  have hG (n) (x) (hx : x ∈ O) : HasFDerivAt (G n) (G' n x) x :=
    (hder n x hx).prodMk π.hasFDerivAt
  have hc : ContinuousAt (fun x => (φ' x).prod π) x₀ :=
    (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) ℝ).continuous.continuousAt.comp
      (hcont.prodMk continuousAt_const)
  have ha : 0 < |A.toContinuousLinearMap.det| := abs_pos.mpr A.toLinearEquiv.isUnit_det'.ne_zero
  obtain ⟨r,hr,hrO,hevent⟩ := eventually_regular_ball hO hx₀ hc A hA ha hG
    (fun r hr hrO => augmented_derivative_uniform (hconv r hr hrO) π)
  let W : Set Q := closedBall 0 (‖π‖*(‖x₀‖+r))
  have hWfin : volume W ≠ ∞ := (isCompact_closedBall (0 : Q) _).measure_lt_top.ne
  have hW (x : E) (hx : x ∈ ball x₀ r) : π x ∈ W := by
    have hnorm : ‖x‖ ≤ ‖x₀‖+r := by
      have h := norm_le_norm_add_norm_sub x₀ x
      rw [norm_sub_rev x₀ x] at h
      have hxr : ‖x-x₀‖ < r := by simpa only [mem_ball,dist_eq_norm] using hx
      linarith
    change dist (π x) 0 ≤ ‖π‖*(‖x₀‖+r)
    rw [dist_zero_right]
    exact (π.le_opNorm x).trans (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
  refine ⟨r,hr,hrO,?_⟩
  apply tendsto_product_chart_zero (F := G) (F' := G') isOpen_ball.measurableSet
    (half_pos ha) hB hWfin hg ?_ hL
  filter_upwards [hevent] with n hn
  exact ⟨fun x hx => (hG n x (hrO hx)).hasFDerivWithinAt,
    hn.1,hn.2,hW,fun x hx => hρ n x (hrO hx)⟩

end BoltzmannNonuniqueness.GainPullback

end

end

section

/-! # Robust compact pullback convergence for submersions

Regularity is expressed by a complementary linear projection at each point.
The critical set is null. Parameter masks need only have a common bound.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]
local notation "E" => P × Q

theorem compact_submersion_pullback_zero {O K Z : Set E} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) (hZ : ((volume : Measure P).prod volume) Z = 0)
    {Φ : ℕ → E → P} {Φ' : ℕ → E → E →L[ℝ] P} {φ' : E → E →L[ℝ] P}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (Φ n) (Φ' n x) x)
    (hcont : ∀ x ∈ O, ContinuousAt φ' x)
    (hreg : ∀ x ∈ K \ Z, ∃ π : E →L[ℝ] Q, ∃ A : E ≃L[ℝ] E,
      (φ' x).prod π = A.toContinuousLinearMap)
    (hconv : ∀ x ∈ O, ∀ r > 0, ball x r ⊆ O →
      TendstoUniformlyOn Φ' φ' atTop (ball x r))
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → E → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n x, x ∈ O → ρ n x ≤ B) (hgM : ∀ n y, g n y ≤ M)
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, ρ n x*g n (Φ n x)
      ∂((volume : Measure P).prod volume)) atTop (𝓝 0) := by
  apply compact_integral_zero_of_local hK hZ (ENNReal.mul_ne_top hB hM)
    (fun n x hx => mul_le_mul' (hρ n x (hKO hx)) (hgM n _))
  intro x hx
  obtain ⟨π,A,hA⟩ := hreg x hx
  obtain ⟨r,hr,_,hlim⟩ := local_augmented_pullback_zero hO (hKO hx.1)
    hder (hcont x (hKO hx.1)) π A hA (hconv x (hKO hx.1)) hB hg hρ hL
  exact ⟨ball x r,isOpen_ball,mem_ball_self hr,hlim⟩

end BoltzmannNonuniqueness.GainPullback

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SubmersionNullPreimage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A surjective derivative admits the complementary chart used in the pullback -/

noncomputable section

open Function MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {P Q : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
local notation "E" => P × Q

theorem exists_complementary_chart (L : E →L[ℝ] P) (hL : Surjective L) :
    ∃ π : E →L[ℝ] Q, ∃ A : E ≃L[ℝ] E, L.prod π = A.toContinuousLinearMap := by
  classical
  obtain ⟨R,hR⟩ := L.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hL)
  have hR' (y : P) : L (R y) = y := LinearMap.congr_fun hR y
  let κ : E →ₗ[ℝ] LinearMap.ker L.toLinearMap :=
    (LinearMap.id-R.comp L.toLinearMap).codRestrict _ (fun x => by
      change L (x-R (L x)) = 0
      rw [map_sub,hR',sub_self])
  let A₀ : E ≃ₗ[ℝ] P × LinearMap.ker L.toLinearMap :=
    { L.toLinearMap.prod κ with
      invFun := fun y => R y.1+y.2
      left_inv := by
        intro x
        change R (L x)+(x-R (L x)) = x
        abel
      right_inv := by
        rintro ⟨y,z⟩
        have hz : L (z : E) = 0 := z.property
        apply Prod.ext
        · change L (R y+z) = y
          rw [map_add,hR',hz,add_zero]
        · apply Subtype.ext
          change R y+z-R (L (R y+z)) = z
          rw [map_add,hR',hz,add_zero]
          abel }
  have hdim : Module.finrank ℝ (LinearMap.ker L.toLinearMap) = Module.finrank ℝ Q := by
    have h := L.toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hL,finrank_top,Module.finrank_prod] at h
    omega
  let e : LinearMap.ker L.toLinearMap ≃ₗ[ℝ] Q := LinearEquiv.ofFinrankEq _ _ hdim
  let A : E ≃L[ℝ] E :=
    (A₀.trans (LinearEquiv.prodCongr (LinearEquiv.refl ℝ P) e)).toContinuousLinearEquiv
  let π : E →L[ℝ] Q := (ContinuousLinearMap.snd ℝ P Q).comp A.toContinuousLinearMap
  refine ⟨π,A,?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext <;> rfl

variable
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [Measure.IsAddHaarMeasure (volume : Measure Q)]

/-- The L1 form of the manuscript's uniform pullback estimate. -/
theorem compact_surjective_pullback_zero {O K Z : Set E} (hO : IsOpen O)
    (hK : IsCompact K) (hKO : K ⊆ O) (hZ : ((volume : Measure P).prod volume) Z = 0)
    {Φ : ℕ → E → P} {Φ' : ℕ → E → E →L[ℝ] P} {φ' : E → E →L[ℝ] P}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (Φ n) (Φ' n x) x)
    (hcont : ∀ x ∈ O, ContinuousAt φ' x)
    (hreg : ∀ x ∈ K \ Z, Surjective (φ' x))
    (hconv : ∀ x ∈ O, ∀ r > 0, ball x r ⊆ O →
      TendstoUniformlyOn Φ' φ' atTop (ball x r))
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → E → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n x, x ∈ O → ρ n x ≤ B) (hgM : ∀ n y, g n y ≤ M)
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, ρ n x*g n (Φ n x)
      ∂((volume : Measure P).prod volume)) atTop (𝓝 0) :=
  compact_submersion_pullback_zero hO hK hKO hZ hder hcont
    (fun x hx => exists_complementary_chart (φ' x) (hreg x hx))
    hconv hB hM hg hρ hgM hL

end BoltzmannNonuniqueness.GainPullback

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

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Only finitely many geometric shells meet a fixed radial window -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.GeometricMesh

theorem index_mono {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b) (hη : 0 < η) :
    index a η ≤ index b η :=
  Int.floor_mono (div_le_div_of_nonneg_right (Real.log_le_log ha hab) hη.le)

theorem jetScale_ratio_exact {s₀ η r : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) (hη : 0 < η) (j : ℕ) :
    JetGeometry.jetScale s₀ η j/r = point (phase (s₀/r) η) η (jetMeshIndex s₀ η r j) := by
  rw [JetGeometry.jetScale,scale_ratio hs₀ hr hη.ne']
  unfold point jetMeshIndex
  push_cast
  rfl

theorem jetIndex_at_meshIndex (s₀ η : ℝ) (r : ℕ → ℝ) (n j : ℕ) :
    jetIndex s₀ η r (jetMeshIndex s₀ η (r n) j) n = j := by
  simp [jetIndex,annularIndex,jetMeshIndex]

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # A uniform finite list of non-small scales in a geometric mesh -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.GeometricMesh

theorem index_point_div_phase {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) (k : ℤ) :
    index (point θ η k/θ) η = k := by
  unfold point index
  rw [mul_div_cancel_left₀ _ hθ.ne',Real.log_exp,mul_div_cancel_left₀ _ hη.ne']
  exact Int.floor_intCast k

theorem point_window {θ η δ R : ℝ} (hθ₁ : 1 ≤ θ) (hθ₂ : θ ≤ Real.exp η)
    (hη : 0 < η) (hδ : 0 < δ) {k : ℤ}
    (hlo : δ ≤ point θ η k) (hhi : point θ η k ≤ R) :
    k ∈ Icc (index (δ/Real.exp η) η) (index R η) := by
  have hθ : 0 < θ := zero_lt_one.trans_le hθ₁
  have hp : 0 < point θ η k := mul_pos hθ (Real.exp_pos _)
  have hl : δ/Real.exp η ≤ point θ η k/θ := by
    apply (div_le_div_iff₀ (Real.exp_pos η) hθ).mpr
    exact (mul_le_mul_of_nonneg_left hθ₂ hδ.le).trans
      (mul_le_mul_of_nonneg_right hlo (Real.exp_pos η).le)
  have hh : point θ η k/θ ≤ R := by
    apply (div_le_iff₀ hθ).mpr
    exact hhi.trans (le_mul_of_one_le_right (hp.le.trans hhi) hθ₁)
  have he := index_point_div_phase hθ hη k
  exact ⟨he ▸ index_mono (div_pos hδ (Real.exp_pos η)) hl hη,
    he ▸ index_mono (div_pos hp hθ) hh hη⟩

end BoltzmannNonuniqueness.GeometricMesh

end

end

section

/-! # Actual retained mesh scales have positive limits and vanishing thermal widths -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness.GeometricMesh

theorem mesh_scale_tendsto_zero {s₀ η θ : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (k : ℤ) :
    Tendsto (fun n => JetGeometry.jetScale s₀ η (jetIndex s₀ η r k n)) atTop (𝓝 0) := by
  have hm := hrlim.mul (jet_scale_approximation hs₀ hη hr hrlim hphase k)
  have he (n : ℕ) : r n*(JetGeometry.jetScale s₀ η (jetIndex s₀ η r k n)/r n) =
      JetGeometry.jetScale s₀ η (jetIndex s₀ η r k n) := by
    field_simp [(hr n).ne']
  simpa only [he,zero_mul] using hm

theorem mesh_width_tendsto_zero {s₀ η θ : ℝ} {r : ℕ → ℝ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : ∀ n, 0 < r n)
    (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (d₀ : ℝ) (k : ℤ) :
    Tendsto (fun n => d₀*JetGeometry.jetScale s₀ η (jetIndex s₀ η r k n)^10)
      atTop (𝓝 0) := by
  simpa using (mesh_scale_tendsto_zero hs₀ hη hr hrlim hphase k).pow 10 |>.const_mul d₀

end BoltzmannNonuniqueness.GeometricMesh

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveVolterra
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive backward gain iteration on free kinetic characteristics -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_inner_measurable (K : Kernel Published.KineticPhase Velocity) [IsSFiniteKernel K]
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (z : Published.KineticPhase) :
    Measurable (fun s => ∫⁻ v, f ((flight z s).1,v) ∂K (flight z s)) := by
  have hflight : Measurable (flight z) := by unfold flight; fun_prop
  let J := K.comap (flight z) hflight
  have hm : Measurable (Function.uncurry (fun s v => f ((flight z s).1,v))) := by
    apply hf.comp
    unfold flight
    fun_prop
  exact hm.lintegral_kernel_prod_right (κ := J)

theorem step_add (a : ℝ) (K : Kernel Published.KineticPhase Velocity) [IsSFiniteKernel K]
    {f g : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    step a K (f+g) = step a K f+step a K g := by
  funext z
  unfold step
  simp only [Pi.add_apply]
  have hi (s : ℝ) : Measurable (fun v => f ((flight z s).1,v)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  simp_rw [lintegral_add_left (hi _)]
  exact lintegral_add_left (step_inner_measurable K hf z) _

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Measurable positive iterates and localization to time slabs -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_measurable (a : ℝ) (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) : Measurable (step a K f) := by
  have hflight : Measurable (fun p : KineticPhase × ℝ => flight p.1 p.2) := by
    unfold flight
    fun_prop
  let J := K.comap (fun p : KineticPhase × ℝ => flight p.1 p.2) hflight
  have hm : Measurable (fun p : (KineticPhase × ℝ) × Velocity =>
      f ((flight p.1.1 p.1.2).1,p.2)) :=
    hf.comp (((hflight.comp measurable_fst).fst).prodMk measurable_snd)
  have hi : Measurable (fun p : KineticPhase × ℝ =>
      ∫⁻ v, f ((flight p.1 p.2).1,v) ∂K (flight p.1 p.2)) :=
    hm.lintegral_kernel_prod_right' (κ := J)
  let D : Set (KineticPhase × ℝ) := {p | a < p.2 ∧ p.2 ≤ p.1.1.1}
  have hD : MeasurableSet D := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd measurable_fst.fst.fst)
  have h : Measurable (fun z : KineticPhase => ∫⁻ s : ℝ,
      D.indicator (fun p : KineticPhase × ℝ =>
        ∫⁻ v, f ((flight p.1 p.2).1,v) ∂K (flight p.1 p.2)) (z,s)) :=
    (hi.indicator hD).lintegral_prod_right'
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  rw [step,← lintegral_indicator measurableSet_Ioc]
  rfl

theorem step_slab_mono {a T : ℝ} (K : Kernel KineticPhase Velocity)
    {f g : KineticPhase → ℝ≥0∞}
    (h : ∀ z, z.1.1 ∈ Icc a T → f z ≤ g z)
    {z : KineticPhase} (hz : z.1.1 ∈ Icc a T) : step a K f z ≤ step a K g z := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  apply lintegral_mono
  intro v
  exact h _ ⟨hs.1.le,hs.2.trans hz.2⟩

end BoltzmannNonuniqueness.PositiveIteration

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LargeOutput
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.inputKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.normalizedCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_WeightLocalL1
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.inputKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.coldCylinderVolume_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.normalizedCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A positive lower bound for the hot weight on bounded velocity sets -/

noncomputable section

namespace BoltzmannNonuniqueness.VelocityWeight

theorem compactLower_pos (R : ℝ) : 0 < compactLower R :=
  mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

theorem compactLower_le_H (q : ℝ) {R : ℝ} (hR : 0 ≤ R) {v : Velocity}
    (hv : ‖v‖ ≤ R) : compactLower R ≤ H q v := by
  have hs : ‖v‖^2 ≤ R^2 := sq_le_sq₀ (norm_nonneg v) hR |>.mpr hv
  have he : Real.exp (-R^2) ≤ Real.exp (-‖v‖^2) := Real.exp_le_exp.mpr (neg_le_neg hs)
  have hp : (1+R^2)^(-50 : ℝ) ≤ (1+‖v‖^2)^(-50 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  unfold compactLower H
  calc
    _ ≤ Real.exp (-‖v‖^2)*(1+‖v‖^2)^(-50 : ℝ) :=
      mul_le_mul he hp (by positivity) (by positivity)
    _ ≤ _ := le_mul_of_one_le_right (by positivity)
      (by linarith [singularity_nonneg q (transverse v)])

end BoltzmannNonuniqueness.VelocityWeight

end

end

section

/-! # Bounds for the normalized weight on retained nonaxial velocities -/

noncomputable section

namespace BoltzmannNonuniqueness.VelocityWeight

theorem H_le_offAxis {q b : ℝ} (hq : 0 ≤ q) (hb : 0 < b)
    {v : Velocity} (hv : b ≤ ‖transverse v‖) : H q v ≤ 1+b^(-q) := by
  have hs : singularity q (transverse v) ≤ b^(-q) :=
    Real.rpow_le_rpow_of_nonpos hb hv (neg_nonpos.mpr hq)
  have he : Real.exp (-‖v‖^2) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg ‖v‖))
  have hp : (1+‖v‖^2)^(-50 : ℝ) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 1 by norm_num)
      (show (1 : ℝ) ≤ 1+‖v‖^2 by nlinarith [sq_nonneg ‖v‖]) (by norm_num : (-50 : ℝ) ≤ 0)
    simpa using h
  unfold H
  calc
    _ ≤ 1*(1+singularity q (transverse v)) :=
      mul_le_mul_of_nonneg_right
        ((mul_le_mul he hp (by positivity) (by norm_num)).trans_eq (one_mul 1))
        (by linarith [singularity_nonneg q (transverse v)])
    _ ≤ 1+b^(-q) := by simpa using add_le_add_left hs 1

theorem H_ratio_le_offAxis {q b V : ℝ} (hq : 0 ≤ q) (hb : 0 < b) (hV : 0 ≤ V)
    {v ξ : Velocity} (hv : ‖v‖ ≤ V) (hξ : b ≤ ‖transverse ξ‖) :
    H q ξ/H q v ≤ (1+b^(-q))/compactLower V := by
  exact (div_le_div_of_nonneg_right (H_le_offAxis hq hb hξ) (H_pos q v).le).trans
    (div_le_div_of_nonneg_left (by positivity) (compactLower_pos V) (compactLower_le_H q hV hv))

end BoltzmannNonuniqueness.VelocityWeight

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_OffAxisBoxExhaustion
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Choosing a bounded representative of a collision kernel on the null axis -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

variable {X : Type*} [MeasurableSpace X]

theorem offAxis_apply (K : Kernel (X × Velocity) Velocity) (z : X × Velocity)
    (hz : transverse z.2 ≠ 0) : offAxis K z = K z := by
  classical
  simp [offAxis,Kernel.piecewise_apply,hz]

theorem offAxis_axis (K : Kernel (X × Velocity) Velocity) (z : X × Velocity)
    (hz : transverse z.2 = 0) : offAxis K z = 0 := by
  classical
  simp [offAxis,Kernel.piecewise_apply,hz]

end BoltzmannNonuniqueness.ChartKernel

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_FreeCoreMismatch
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual free-core kernel in the coordinates of positive iteration -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCoreSheet

instance kineticFreeKernel_sFinite (η K α γ s d q : ℝ) (a : Bool) :
    IsSFiniteKernel (kineticFreeKernel η K α γ s d q a) := by
  unfold kineticFreeKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DilatedCoreDensity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Positive gain kernels under the actual cap dilation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem dilatedColdKernel_apply (r η K α γ s d : ℝ) (sign : Bool) (z : SpaceTime) :
    dilatedColdKernel r η K α γ s d sign z =
      ENNReal.ofReal r • kineticColdKernel η K α γ s d sign (r*z.1,r • z.2) := by
  rw [dilatedColdKernel,Kernel.withDensity_apply _ measurable_const,withDensity_const]
  rfl

instance dilatedFreeKernel_sFinite (r η K α γ s d q : ℝ) (sign : Bool) :
    IsSFiniteKernel (dilatedFreeKernel r η K α γ s d q sign) := by
  unfold dilatedFreeKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TranslatedCoreKernel
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dilated free kernels for the actual periodic labels -/

noncomputable section

open MeasureTheory ProbabilityTheory
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open scoped ENNReal

namespace BoltzmannNonuniqueness.ChartKernel

theorem inputKernel_congr_base {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (c : Kernel X Velocity) (d : Kernel Y Velocity) [IsSFiniteKernel c] [IsSFiniteKernel d]
    {x : X} {y : Y} (h : c x = d y) (q : ℝ) (v : Velocity) :
    inputKernel c q (x,v) = inputKernel d q (y,v) := by
  change (coordinateKernel c q (x,v)).map _ = (coordinateKernel d q (y,v)).map _
  rw [coordinateKernel_apply,coordinateKernel_apply,h]

end BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetCopyDatum

instance copyFreeKernel_sFinite (r s₀ η K α γ d₀ q : ℝ) (i : Label) :
    IsSFiniteKernel (copyFreeKernel r s₀ η K α γ d₀ q i) := by
  unfold copyFreeKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem copyFreeKernel_eq (r s₀ η K α γ d₀ q : ℝ) (i : Label) (z : KineticPhase) :
    copyFreeKernel r s₀ η K α γ d₀ q i z =
      JetCoreSheet.dilatedFreeKernel r η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) q i.positive
        ((z.1.1,z.1.2-r⁻¹ • latticeVector i.lattice),z.2) := by
  by_cases hv : VelocityWeight.transverse z.2 = 0
  · rw [copyFreeKernel,JetCoreSheet.dilatedFreeKernel,ChartKernel.offAxis_axis _ z hv,
      ChartKernel.offAxis_axis _ ((z.1.1,z.1.2-r⁻¹ • latticeVector i.lattice),z.2) hv]
  · rw [copyFreeKernel,JetCoreSheet.dilatedFreeKernel,ChartKernel.offAxis_apply _ z hv,
      ChartKernel.offAxis_apply _ ((z.1.1,z.1.2-r⁻¹ • latticeVector i.lattice),z.2) hv]
    exact ChartKernel.inputKernel_congr_base (copyColdKernel r s₀ η K α γ d₀ i)
      (JetCoreSheet.dilatedColdKernel r η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) i.positive)
      (x := z.1) (y := (z.1.1,z.1.2-r⁻¹ • latticeVector i.lattice)) rfl q z.2

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MainCoreScaleWindow
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurable regions selecting the unique main periodic core -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem mainCoreRegion_unique {s₀ η r : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    {i j : Label} {z : SpaceTime}
    (hi : z ∈ mainCoreRegion s₀ η r N i) (hj : z ∈ mainCoreRegion s₀ η r N j) : i = j :=
  common_point_label hs₀ hsmax hη hηmax hi.2.1 hi.2.2 hj.2.2

theorem mainCoreKernel_eq {s₀ η r : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (K : Label → Kernel SpaceTime Velocity) {z : SpaceTime} {i : Label}
    (hi : z ∈ mainCoreRegion s₀ η r N i) : mainCoreKernel s₀ η r N K z = K i z := by
  classical
  apply Measure.ext
  intro E hE
  rw [mainCoreKernel,Kernel.sum_apply' _ _ hE,tsum_eq_single i]
  · simp [Kernel.piecewise_apply',hi]
  · intro j hji
    have hj : z ∉ mainCoreRegion s₀ η r N j :=
      fun hj => hji (mainCoreRegion_unique hs₀ hsmax hη hηmax hj hi)
    simp [Kernel.piecewise_apply',hj]

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_SelectedCoreSelection
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The selected main free core and its uniform positive gain bound -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.JetLattice
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

instance selectedFreeKernel_sFinite (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) :
    IsSFiniteKernel (selectedFreeKernel r s₀ η K α γ d₀ q N) := by
  unfold selectedFreeKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance positiveMainKernel_sFinite (r s₀ η K α γ d₀ q : ℝ) (N : ℕ) :
    IsSFiniteKernel (positiveMainKernel r s₀ η K α γ d₀ q N) := by
  unfold positiveMainKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Pointwise identification of the selected free kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem selectedFreeKernel_eq_copy {s₀ η r K α γ d₀ q : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    {i : Label} {z : Published.KineticPhase} (hi : z.1 ∈ mainCoreRegion s₀ η r N i) :
    selectedFreeKernel r s₀ η K α γ d₀ q N z = copyFreeKernel r s₀ η K α γ d₀ q i z := by
  by_cases hv : transverse z.2 = 0
  · rw [selectedFreeKernel,copyFreeKernel,ChartKernel.offAxis_axis _ _ hv,
      ChartKernel.offAxis_axis _ _ hv]
  · rw [selectedFreeKernel,copyFreeKernel,ChartKernel.offAxis_apply _ _ hv,
      ChartKernel.offAxis_apply _ _ hv]
    exact ChartKernel.inputKernel_congr_base _ _
      (mainCoreKernel_eq hs₀ hsmax hη hηmax _ hi) q z.2

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_CoreDensityTranslation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The exact free-core integral over three Euclidean thermal parameters -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermalCoordinates_measurePreserving :
    MeasurePreserving thermalCoordinates volume ((volume : Measure Transverse).prod volume) := by
  exact (MeasurePreserving.symm SheetMeasures.join HotRectangleDensity.join_measurePreserving).comp
    (PiLp.volume_preserving_toLp (Fin 3))

theorem core_thermal_integral {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t) (η K : ℝ) (a : Bool) (x : JetPrototype.Space)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ p, f p ∂volume.withDensity
      (fun p => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x,p)))) =
    ∫⁻ w : FiveGainMap.V, ENNReal.ofReal (thermalWeight η K α γ s d t a x w)*
      f (thermalPoint α γ s d t a x w) := by
  have hvm := (JetCoreMeasure.velocity_measurePreserving hα hγ hs hd ht
    (JetPrototype.sign a) x.2).measurable
  have hwm := (weight_measurable hα hγ hs ht η K d a x).ennreal_ofReal
  have hfm : Measurable (fun w => f (JetCoreMeasure.velocityMap
      (JetPrototype.sign a) α γ s d t x.2 w)) := hf.comp hvm
  rw [← measure_identity hα hγ hs hd ht η K a x,lintegral_map hf hvm,
    lintegral_withDensity_eq_lintegral_mul _ hwm hfm]
  exact (thermalCoordinates_measurePreserving.lintegral_comp
    (hwm.mul hfm)).symm

theorem thermalCoordinates_apply (w : FiveGainMap.V) :
    thermalCoordinates w = (transverse (WithLp.toLp 2 w),axial (WithLp.toLp 2 w)) := by
  change MeasurableEquiv.prodComm.symm (split (WithLp.toLp 2 w)) = _
  rw [split_apply]
  rfl

theorem thermalPoint_eq_center (α γ s d t : ℝ) (a : Bool) (x : JetPrototype.Space)
    (xv w : FiveGainMap.V) (hx : xv 2 = x.2) :
    thermalPoint α γ s d t a x w = WithLp.toLp 2
      (FiveGainMap.thermalCenter (JetPrototype.sign a) α γ s d t xv w) := by
  apply split.injective
  simp only [thermalPoint,JetCoreMeasure.velocityMap,thermalCoordinates_apply,split_apply,
    PlaneChart.transverse_join,PlaneChart.axial_join]
  apply Prod.ext
  · change JetCoreMap.axialMap _ _ _ _ _ _ x.2 (w 2) =
      JetCoreMap.axialMap _ _ _ _ _ _ (xv 2) (w 2)
    rw [hx]
  · apply (WithLp.ext_iff 2).mpr
    funext i
    fin_cases i <;> simp [transverse,FiveGainMap.thermalCenter]

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Uniform density and support bounds in the actual thermal parameters -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermalWeight_bound {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η d : ℝ) (a : Bool) (x : JetPrototype.Space) (w : FiveGainMap.V) :
    thermalWeight η K α γ s d t a x w ≤
      ((K*max 1 (α*γ)⁻¹)/(s+t))*JetThermalKernel.bound := by
  apply (weight_bound hK hα hγ hs ht η d a x (thermalCoordinates w)).trans
  exact mul_le_mul_of_nonneg_left (JetThermalKernel.J_le _)
    (div_nonneg (mul_nonneg hK (le_max_of_le_left zero_le_one)) (by positivity))

theorem thermalWeight_zero {η K α γ s d t : ℝ} (a : Bool) (x : JetPrototype.Space)
    {w : FiveGainMap.V} (hw : 1 ≤ ‖WithLp.toLp 2 w‖) :
    thermalWeight η K α γ s d t a x w = 0 := by
  have he : SheetMeasures.join (thermalCoordinates w) = WithLp.toLp 2 w :=
    SheetMeasures.join.apply_symm_apply _
  unfold thermalWeight weight
  rw [he,JetThermalKernel.J_zero hw,mul_zero]

theorem dilated_thermalWeight_bound {r K α γ s t : ℝ} (hr : 0 < r)
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η d : ℝ) (a : Bool) (x : JetPrototype.Space) (w : FiveGainMap.V) :
    r*thermalWeight η K α γ (r*s) d (r*t) a (r • x) w ≤
      ((K*max 1 (α*γ)⁻¹)/(s+t))*JetThermalKernel.bound := by
  apply (mul_le_mul_of_nonneg_left
    (thermalWeight_bound hK hα hγ (mul_pos hr hs) (mul_nonneg hr.le ht) η d a (r • x) w)
    hr.le).trans_eq
  have hst : s+t ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hs ht)
  field_simp

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Joint measurable thermal parameters on nonnegative time

Clamping time at zero provides a globally measurable representative, equal to
the physical parametrization at every nonnegative collision time.
-/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem clamped_sourceFoot_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (σ d : ℝ) :
    Measurable (fun p : ThermalArguments =>
      sourceFoot σ α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2)) := by
  have hc := (AxialFlow.clamped_foot_continuous (σ := σ) hα hγ hs).comp
    (show Continuous (fun p : ThermalArguments =>
      (p.1,p.2.1.2-max 0 p.1*d*(p.2.2 2))) by fun_prop)
  exact hc.measurable

theorem clamped_axialMap_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (σ d : ℝ) :
    Measurable (fun p : ThermalArguments =>
      axialMap σ α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2)) := by
  have hc := (AxialFlow.clamped_velocity_continuous (σ := σ) hα hγ hs).comp
    (show Continuous (fun p : ThermalArguments =>
      (p.1,p.2.1.2-max 0 p.1*d*(p.2.2 2))) by fun_prop)
  change Measurable (fun p : ThermalArguments =>
    d*(p.2.2 2)+AxialFlow.velocity σ α γ s (max 0 p.1)
      (p.2.1.2-max 0 p.1*d*(p.2.2 2)))
  exact (by fun_prop : Measurable (fun p : ThermalArguments => d*(p.2.2 2))).add hc.measurable

theorem clamped_thermalPoint_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (d : ℝ) (a : Bool) :
    Measurable (fun p : ThermalArguments =>
      thermalPoint α γ s d (max 0 p.1) a p.2.1 p.2.2) := by
  have ha := clamped_axialMap_measurable hα hγ hs (sign a) d
  have ht : Measurable (fun p : ThermalArguments => d • transverse (WithLp.toLp 2 p.2.2)) :=
    by fun_prop
  have h := SheetMeasures.join.measurable.comp (ht.prodMk ha)
  simp only [thermalPoint,thermalCoordinates_apply,JetCoreMeasure.velocityMap]
  change Measurable (fun p : ThermalArguments =>
    SheetMeasures.join (d • transverse (WithLp.toLp 2 p.2.2),
      axialMap (sign a) α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2)))
  exact h

theorem clamped_thermalWeight_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (η K d : ℝ) (a : Bool) :
    Measurable (fun p : ThermalArguments =>
      thermalWeight η K α γ s d (max 0 p.1) a p.2.1 p.2.2) := by
  have hfoot := clamped_sourceFoot_measurable hα hγ hs (sign a) d
  have hm : Measurable (fun p : ThermalArguments =>
      (JetGeometry.mask η s a).indicator (fun _ => (1 : ℝ))
        (p.2.1.1-max 0 p.1 • (d • transverse (WithLp.toLp 2 p.2.2)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η s a)).comp (by fun_prop)
  have hS : Measurable (fun p : ThermalArguments =>
      JetAxialWeight.S (γ*sourceFoot (sign a) α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2)/s)) :=
    JetAxialWeight.continuous_S.measurable.comp ((hfoot.const_mul γ).div_const s)
  have hc : Measurable (fun p : ThermalArguments =>
      compressed K α γ s (max 0 p.1)
        (sourceFoot (sign a) α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2))) := by
    unfold compressed
    exact (hS.const_mul K).div (measurable_const.add
      ((((by fun_prop : Measurable (fun p : ThermalArguments => max 0 p.1)).mul_const α).mul_const γ).mul hS))
  have hcut : Measurable (fun p : ThermalArguments =>
      (Ioo (-(1/8 : ℝ)) (1/8)).indicator (fun _ => (1 : ℝ))
        (sourceFoot (sign a) α γ s d (max 0 p.1) p.2.1.2 (p.2.2 2))) :=
    (measurable_const.indicator measurableSet_Ioo).comp hfoot
  have hj : Measurable (fun p : ThermalArguments => JetThermalKernel.J (WithLp.toLp 2 p.2.2)) :=
    JetThermalKernel.J_smooth.continuous.measurable.comp (by fun_prop)
  convert (hm.mul (hcut.mul hc)).mul hj using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  have hjp : SheetMeasures.join (transverse (WithLp.toLp 2 p.2.2),
      axial (WithLp.toLp 2 p.2.2)) = WithLp.toLp 2 p.2.2 := by
    rw [← thermalCoordinates_apply]
    exact SheetMeasures.join.apply_symm_apply _
  simp only [thermalWeight,weight,thermalCoordinates_apply,hjp,Pi.mul_apply]
  change _ = _
  rw [← indicator_mul_left]
  simp only [one_mul]
  rfl

end BoltzmannNonuniqueness.JetCoreDensity

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DilatedTwoCoreLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Exact measure representation of the dilated cold core

The masks stay at their original physical scale. Dilation is carried by the
measure factor and the time/position arguments, without identifying masks.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.ChartKernel

theorem inputKernel_smul_base {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (c : Kernel X Velocity) (d : Kernel Y Velocity) [IsSFiniteKernel c] [IsSFiniteKernel d]
    {x : X} {y : Y} {a : ℝ≥0∞} (h : c x = a • d y) (q : ℝ) (v : Velocity) :
    inputKernel c q (x,v) = a • inputKernel d q (y,v) := by
  change (coordinateKernel c q (x,v)).map _ = a • (coordinateKernel d q (y,v)).map _
  rw [coordinateKernel_apply,coordinateKernel_apply]
  unfold normalizedMeasure
  rw [h,measure_smul,Measure.map_smul]

end BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem rescaledCoreMeasure_axis (r η K α γ μ d q : ℝ) (sign : Bool)
    (t : ℝ) (x : JetPrototype.Space) {v : Velocity} (hv : transverse v = 0) :
    rescaledCoreMeasure r η K α γ μ d q sign t x v = 0 := by
  unfold rescaledCoreMeasure
  rw [ChartKernel.offAxis_axis _ _ hv,smul_zero]

theorem dilatedFreeKernel_eq_rescaled {r : ℝ} (hr : 0 < r)
    (η K α γ s d q : ℝ) (sign : Bool) (z : Published.KineticPhase) :
    dilatedFreeKernel r η K α γ s d q sign z =
      rescaledCoreMeasure r η K α γ (s/r) d q sign z.1.1
        (JetPeriodicDatum.spatialMap z.1.2) z.2 := by
  have hs : r*(s/r) = s := by field_simp
  have hx : JetPeriodicDatum.spatialMap (r • z.1.2) =
      r • JetPeriodicDatum.spatialMap z.1.2 := by
    ext i <;> rfl
  by_cases hv : transverse z.2 = 0
  · rw [dilatedFreeKernel,ChartKernel.offAxis_axis _ _ hv,
      rescaledCoreMeasure_axis _ _ _ _ _ _ _ _ _ _ _ hv]
  · rw [dilatedFreeKernel,ChartKernel.offAxis_apply _ z hv,rescaledCoreMeasure,
      ChartKernel.offAxis_apply _ ((r*z.1.1,r • JetPeriodicDatum.spatialMap z.1.2),z.2) hv,hs]
    have h := ChartKernel.inputKernel_smul_base
      (dilatedColdKernel r η K α γ s d sign) (coreKernel η K α γ s d sign)
      (x := z.1) (y := (r*z.1.1,r • JetPeriodicDatum.spatialMap z.1.2))
      (a := ENNReal.ofReal r) ?_ q z.2
    · exact h
    · rw [dilatedColdKernel_apply]
      change ENNReal.ofReal r • coreKernel η K α γ s d sign
        (r*z.1.1,JetPeriodicDatum.spatialMap (r • z.1.2)) = _
      rw [hx]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PullbackCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Transport of the compact submersion estimate to the actual parameter space -/

noncomputable section

open Function MeasureTheory MeasureTheory.Measure Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.GainPullback

variable {E P Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
  [MeasurableSpace E] [BorelSpace E]
  [MeasureSpace P] [BorelSpace P] [IsAddHaarMeasure (volume : Measure P)]
  [MeasureSpace Q] [BorelSpace Q] [IsAddHaarMeasure (volume : Measure Q)]

/-- The domain coordinates may differ from the output plus complementary coordinates.
Only compact-local convergence of the derivatives is needed. -/
theorem compact_pullback_zero_coordinates (e : E ≃L[ℝ] P × Q)
    {μ : Measure E} [IsAddHaarMeasure μ]
    {O K Z : Set E} (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O) (hZ : μ Z = 0)
    {Φ : ℕ → E → P} {Φ' : ℕ → E → E →L[ℝ] P} {φ' : E → E →L[ℝ] P}
    (hder : ∀ n, ∀ x ∈ O, HasFDerivAt (Φ n) (Φ' n x) x)
    (hcont : ∀ x ∈ O, ContinuousAt φ' x)
    (hreg : ∀ x ∈ K \ Z, Surjective (φ' x))
    (hconv : ∀ C : Set E, IsCompact C → C ⊆ O → TendstoUniformlyOn Φ' φ' atTop C)
    {g : ℕ → P → ℝ≥0∞} {ρ : ℕ → E → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n x, x ∈ O → ρ n x ≤ B) (hgM : ∀ n y, g n y ≤ M)
    (hL : Tendsto (fun n => ∫⁻ y, g n y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x in K, ρ n x*g n (Φ n x) ∂μ) atTop (𝓝 0) := by
  let ν : Measure (P × Q) := (volume : Measure P).prod volume
  let em := e.toHomeomorph.toMeasurableEquiv
  have hmap : μ.map e = addHaarScalarFactor (μ.map e) ν • ν :=
    isAddLeftInvariant_eq_smul _ _
  have hZ' : ν (e '' Z) = 0 := by
    apply (absolutelyContinuous_isAddHaarMeasure ν (μ.map e))
    change (μ.map em) (e '' Z) = 0
    rw [em.map_apply]
    simpa only [em,Homeomorph.toMeasurableEquiv_coe,ContinuousLinearEquiv.coe_toHomeomorph,
      e.injective.preimage_image] using hZ
  let Oe := e.symm ⁻¹' O
  have hOe : IsOpen Oe := hO.preimage e.symm.continuous
  have hKe : IsCompact (e '' K) := hK.image e.continuous
  have hKeO : e '' K ⊆ Oe := by
    rintro _ ⟨x,hx,rfl⟩
    simpa only [Oe,mem_preimage,e.symm_apply_apply] using hKO hx
  obtain ⟨U,hU,hKU,hUO⟩ := hKe.exists_isOpen_closure_subset (hOe.mem_nhdsSet.mpr hKeO)
  have hUO' : U ⊆ Oe := subset_closure.trans hUO
  let D := fun n y => (Φ' n (e.symm y)).comp e.symm.toContinuousLinearMap
  let D₀ := fun y => (φ' (e.symm y)).comp e.symm.toContinuousLinearMap
  let precomp : (E →L[ℝ] P) →L[ℝ] ((P × Q) →L[ℝ] P) :=
    (ContinuousLinearMap.compL ℝ (P × Q) E P).flip e.symm.toContinuousLinearMap
  have hd : ∀ n, ∀ y ∈ U, HasFDerivAt (fun y => Φ n (e.symm y)) (D n y) y := by
    intro n y hy
    exact (hder n (e.symm y) (hUO' hy)).comp y e.symm.hasFDerivAt
  have hc : ∀ y ∈ U, ContinuousAt D₀ y := by
    intro y hy
    exact precomp.continuous.continuousAt.comp
      ((hcont (e.symm y) (hUO' hy)).comp e.symm.continuousAt)
  have hr : ∀ y ∈ e '' K \ e '' Z, Surjective (D₀ y) := by
    rintro y ⟨⟨x,hx,rfl⟩,hz⟩
    have hxn : x ∉ Z := fun h => hz ⟨x,h,rfl⟩
    intro w
    obtain ⟨z,hz⟩ := hreg x ⟨hx,hxn⟩ w
    refine ⟨e z,?_⟩
    change φ' (e.symm (e x)) (e.symm (e z)) = w
    simpa only [e.symm_apply_apply] using hz
  have hv : ∀ y ∈ U, ∀ r > 0, ball y r ⊆ U →
      TendstoUniformlyOn D D₀ atTop (ball y r) := by
    intro y hy r hr hball
    have hclosed : closedBall y r ⊆ Oe := by
      rw [← closure_ball y hr.ne']
      exact (closure_mono hball).trans hUO
    let C := e.symm '' closedBall y r
    have hC : IsCompact C := (isCompact_closedBall y r).image e.symm.continuous
    have hCO : C ⊆ O := by
      rintro _ ⟨z,hz,rfl⟩
      exact hclosed hz
    have hv₁ := (hconv C hC hCO).comp e.symm
    have hv₂ := precomp.uniformContinuous.comp_tendstoUniformlyOn hv₁
    exact hv₂.mono (fun z hz => ⟨z,ball_subset_closedBall hz,rfl⟩)
  have ht := compact_surjective_pullback_zero hU hKe hKU hZ' hd hc hr hv
    hB hM hg (fun n y hy => hρ n (e.symm y) (hUO' hy)) hgM hL
  have hscale := ENNReal.Tendsto.const_mul
    (a := (addHaarScalarFactor (μ.map e) ν : ℝ≥0∞)) ht (Or.inr ENNReal.coe_ne_top)
  simp only [mul_zero] at hscale
  convert hscale using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  have heq := em.restrict_map μ (e '' K)
  have hi := lintegral_map_equiv
    (fun y => ρ n (e.symm y)*g n (Φ n (e.symm y))) em
    (μ := μ.restrict (em ⁻¹' (e '' K)))
  rw [← heq] at hi
  simp only [em,Homeomorph.toMeasurableEquiv_coe,ContinuousLinearEquiv.coe_toHomeomorph] at hi
  rw [hmap,Measure.restrict_smul,lintegral_smul_measure] at hi
  simpa only [e.injective.preimage_image,e.symm_apply_apply,ENNReal.smul_def,smul_eq_mul,ν] using hi.symm

end BoltzmannNonuniqueness.GainPullback

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ThermalPointBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for the actual thermal core velocity parameters -/

noncomputable section

open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermalPoint_transverse (α γ s d t : ℝ) (color : Bool)
    (x : JetPrototype.Space) (w : FiveGainMap.V) :
    transverse (thermalPoint α γ s d t color x w) = d • transverse (WithLp.toLp 2 w) := by
  simp only [thermalPoint,thermalCoordinates_apply,JetCoreMeasure.velocityMap,PlaneChart.transverse_join]

theorem thermalPoint_axial (α γ s d t : ℝ) (color : Bool)
    (x : JetPrototype.Space) (w : FiveGainMap.V) :
    axial (thermalPoint α γ s d t color x w) =
      JetCoreMap.axialMap (JetPrototype.sign color) α γ s d t x.2 (w 2) := by
  simp only [thermalPoint,thermalCoordinates_apply,JetCoreMeasure.velocityMap,PlaneChart.axial_join]
  rfl

theorem thermalPoint_transverse_bound {d : ℝ} (hd : 0 ≤ d)
    (α γ s t : ℝ) (color : Bool) (x : JetPrototype.Space) (w : FiveGainMap.V)
    (hw : ‖WithLp.toLp 2 w‖ ≤ 1) :
    ‖transverse (thermalPoint α γ s d t color x w)‖ ≤ d := by
  rw [thermalPoint_transverse,norm_smul,Real.norm_eq_abs,abs_of_nonneg hd]
  have ht := (LargeOutput.transverse_norm_le (WithLp.toLp 2 w)).trans hw
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ht hd

theorem thermalPoint_axial_bound {α d : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d)
    (γ s t : ℝ) (color : Bool) (x : JetPrototype.Space) (w : FiveGainMap.V)
    (hw : ‖WithLp.toLp 2 w‖ ≤ 1) :
    |axial (thermalPoint α γ s d t color x w)| ≤ d+1+α := by
  rw [thermalPoint_axial,JetCoreMap.axialMap]
  have ha : |w 2| ≤ 1 := (SmallInputGeometry.abs_axial_le_norm (WithLp.toLp 2 w)).trans hw
  have hu := AxialTransport.velocity_abs_le (σ := JetPrototype.sign color)
    (γ := γ) (s := s) (t := t) (z := x.2-t*d*(w 2)) hα
  have hsign : |JetPrototype.sign color| = 1 := by cases color <;> norm_num [JetPrototype.sign]
  rw [hsign] at hu
  calc
    _ ≤ |d*(w 2)|+|AxialFlow.velocity (JetPrototype.sign color) α γ s t (x.2-t*d*(w 2))| :=
      abs_add_le _ _
    _ ≤ d+(1+α) := add_le_add (by rw [abs_mul,abs_of_nonneg hd]; nlinarith) hu
    _ = _ := by ring

theorem thermalPoint_norm_bound {α d : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d) (hdmax : d ≤ 1)
    (γ s t : ℝ) (color : Bool) (x : JetPrototype.Space) (w : FiveGainMap.V)
    (hw : ‖WithLp.toLp 2 w‖ ≤ 1) :
    ‖thermalPoint α γ s d t color x w‖ ≤ α+3 := by
  have ht := thermalPoint_transverse_bound hd α γ s t color x w hw
  have ha := thermalPoint_axial_bound hα hd γ s t color x w hw
  have he := norm_sq_split (thermalPoint α γ s d t color x w)
  have ht0 := norm_nonneg (transverse (thermalPoint α γ s d t color x w))
  have ha0 := abs_nonneg (axial (thermalPoint α γ s d t color x w))
  have hn0 := norm_nonneg (thermalPoint α γ s d t color x w)
  have hts : ‖transverse (thermalPoint α γ s d t color x w)‖^2 ≤ d^2 := by nlinarith
  have has : (axial (thermalPoint α γ s d t color x w))^2 ≤ (d+1+α)^2 := by
    nlinarith [sq_abs (axial (thermalPoint α γ s d t color x w))]
  nlinarith

end BoltzmannNonuniqueness.JetCoreDensity

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RedundantParameterSupport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The redundant coordinates recover the actual graph-chart velocity -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix ENNReal RealInnerProductSpace
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart
open BoltzmannNonuniqueness.TransverseLine
open BoltzmannNonuniqueness.TransverseAverage

namespace BoltzmannNonuniqueness.RedundantPlane

theorem normal_norm_sq (v p : Velocity) :
    ‖normal v p‖^2 = normalVector v p 0^2+normalVector v p 1^2 := by
  simp [normal,normalVector,transverse,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_two]

theorem crossVelocity_on_plane (v p : Velocity) (L : V) :
    inner ℝ (v-p) (crossVelocity v p L) = 0 := by
  simp [crossVelocity,normalVector,PiLp.inner_apply,Fin.sum_univ_succ,cross_apply]
  ring

theorem crossVelocity_axial (v p : Velocity) (L : V) :
    axial (crossVelocity v p L) = coordinates (normalVector v p) ‖normal v p‖ L 0 := by
  simp [crossVelocity,axial,coordinates_apply,cross_apply]

theorem crossVelocity_tangent (v p : Velocity) (L : V) :
    inner ℝ (quarterTurn (direction (normal v p))) (transverse (crossVelocity v p L)) =
      coordinates (normalVector v p) ‖normal v p‖ L 1 := by
  simp [crossVelocity,normalVector,normal,transverse,quarterTurn,direction,
    PiLp.inner_apply,Fin.sum_univ_two,coordinates_apply,cross_apply]
  ring

theorem chart_crossVelocity (v p : Velocity) (hn : normal v p ≠ 0) (L : V) :
    chart v p (coordinates (normalVector v p) ‖normal v p‖ L 0)
      (coordinates (normalVector v p) ‖normal v p‖ L 1+tangentOffset v p) =
      v+crossVelocity v p L := by
  have hp := chart_recovers v p (v+crossVelocity v p L) hn (by
    simpa only [add_sub_cancel_left] using crossVelocity_on_plane v p L)
  have ha : axial (v+crossVelocity v p L)-axial v =
      coordinates (normalVector v p) ‖normal v p‖ L 0 := by
    change (v 2+crossVelocity v p L 2)-v 2 = _
    rw [add_sub_cancel_left]
    exact crossVelocity_axial v p L
  have ht : inner ℝ (quarterTurn (direction (normal v p)))
      (transverse (v+crossVelocity v p L)) =
      coordinates (normalVector v p) ‖normal v p‖ L 1+tangentOffset v p := by
    have he : transverse (v+crossVelocity v p L) =
        transverse v+transverse (crossVelocity v p L) := rfl
    rw [he,inner_add_right,crossVelocity_tangent,tangentOffset,add_comm]
  rwa [ha,ht] at hp

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # The actual Carleman chart integral in redundant plane parameters

The probability density in the redundant normal coordinate is arbitrary.
It can later be chosen bounded with compact support. No regularity of the
normal as a function of preceding collision parameters is required here.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.RedundantPlane

attribute [local irreducible] PlaneChart.chart

theorem chart_integral_redundant (v p : Velocity) (hn : normal v p ≠ 0)
    {ζ : ℝ → ℝ≥0∞} (hζ : Measurable ζ) (hζone : ∫⁻ u, ζ u = 1)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    ENNReal.ofReal (‖normal v p‖⁻¹) *
      (∫⁻ z : ℝ, ∫⁻ s : ℝ, f (chart v p z s)) =
    ∫⁻ L : V, ζ (coordinates (normalVector v p) ‖normal v p‖ L 2) *
      f (v+crossVelocity v p L) := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun zs =>
    f (chart v p zs.1 (zs.2+tangentOffset v p))
  let k : ℝ × ℝ → ChartKernel.Coordinates := fun zs => (p,zs)
  have hk : Measurable k := measurable_const.prodMk measurable_id
  have hchart : Measurable (fun zs : ℝ × ℝ => chart v p zs.1 zs.2) := by
    simpa only [Function.comp_def,k] using (ChartKernel.measurable_point v).comp hk
  have hF : Measurable F := hf.comp (hchart.comp
    (measurable_fst.prodMk (measurable_snd.add_const _)))
  have hi := redundant_coordinates_integral (norm_pos_iff.mpr hn) (normal_norm_sq v p)
    hζ hζone hF
  have hr : (∫⁻ z : ℝ, ∫⁻ s : ℝ, F (z,s)) =
      ∫⁻ z : ℝ, ∫⁻ s : ℝ, f (chart v p z s) := by
    apply lintegral_congr
    intro z
    exact lintegral_add_right_eq_self (fun s => f (chart v p z s)) (tangentOffset v p)
  rw [hr] at hi
  simpa only [F,chart_crossVelocity v p hn] using hi.symm

theorem gain_redundant (c : Measure Velocity) (v : Velocity)
    (hc : ∀ᵐ p ∂c, normal v p ≠ 0)
    {ζ : ℝ → ℝ≥0∞} (hζ : Measurable ζ) (hζone : ∫⁻ u, ζ u = 1)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    chartGain c f v = 2 * ∫⁻ p, ∫⁻ L : V,
      ζ (coordinates (normalVector v p) ‖normal v p‖ L 2) *
        f (v+crossVelocity v p L) ∂volume ∂c := by
  unfold chartGain
  congr 1
  apply lintegral_congr_ae
  filter_upwards [hc] with p hp
  exact chart_integral_redundant v p hp hζ hζone hf

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Redundant parameters for the normalized positive collision kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.RedundantPlane

theorem measurable_redundant_point (v : Velocity) :
    Measurable (fun q : Velocity × V => v+crossVelocity v q.1 q.2) := by
  unfold crossVelocity normalVector
  apply measurable_const.add
  apply (MeasurableEquiv.toLp 2 V).measurable.comp
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [cross_apply] <;> fun_prop

theorem measurable_normalCoefficient (v : Velocity) :
    Measurable (fun q : Velocity × V => normalCoefficient v q.1 q.2) := by
  unfold normalCoefficient normSq normalVector
  simp only [Matrix.vec3_dotProduct]
  fun_prop

theorem ae_normal_ne (v : Velocity) : ∀ᵐ p ∂volume, normal v p ≠ 0 := by
  have h := (MeasureTheory.QuasiMeasurePreserving.snd
    split_measurePreserving.quasiMeasurePreserving).ae (volume.ae_ne (transverse v))
  have ht : ∀ᵐ p ∂volume, transverse p ≠ transverse v := by
    simpa only [split_apply] using h
  filter_upwards [ht] with p hp
  rw [normal,transverse_sub,sub_ne_zero]
  exact Ne.symm hp

theorem inputKernel_redundant {X : Type*} [MeasurableSpace X]
    (c : Kernel X Velocity) [IsSFiniteKernel c] (q : ℝ) (z : X × Velocity)
    (hc : ∀ᵐ p ∂c z.1, normal z.2 p ≠ 0)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂ChartKernel.inputKernel c q z) =
      2 * ∫⁻ p, ∫⁻ L : V, normalDensity (normalCoefficient z.2 p L) *
        (ENNReal.ofReal (H q (z.2+crossVelocity z.2 p L)/H q z.2)*
          f (z.2+crossVelocity z.2 p L)) ∂volume ∂c z.1 := by
  rw [ChartKernel.lintegral_inputKernel_eq_gain c q z hf]
  have hw : Measurable (fun ξ => ENNReal.ofReal (H q ξ/H q z.2)*f ξ) :=
    (((ChartKernel.measurable_H q).div_const _).ennreal_ofReal).mul hf
  simpa only [coordinates_last,normalCoefficient] using
    gain_redundant (c z.1) z.2 hc measurable_normalDensity lintegral_normalDensity hw

end BoltzmannNonuniqueness.RedundantPlane

end

end

section

/-! # Compact support of redundant plane parameters on retained collision paths -/

noncomputable section

open MeasureTheory
open scoped ENNReal Matrix
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.RedundantPlane

theorem normSq_eq_norm_sq (L : V) : normSq L = ‖WithLp.toLp 2 L‖^2 := by
  simp [normSq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
  ring

theorem plane_parameter_sq_bound {δ Vmax P : ℝ} (hδ : 0 < δ)
    (hV : 0 ≤ Vmax) (hP : 0 ≤ P) (v p : Velocity) (L : V)
    (hv : ‖v‖ ≤ Vmax) (hp : ‖p‖ ≤ P) (hlow : δ ≤ ‖v-p‖)
    (hout : ‖v+crossVelocity v p L‖ ≤ Vmax)
    (hρ : normalDensity (normalCoefficient v p L) ≠ 0) :
    ‖WithLp.toLp 2 L‖^2 ≤ (2*Vmax)^2/δ^2+(Vmax+P)^2 := by
  have hn : ‖v-p‖ ≤ Vmax+P := (norm_sub_le v p).trans (add_le_add hv hp)
  have hk : ‖crossVelocity v p L‖ ≤ 2*Vmax := by
    calc
      _ = ‖(v+crossVelocity v p L)-v‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖v+crossVelocity v p L‖+‖v‖ := norm_sub_le _ _
      _ ≤ 2*Vmax := by linarith
  have hcoef := normalDensity_support hρ
  have hc : |coordinates (normalVector v p) 1 L 2| ≤ 1 := by
    rw [coordinates_last]
    change |normalCoefficient v p L| ≤ 1
    exact abs_le.mpr ⟨by linarith [hcoef.1],hcoef.2⟩
  have hnorm : normSq (normalVector v p) = ‖v-p‖^2 := normSq_eq_norm_sq _
  have hcross : normSq (normalVector v p ⨯₃ L) = ‖crossVelocity v p L‖^2 := normSq_eq_norm_sq _
  have hl : δ^2 ≤ normSq (normalVector v p) := by
    rw [hnorm]
    nlinarith [norm_nonneg (v-p)]
  have hh : normSq (normalVector v p) ≤ (Vmax+P)^2 := by
    rw [hnorm]
    nlinarith [norm_nonneg (v-p)]
  have hk' : normSq (normalVector v p ⨯₃ L) ≤ (2*Vmax)^2 := by
    rw [hcross]
    nlinarith [norm_nonneg (crossVelocity v p L)]
  rw [← normSq_eq_norm_sq]
  exact normSq_parameter_bound hδ hl hh hk' hc

theorem plane_parameter_bound {δ Vmax P : ℝ} (hδ : 0 < δ)
    (hV : 0 ≤ Vmax) (hP : 0 ≤ P) (v p : Velocity) (L : V)
    (hv : ‖v‖ ≤ Vmax) (hp : ‖p‖ ≤ P) (hlow : δ ≤ ‖v-p‖)
    (hout : ‖v+crossVelocity v p L‖ ≤ Vmax)
    (hρ : normalDensity (normalCoefficient v p L) ≠ 0) :
    ‖WithLp.toLp 2 L‖ ≤ (2*Vmax)^2/δ^2+(Vmax+P)^2+1 := by
  have h := plane_parameter_sq_bound hδ hV hP v p L hv hp hlow hout hρ
  have hn := norm_nonneg (WithLp.toLp 2 L)
  nlinarith [sq_nonneg (‖WithLp.toLp 2 L‖-1)]

end BoltzmannNonuniqueness.RedundantPlane

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_CoreParameterStep
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual free-core normalized gain as a six-parameter integral -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.RedundantPlane
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem normalizedCoreKernel_parameter_integral {α γ s d t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (η K q : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂normalizedCoreKernel η K α γ s d q a ((t,x),v)) =
      ∫⁻ w : FiveGainMap.V, ∫⁻ L : FiveGainMap.V,
        parameterDensity η K α γ s d t q a x v w L *
          f (parameterPoint α γ s d t a x v w L) := by
  let F : Velocity × FiveGainMap.V → ℝ≥0∞ := fun p =>
    normalDensity (normalCoefficient v p.1 p.2) *
      (ENNReal.ofReal (H q (v+crossVelocity v p.1 p.2)/H q v)*
        f (v+crossVelocity v p.1 p.2))
  have hpoint := measurable_redundant_point v
  have hF : Measurable F :=
    (measurable_normalDensity.comp (measurable_normalCoefficient v)).mul
      (((((ChartKernel.measurable_H q).comp hpoint).div_const _).ennreal_ofReal).mul
        (hf.comp hpoint))
  have houter : Measurable (fun p : Velocity => ∫⁻ L : FiveGainMap.V, F (p,L)) :=
    hF.lintegral_prod_right
  have hc : ∀ᵐ p ∂coreKernel η K α γ s d a (t,x), PlaneChart.normal v p ≠ 0 := by
    rw [coreKernel_apply]
    exact (withDensity_absolutelyContinuous volume _).ae_le (ae_normal_ne v)
  have hg := inputKernel_redundant (coreKernel η K α γ s d a) q ((t,x),v) hc hf
  change (∫⁻ ξ, f ξ ∂normalizedCoreKernel η K α γ s d q a ((t,x),v)) =
    2 * ∫⁻ p, ∫⁻ L : FiveGainMap.V, F (p,L) ∂volume ∂coreKernel η K α γ s d a (t,x) at hg
  rw [hg,coreKernel_apply,core_thermal_integral hα hγ hs hd ht η K a x houter,
    ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  apply lintegral_congr
  intro w
  rw [← mul_assoc,← lintegral_const_mul' _ _
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)]
  apply lintegral_congr
  intro L
  dsimp only [F,parameterDensity,parameterPoint]
  ac_rfl

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # The parameterized gain and its thermal collision map -/

noncomputable section

open scoped Matrix
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem parameterPoint_eq_center (α γ s d t : ℝ) (a : Bool)
    (x : JetPrototype.Space) (xv : FiveGainMap.V) (hx : xv 2 = x.2)
    (v : Velocity) (w L : FiveGainMap.V) :
    WithLp.ofLp (parameterPoint α γ s d t a x v w L) =
      WithLp.ofLp v + (WithLp.ofLp v-
        FiveGainMap.thermalCenter (JetPrototype.sign a) α γ s d t xv w) ⨯₃ L := by
  unfold parameterPoint RedundantPlane.crossVelocity RedundantPlane.normalVector
  rw [thermalPoint_eq_center α γ s d t a x xv w hx]
  rfl

theorem thermalStep_eq_parameterPoint (α γ s d t : ℝ) (a : Bool)
    (L w : FiveGainMap.V) (z : FiveGainMap.State) :
    FiveGainMap.thermalStep (JetPrototype.sign a) α γ s d t L w z =
      (t,z.2.1-(z.1-t) • z.2.2,
        WithLp.ofLp (parameterPoint α γ s d t a
          (jetPosition (z.2.1-(z.1-t) • z.2.2)) (WithLp.toLp 2 z.2.2) w L)) := by
  rw [parameterPoint_eq_center α γ s d t a _ (z.2.1-(z.1-t) • z.2.2) rfl]
  rfl

theorem parameterPoint_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t)
    (d : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity) (w L : FiveGainMap.V) :
    parameterPoint α γ (r*s) d (r*t) a (r • x) v w L =
      parameterPoint α γ s d t a x v w L := by
  have hp : thermalPoint α γ (r*s) d (r*t) a (r • x) w =
      thermalPoint α γ s d t a x w :=
    JetCoreMeasure.velocityMap_dilation hr hα hγ hs ht (JetPrototype.sign a) d x.2
      (thermalCoordinates w)
  simp only [parameterPoint,hp]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RescaledParameterSlab
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The physical dilated gain in bounded thermal and plane parameters -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.RedundantPlane
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem rescaledCoreMeasure_parameter_integral {r α γ μ d t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hd : 0 < d) (ht : 0 ≤ t)
    (η K q : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity)
    (hv : transverse v ≠ 0) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂rescaledCoreMeasure r η K α γ μ d q a t x v) =
      ∫⁻ w : FiveGainMap.V, ∫⁻ L : FiveGainMap.V,
        rescaledParameterDensity r η K α γ μ d t q a x v w L *
          f (parameterPoint α γ μ d t a x v w L) := by
  rw [rescaledCoreMeasure,ChartKernel.offAxis_apply _ _ hv,lintegral_smul_measure]
  rw [normalizedCoreKernel_parameter_integral hα hγ (mul_pos hr hμ) hd (mul_nonneg hr.le ht)
    η K q a (r • x) v hf]
  simp only [smul_eq_mul]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro w
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro L
  rw [parameterPoint_dilation hr hα hγ hμ ht]
  exact (mul_assoc _ _ _).symm

theorem rescaledParameterDensity_bound {r K α γ μ t q b V : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ)
    (ht : 0 ≤ t) (hq : 0 ≤ q) (hb : 0 < b) (hV : 0 ≤ V)
    (η d : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity) (w L : FiveGainMap.V)
    (hv : ‖v‖ ≤ V) (hξ : b ≤ ‖transverse (parameterPoint α γ μ d t a x v w L)‖) :
    rescaledParameterDensity r η K α γ μ d t q a x v w L ≤
      2 * ENNReal.ofReal (((K*max 1 (α*γ)⁻¹)/(μ+t))*JetThermalKernel.bound) *
        ENNReal.ofReal ((1+b^(-q))/compactLower V) := by
  unfold rescaledParameterDensity parameterDensity
  rw [parameterPoint_dilation hr hα.le hγ.le hμ ht]
  have hw : ENNReal.ofReal r*ENNReal.ofReal
      (thermalWeight η K α γ (r*μ) d (r*t) a (r • x) w) ≤
      ENNReal.ofReal (((K*max 1 (α*γ)⁻¹)/(μ+t))*JetThermalKernel.bound) := by
    rw [← ENNReal.ofReal_mul hr.le]
    exact ENNReal.ofReal_le_ofReal (dilated_thermalWeight_bound hr hK hα hγ hμ ht η d a x w)
  have hn := normalDensity_le_one
    (normalCoefficient v (thermalPoint α γ (r*μ) d (r*t) a (r • x) w) L)
  have hratio := ENNReal.ofReal_le_ofReal (H_ratio_le_offAxis hq hb hV hv hξ)
  calc
    _ = (2*(ENNReal.ofReal r*ENNReal.ofReal
        (thermalWeight η K α γ (r*μ) d (r*t) a (r • x) w))) *
        normalDensity (normalCoefficient v (thermalPoint α γ (r*μ) d (r*t) a (r • x) w) L) *
        ENNReal.ofReal (H q (parameterPoint α γ μ d t a x v w L)/H q v) := by ac_rfl
    _ ≤ (2*ENNReal.ofReal (((K*max 1 (α*γ)⁻¹)/(μ+t))*JetThermalKernel.bound))*1*
        ENNReal.ofReal ((1+b^(-q))/compactLower V) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hw) hn) hratio
    _ = _ := by rw [mul_one]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Uniform compact parameter support for retained physical collisions -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreDensity
open BoltzmannNonuniqueness.RedundantPlane

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem rescaledParameterDensity_support {r α γ μ d t b Vmax : ℝ}
    (hr : 0 < r) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hd : 0 < d) (hdmax : d ≤ 1) (hb : 0 < b) (hthin : d ≤ b/2) (hV : 0 ≤ Vmax)
    (η K q : ℝ) (color : Bool) (x : JetPrototype.Space) (v : Velocity)
    (w L : FiveGainMap.V) (hv : ‖v‖ ≤ Vmax) (hvtrans : b ≤ ‖transverse v‖)
    (hout : ‖parameterPoint α γ μ d t color x v w L‖ ≤ Vmax)
    (hnonzero : rescaledParameterDensity r η K α γ μ d t q color x v w L ≠ 0) :
    ‖WithLp.toLp 2 w‖ < 1 ∧ ‖WithLp.toLp 2 L‖ ≤ retainedPlaneBound α b Vmax := by
  let p := thermalPoint α γ (r*μ) d (r*t) color (r • x) w
  have hw : ‖WithLp.toLp 2 w‖ < 1 := by
    by_contra h
    have hz := thermalWeight_zero (η := η) (K := K) (α := α) (γ := γ) (s := r*μ)
      (d := d) (t := r*t) color (r • x) (le_of_not_gt h)
    apply hnonzero
    simp only [rescaledParameterDensity,parameterDensity,hz,ENNReal.ofReal_zero,mul_zero,zero_mul]
  have hnormal : normalDensity (normalCoefficient v p L) ≠ 0 := by
    intro hz
    apply hnonzero
    change ENNReal.ofReal r*(2*ENNReal.ofReal _*normalDensity (normalCoefficient v p L)*_) = 0
    rw [hz,mul_zero,zero_mul,mul_zero]
  have hpt : ‖transverse p‖ ≤ d :=
    thermalPoint_transverse_bound hd.le α γ (r*μ) (r*t) color (r • x) w hw.le
  have hp : ‖p‖ ≤ α+3 := thermalPoint_norm_bound hα hd.le hdmax γ (r*μ) (r*t)
    color (r • x) w hw.le
  have hlow : b/2 ≤ ‖v-p‖ := by
    have hdiff := norm_sub_norm_le (transverse v) (transverse p)
    have htrans := LargeOutput.transverse_norm_le (v-p)
    rw [PlaneChart.transverse_sub] at htrans
    linarith
  have hout' : ‖v+crossVelocity v p L‖ ≤ Vmax := by
    have he := parameterPoint_dilation hr hα hγ hμ ht d color x v w L
    change parameterPoint α γ (r*μ) d (r*t) color (r • x) v w L = _ at he
    change ‖parameterPoint α γ (r*μ) d (r*t) color (r • x) v w L‖ ≤ Vmax
    rw [he]
    exact hout
  exact ⟨hw,plane_parameter_bound (half_pos hb) hV (by linarith) v p L hv hp hlow hout' hnormal⟩

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # A common bound for retained physical gain densities on a positive slab -/

noncomputable section

open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem parameterSlabBound_ne_top (K α γ q a b V : ℝ) :
    parameterSlabBound K α γ q a b V ≠ ∞ := by
  unfold parameterSlabBound
  finiteness

theorem rescaledParameterDensity_slab_bound {r K α γ μ t q a b V : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ)
    (ha : 0 < a) (ht : a ≤ t) (hq : 0 ≤ q) (hb : 0 < b) (hV : 0 ≤ V)
    (η d : ℝ) (sign : Bool) (x : JetPrototype.Space) (v : Velocity) (w L : FiveGainMap.V)
    (hv : ‖v‖ ≤ V) (hξ : b ≤ ‖transverse (parameterPoint α γ μ d t sign x v w L)‖) :
    rescaledParameterDensity r η K α γ μ d t q sign x v w L ≤
      parameterSlabBound K α γ q a b V := by
  apply (rescaledParameterDensity_bound hr hK hα hγ hμ (ha.le.trans ht) hq hb hV
    η d sign x v w L hv hξ).trans
  apply mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)) le_rfl
  apply mul_le_mul_of_nonneg_right _ JetThermalKernel.bound_pos.le
  exact div_le_div_of_nonneg_left
    (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha (by linarith)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_AnalyticRankAlmostEverywhere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # From one regular point to almost-everywhere rank, conditionally on scalar zero sets -/

noncomputable section

open MeasureTheory Set Function

namespace BoltzmannNonuniqueness.FiveGainMap

theorem analytic_rank_ae (hM : Published.Mityagin2020FiveGainParameters)
    {U : Set Parameters} (hU : IsOpen U) (hconn : IsPreconnected U)
    {Φ : Parameters → State} (ha : AnalyticOnNhd ℝ Φ U)
    {q₀ : Parameters} (hq₀ : q₀ ∈ U) (hrank : Surjective (fderiv ℝ Φ q₀)) :
    volume {q ∈ U | ¬Surjective (fderiv ℝ Φ q)} = 0 := by
  classical
  obtain ⟨R,hR⟩ := (fderiv ℝ Φ q₀).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hrank)
  let R' : State →L[ℝ] Parameters := R.toContinuousLinearMap
  let A : Parameters → State →L[ℝ] State := fun q => (fderiv ℝ Φ q).comp R'
  have hA : AnalyticOnNhd ℝ A U := by
    intro q hq
    exact (((ContinuousLinearMap.compL ℝ State Parameters State).flip R').analyticAt _).comp
      (ha q hq).fderiv
  have hA₀ : A q₀ = ContinuousLinearMap.id ℝ State := by
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.congr_fun hR v
  have hz := hM U hU hconn (fun q => (A q).toLinearMap.det)
    (fun q hq => determinant_analyticAt (hA q hq))
    ⟨q₀,hq₀,by rw [hA₀]; simp⟩
  apply measure_mono_null _ hz
  intro q hq
  refine ⟨hq.1,?_⟩
  by_contra hdet
  have hunit : IsUnit (A q).toLinearMap :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsur : Surjective (A q) := LinearMap.range_eq_top.mp
    ((LinearMap.isUnit_iff_range_eq_top _).mp hunit)
  apply hq.2
  intro v
  obtain ⟨w,hw⟩ := hsur v
  exact ⟨R' w,hw⟩

end BoltzmannNonuniqueness.FiveGainMap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_CoreJointParameterDensity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Joint measurability of the physical six-parameter collision density -/

noncomputable section

open MeasureTheory
open scoped Matrix ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.RedundantPlane

theorem joint_point_measurable : Measurable (fun p : (Velocity × Velocity) × V =>
    p.1.1+crossVelocity p.1.1 p.1.2 p.2) := by
  apply measurable_fst.fst.add
  apply (MeasurableEquiv.toLp 2 V).measurable.comp
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [normalVector,cross_apply] <;> fun_prop

theorem joint_normalCoefficient_measurable :
    Measurable (fun p : (Velocity × Velocity) × V => normalCoefficient p.1.1 p.1.2 p.2) := by
  unfold normalCoefficient normalVector normSq
  simp only [Matrix.vec3_dotProduct]
  fun_prop

end BoltzmannNonuniqueness.RedundantPlane

namespace BoltzmannNonuniqueness.JetCoreSheet

attribute [local irreducible] thermalPoint parameterPoint parameterDensity
  thermalWeight RedundantPlane.normalCoefficient RedundantPlane.normalDensity

private theorem arguments_measurable : Measurable (fun p : ParameterArguments =>
    ((p.1.1,p.1.2,p.2.2.1) : ThermalArguments)) := by fun_prop

theorem clamped_parameterPoint_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (d : ℝ) (color : Bool) :
    Measurable (fun p : ParameterArguments => parameterPoint α γ s d (max 0 p.1.1) color
      p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  have hc : Measurable (fun p : ParameterArguments =>
      thermalPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.2.1) :=
    (clamped_thermalPoint_measurable hα hγ hs d color).comp arguments_measurable
  unfold parameterPoint
  exact RedundantPlane.joint_point_measurable.comp
    ((measurable_snd.fst.prodMk hc).prodMk measurable_snd.snd.snd)

private theorem clamped_normalDensity_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (d : ℝ) (color : Bool) :
    Measurable (fun p : ParameterArguments => RedundantPlane.normalDensity
      (RedundantPlane.normalCoefficient p.2.1
        (thermalPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.2.1) p.2.2.2)) := by
  have hc : Measurable (fun p : ParameterArguments =>
      thermalPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.2.1) :=
    (clamped_thermalPoint_measurable hα hγ hs d color).comp arguments_measurable
  have harg : Measurable (fun p : ParameterArguments =>
      ((p.2.1,thermalPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.2.1),p.2.2.2)) :=
    (measurable_snd.fst.prodMk hc).prodMk measurable_snd.snd.snd
  apply RedundantPlane.measurable_normalDensity.comp
  exact RedundantPlane.joint_normalCoefficient_measurable.comp harg

private theorem clamped_ratio_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (d q : ℝ) (color : Bool) :
    Measurable (fun p : ParameterArguments => ENNReal.ofReal
      (H q (parameterPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.1 p.2.2.1 p.2.2.2)/H q p.2.1)) := by
  have hp := clamped_parameterPoint_measurable hα hγ hs d color
  have hnum : Measurable (fun p : ParameterArguments =>
      H q (parameterPoint α γ s d (max 0 p.1.1) color p.1.2 p.2.1 p.2.2.1 p.2.2.2)) :=
    (ChartKernel.measurable_H q).comp hp
  have hden : Measurable (fun p : ParameterArguments => H q p.2.1) :=
    (ChartKernel.measurable_H q).comp measurable_snd.fst
  exact (hnum.div hden).ennreal_ofReal

theorem clamped_parameterDensity_measurable {α γ s : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (η K d q : ℝ) (color : Bool) :
    Measurable (fun p : ParameterArguments => parameterDensity η K α γ s d (max 0 p.1.1) q color
      p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  have hw : Measurable (fun p : ParameterArguments =>
      thermalWeight η K α γ s d (max 0 p.1.1) color p.1.2 p.2.2.1) :=
    (clamped_thermalWeight_measurable hα hγ hs η K d color).comp arguments_measurable
  have hn := clamped_normalDensity_measurable hα hγ hs d color
  have hr := clamped_ratio_measurable hα hγ hs d q color
  unfold parameterDensity
  exact ((measurable_const.mul hw.ennreal_ofReal).mul hn).mul hr

theorem clamped_rescaledParameterDensity_measurable {r α γ μ : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (η K d q : ℝ) (color : Bool) :
    Measurable (fun p : ParameterArguments =>
      rescaledParameterDensity r η K α γ μ d (max 0 p.1.1) q color
        p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  have h := (clamped_parameterDensity_measurable hα hγ (mul_pos hr hμ) η K d q color).comp
    (show Measurable (fun p : ParameterArguments => ((r*p.1.1,r • p.1.2),p.2)) by fun_prop)
  have hm (t : ℝ) : max 0 (r*t) = r*max 0 t := by
    rw [mul_max_of_nonneg _ _ hr.le,mul_zero]
  unfold rescaledParameterDensity
  apply measurable_const.mul
  simpa only [Function.comp_def,hm] using h

end BoltzmannNonuniqueness.JetCoreSheet

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FiveGainPullback
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Rank seven of the actual map at the explicit collision witness -/

noncomputable section

open Matrix Function
open scoped Matrix
open BoltzmannNonuniqueness.FiveGainWitness

namespace BoltzmannNonuniqueness.FiveGainMap

theorem rank_at_witness {R : ℝ} (hR : 0 < R) {α γ τ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hτ : 0 < τ)
    (σ s : Fin 5 → ℝ) (hs : ∀ i, 0 < s i) (t₀ z : ℝ) (x₀ : V) :
    let endpoint : State := (t₀,x₀,![R,0,z])
    let a := equalTimeSpeeds σ s α γ τ endpoint
    let q : Parameters := ((fun _ => τ),witnessAngles R z a)
    Surjective (fderiv ℝ (map σ s α γ endpoint) q) := by
  dsimp only
  let endpoint : State := (t₀,x₀,![R,0,z])
  let a := equalTimeSpeeds σ s α γ τ endpoint
  let L := witnessAngles R z a
  let q : Parameters := ((fun _ => τ),L)
  let T := fderiv ℝ (map σ s α γ endpoint) q
  change Surjective T
  have heq : ∀ i, q.1 i = τ := fun _ => rfl
  have hpos (c : V) : (T (firstTimeDirection c)).2.1 = witnessPosition R (z-a 2) c := by
    change (fderiv ℝ (map σ s α γ endpoint) q (firstTimeDirection c)).2.1 = _
    rw [map_derivative_position hα hγ hs hτ endpoint q _ heq]
    have hp (i : Fin 4) : (path σ s α γ endpoint q (i.val+1)).2.2 =
        witnessVelocities R z (z-a 2) ⟨i.val+1,by omega⟩ := by
      have h := congrArg (fun u : State => u.2.2)
        (path_equal_time σ s α γ τ endpoint L (k := i.val+1) (by omega) (by omega))
      exact h.trans (witness_velocityPath hR z a (i.val+1) (by omega))
    simp_rw [hp]
    exact positionDirection_at_witness R z a c
  have hw₃ : velocityPath a L endpoint.2.2 3 = witnessVelocities R z (z-a 2) 3 :=
    witness_velocityPath hR z a 3 (by decide)
  have hw₄ : velocityStep (a 3) (L 3) (velocityPath a L endpoint.2.2 3) =
      witnessVelocities R z (z-a 2) 4 := by
    exact witness_velocityPath hR z a 4 (by decide)
  have hang (A B : V) : (T (lastAngularDirection A B)).2.2 =
      (witnessVelocities R z (z-a 2) 3-axis (a 3)) ⨯₃ A+
      (witnessVelocities R z (z-a 2) 4-axis (a 4)) ⨯₃ B := by
    have h := map_derivative_last_angular (σ := σ) hα hγ hs hτ endpoint L
      (witnessAngles_last R z a) A B
    change (T (lastAngularDirection A B)).2.2 =
      (velocityPath a L endpoint.2.2 3-axis (a 3)) ⨯₃ A+
      (velocityStep (a 3) (L 3) (velocityPath a L endpoint.2.2 3)-axis (a 4)) ⨯₃ B at h
    rwa [hw₄,hw₃] at h
  apply surjective_of_blocks T
  · intro d
    exact map_derivative_time hα hγ hs endpoint q d (fun _ => hτ)
  · intro x
    obtain ⟨c,hc⟩ := witnessPosition_surjective R (z-a 2) x
    exact ⟨c,(hpos c).trans hc⟩
  · intro A B
    change (fderiv ℝ (map σ s α γ endpoint) q (lastAngularDirection A B)).2.1 = 0
    rw [map_derivative_position hα hγ hs hτ endpoint q _ heq]
    simp [positionDirection,lastAngularDirection]
  · intro v
    have hsur := final_angular_surjective R (z-a 2)
      (z+smallFactor R (z-a 2)*transverseSquare R-a 3)
      (z+smallFactor R (z-a 2)*transverseSquare R-a 4)
    obtain ⟨p,hp⟩ := hsur v
    refine ⟨p,(hang p.1 p.2).trans ?_⟩
    simpa [witnessVelocities,axis,Pi.sub_apply] using hp

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Transporting the rank witness to every nonaxial endpoint -/

noncomputable section

open Matrix Function
open scoped Matrix

namespace BoltzmannNonuniqueness.FiveGainMap

theorem rank_rotation {c s : ℝ} (hcs : c^2+s^2 = 1)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (z : State) (q : Parameters) (ht : q ∈ positiveDomain)
    (hrank : Surjective (fderiv ℝ (map σ μ α γ z) q)) :
    Surjective (fderiv ℝ (map σ μ α γ (rotateState c s z)) (rotateParameters c s q)) := by
  let P := rotateParameters c s
  let S := rotateState c s
  let D := fderiv ℝ (map σ μ α γ z) q
  let D' := fderiv ℝ (map σ μ α γ (S z)) (P q)
  have h₁ := ((map_analytic (σ := σ) hα hγ hμ (S z) (P q) ht).hasStrictFDerivAt.hasFDerivAt).comp q P.hasFDerivAt
  have h₂ := S.hasFDerivAt.comp q
    (map_analytic (σ := σ) hα hγ hμ z q ht).hasStrictFDerivAt.hasFDerivAt
  have he : (fun r => map σ μ α γ (S z) (P r)) =
      (fun r => S (map σ μ α γ z r)) := funext (map_rotation hcs σ μ α γ z)
  change HasFDerivAt (fun r => map σ μ α γ (S z) (P r)) (D'.comp P) q at h₁
  change HasFDerivAt (fun r => S (map σ μ α γ z r)) (S.comp D) q at h₂
  rw [he] at h₁
  have hD := h₁.unique h₂
  intro w
  obtain ⟨v,hv⟩ := rotateState_surjective hcs w
  obtain ⟨u,hu⟩ := hrank v
  refine ⟨P u,?_⟩
  have h := congrArg (fun L : Parameters →L[ℝ] State => L u) hD
  change D' (P u) = S (D u) at h
  exact h.trans (by rw [show D u = v from hu]; exact hv)

theorem exists_nonaxial_rank_point {σ μ : Fin 5 → ℝ} {α γ τ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : ∀ i, 0 < μ i) (hτ : 0 < τ)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2) :
    ∃ q : Parameters, (∀ i, q.1 i = τ) ∧ Surjective (fderiv ℝ (map σ μ α γ (t₀,x,v)) q) := by
  let R := Real.sqrt (v 0^2+v 1^2)
  have hR : 0 < R := Real.sqrt_pos.mpr hv
  have hR2 : R^2 = v 0^2+v 1^2 := Real.sq_sqrt hv.le
  let c := v 0/R
  let s := v 1/R
  have hcs : c^2+s^2 = 1 := by
    dsimp [c,s]
    field_simp
    nlinarith
  let z : State := (t₀,rotation c (-s) x,![R,0,v 2])
  have hz : rotateState c s z = (t₀,x,v) := by
    have hn : c^2+(-s)^2 = 1 := by simpa using hcs
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simpa only [z,rotateState_apply,neg_neg] using rotation_inverse hn x
    · ext i
      fin_cases i <;> simp [z,rotateState_apply,rotation_apply,c,s,ne_of_gt hR]
  let a := equalTimeSpeeds σ μ α γ τ z
  let q : Parameters := ((fun _ => τ),witnessAngles R (v 2) a)
  have hrank : Surjective (fderiv ℝ (map σ μ α γ z) q) :=
    rank_at_witness hR hα hγ hτ σ μ hμ t₀ (v 2) (rotation c (-s) x)
  refine ⟨rotateParameters c s q,(fun _ => rfl),?_⟩
  rw [← hz]
  exact rank_rotation hcs hα hγ hμ z q (fun _ => hτ) hrank

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Almost-everywhere rank of the actual five-gain map -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.FiveGainMap

theorem map_rank_ae (hM : Published.Mityagin2020FiveGainParameters)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2) :
    volume {q ∈ positiveDomain | ¬Function.Surjective
      (fderiv ℝ (map σ μ α γ (t₀,x,v)) q)} = 0 := by
  obtain ⟨q,hq,hrank⟩ := exists_nonaxial_rank_point hα hγ hμ (by norm_num : (0 : ℝ) < 1)
    t₀ x v hv
  apply analytic_rank_ae hM positiveDomain_open positiveDomain_preconnected
    (map_analyticOnNhd hα hγ hμ (t₀,x,v)) (q₀ := q) _ hrank
  intro i
  rw [hq]
  norm_num

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Exact derivative of the zero-width map, including spectator variables -/

noncomputable section

namespace BoltzmannNonuniqueness.FiveGainMap

theorem controlDerivative_zero_apply {σ s : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i)
    (z : State) (q : Parameters) (w : Fin 5 → V) (ht : ∀ i, 0 < q.1 i)
    (d : ThermalControls) :
    controlDerivative σ α γ ((s,0,z),(q,w)) d =
      fderiv ℝ (map σ s α γ z) q d.1 := by
  have hf := thermalControl_hasFDerivAt (σ := σ) hα hγ
    (⟨(s,0,z),hs⟩ : PositiveEnvironment) (q,w) ht
  have hg := ((map_analytic (σ := σ) hα hγ hs z q ht).hasStrictFDerivAt.hasFDerivAt).comp
    (q,w) (hasFDerivAt_fst (𝕜 := ℝ))
  have he : (fun u : ThermalControls => thermalMap σ α γ ((s,0,z),u)) =
      (fun u : ThermalControls => map σ s α γ z u.1) :=
    funext (fun u => thermalMap_zero σ s α γ z u.1 u.2)
  change HasFDerivAt (fun u : ThermalControls => thermalMap σ α γ ((s,0,z),u))
    (controlDerivative σ α γ ((s,0,z),(q,w))) (q,w) at hf
  change HasFDerivAt (fun u : ThermalControls => map σ s α γ z u.1)
    ((fderiv ℝ (map σ s α γ z) q).comp (ContinuousLinearMap.fst ℝ _ _)) (q,w) at hg
  rw [he] at hf
  exact congrArg (fun L : ThermalControls →L[ℝ] State => L d) (hf.unique hg)

theorem controlDerivative_zero_surjective {σ s : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ i, 0 < s i)
    (z : State) (q : Parameters) (w : Fin 5 → V) (ht : ∀ i, 0 < q.1 i)
    (hrank : Function.Surjective (fderiv ℝ (map σ s α γ z) q)) :
    Function.Surjective (controlDerivative σ α γ ((s,0,z),(q,w))) := by
  intro v
  obtain ⟨d,hd⟩ := hrank v
  refine ⟨(d,0),?_⟩
  rw [controlDerivative_zero_apply hα hγ hs z q w ht]
  exact hd

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The zero-width rank statement with all fifteen thermal spectator variables -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.FiveGainMap

theorem zeroWidth_rank_ae (hM : Published.Mityagin2020FiveGainParameters)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2) :
    ((volume : Measure Parameters).prod (volume : Measure (Fin 5 → V)))
      {p : ThermalControls | p.1 ∈ positiveDomain ∧ ¬Function.Surjective
        (controlDerivative σ α γ ((μ,0,(t₀,x,v)),p))} = 0 := by
  let Z := {q ∈ positiveDomain | ¬Function.Surjective
    (fderiv ℝ (map σ μ α γ (t₀,x,v)) q)}
  have hZ : (volume : Measure Parameters) Z = 0 :=
    map_rank_ae hM hα hγ hμ t₀ x v hv
  have hsub : {p : ThermalControls | p.1 ∈ positiveDomain ∧ ¬Function.Surjective
      (controlDerivative σ α γ ((μ,0,(t₀,x,v)),p))} ⊆ Z ×ˢ Set.univ := by
    intro p hp
    refine ⟨⟨hp.1,?_⟩,Set.mem_univ _⟩
    intro hq
    exact hp.2 (controlDerivative_zero_surjective hα hγ hμ (t₀,x,v) p.1 p.2 hp.1 hq)
  apply measure_mono_null hsub
  rw [Measure.prod_prod,hZ,zero_mul]

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Compact pullback convergence for the actual five thermal gains -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Filter Set Function
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.FiveGainMap

theorem controlDomain_open : IsOpen controlDomain :=
  positiveDomain_open.preimage continuous_fst

theorem controlDerivative_continuousAt {σ : Fin 5 → ℝ} {α γ : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (env : PositiveEnvironment)
    {q : ThermalControls} (hq : q ∈ controlDomain) :
    ContinuousAt (fun u => controlDerivative σ α γ (env.val,u)) q := by
  let precomp := (ContinuousLinearMap.compL ℝ ThermalControls ThermalInput State).flip
    (ContinuousLinearMap.inr ℝ ThermalEnvironment ThermalControls)
  have hd := (thermalMap_analytic (σ := σ) hα hγ (env.val,q) env.property hq).fderiv.continuousAt
  exact precomp.continuous.continuousAt.comp
    (hd.comp (f := fun u => (env.val,u)) (continuousAt_const.prodMk continuousAt_id))

/-- Uniformly bounded parameter densities pull local L1 errors back to zero
through the five thermal gains, at any nonaxial limiting endpoint. -/
theorem thermal_compact_pullback_zero (hMityagin : Published.Mityagin2020FiveGainParameters)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    {K : Set ThermalControls} (hK : IsCompact K) (hKT : K ⊆ controlDomain)
    {g : ℕ → State → ℝ≥0∞} {ρ : ℕ → ThermalControls → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n q, q ∈ controlDomain → ρ n q ≤ B) (hgM : ∀ n z, g n z ≤ M)
    (hL : Tendsto (fun n => ∫⁻ z, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q in K, ρ n q*g n (thermalMap σ α γ ((env n).val,q)))
      atTop (𝓝 0) := by
  have : IsAddHaarMeasure (volume : Measure (V × V)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have : IsAddHaarMeasure (volume : Measure State) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have : IsAddHaarMeasure (volume : Measure (Fin 5 → V)) :=
    Measure.pi.isAddHaarMeasure _
  have : IsAddHaarMeasure (volume : Measure Parameters) :=
    Measure.prod.instIsAddHaarMeasure _ _
  have : IsAddHaarMeasure (volume : Measure ThermalControls) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let env₀ : PositiveEnvironment := ⟨(μ,0,(t₀,x,v)),hμ⟩
  let Z := {q : ThermalControls | q ∈ controlDomain ∧
    ¬Surjective (controlDerivative σ α γ (env₀.val,q))}
  have hZ : (volume : Measure ThermalControls) Z = 0 :=
    zeroWidth_rank_ae hMityagin hα hγ hμ t₀ x v hv
  apply GainPullback.compact_pullback_zero_coordinates controlCoordinates
    controlDomain_open hK hKT hZ
    (fun n q hq => thermalControl_hasFDerivAt hα hγ (env n) q hq)
    (fun q hq => controlDerivative_continuousAt hα hγ env₀ hq)
    (φ' := fun q => controlDerivative σ α γ (env₀.val,q))
    (fun q hq => by
      by_contra hn
      exact hq.2 ⟨hKT hq.1,hn⟩)
    (fun C hC hCT => thermalDerivative_compact_tendsto hα hγ henv hC
      (fun q hq => hCT hq)) hB hM hg hρ hgM hL

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Local L1 smallness suffices for the five-gain pullback -/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] thermalMap

/-- Only the values on one fixed output ball enter a compact parameter integral. -/
theorem thermal_compact_pullback_zero_local
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    {K : Set ThermalControls} (hK : IsCompact K) (hKT : K ⊆ controlDomain)
    {g : ℕ → State → ℝ≥0∞} {ρ : ℕ → ThermalControls → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n q, q ∈ controlDomain → ρ n q ≤ B) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ R : ℝ, 0 < R → Tendsto
      (fun n => ∫⁻ z in closedBall (0 : State) R, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q in K, ρ n q*g n (thermalMap σ α γ ((env n).val,q)))
      atTop (𝓝 0) := by
  let env₀ : PositiveEnvironment := ⟨(μ,0,(t₀,x,v)),hμ⟩
  let φ₀ := fun q => thermalMap σ α γ (env₀.val,q)
  have hc : ContinuousOn φ₀ K := by
    intro q hq
    exact (thermalControl_hasFDerivAt (σ := σ) hα hγ env₀ q (hKT hq)).continuousAt.continuousWithinAt
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn hc
  let R' := max R 0+1
  have hR' : 0 < R' := by dsimp [R'] <;> positivity
  have hu := thermalMap_compact_tendsto (σ := σ) hα hγ henv hK
    (fun q hq => hKT hq)
  have himage : ∀ᶠ n in atTop, ∀ q ∈ K,
      thermalMap σ α γ ((env n).val,q) ∈ closedBall (0 : State) R' := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu 1 (by norm_num)] with n hn
    intro q hq
    rw [mem_closedBall,dist_zero_right]
    have hd : ‖thermalMap σ α γ ((env n).val,q)-φ₀ q‖ < 1 := by
      have hd := hn q hq
      change dist (φ₀ q) (thermalMap σ α γ ((env n).val,q)) < 1 at hd
      rwa [dist_eq_norm,norm_sub_rev] at hd
    have hr := hR q hq
    have ht := norm_add_le (thermalMap σ α γ ((env n).val,q)-φ₀ q) (φ₀ q)
    rw [sub_add_cancel] at ht
    exact ht.trans (by dsimp [R'] <;> linarith [le_max_left R 0])
  let g' := fun n => (closedBall (0 : State) R').indicator (g n)
  have hg' : ∀ n, Measurable (g' n) := fun n => (hg n).indicator isClosed_closedBall.measurableSet
  have hb' : ∀ n z, g' n z ≤ M := by
    intro n z
    exact (indicator_le_self _ _ z).trans (hgM n z)
  have hlim : Tendsto (fun n => ∫⁻ z, g' n z) atTop (𝓝 0) := by
    simpa only [g',lintegral_indicator isClosed_closedBall.measurableSet] using hL R' hR'
  have ht := thermal_compact_pullback_zero (σ := σ) hMityagin hα hγ hμ t₀ x v hv
    henv hK hKT hB hM hg' hρ hb' hlim
  apply ht.congr'
  filter_upwards [himage] with n hn
  apply setLIntegral_congr_fun hK.measurableSet
  intro q hq
  change ρ n q*g' n (thermalMap σ α γ ((env n).val,q)) =
    ρ n q*g n (thermalMap σ α γ ((env n).val,q))
  rw [show g' n (thermalMap σ α γ ((env n).val,q)) =
    g n (thermalMap σ α γ ((env n).val,q)) from indicator_of_mem (hn q hq) _]

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The five-gain output coordinates preserve physical kinetic volume -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.FiveGainMap

theorem toKinetic_apply (z : State) :
    toKinetic z = ((z.1,WithLp.toLp 2 z.2.1),WithLp.toLp 2 z.2.2) := rfl

theorem toKinetic_measurePreserving : MeasurePreserving toKinetic := by
  have hV := PiLp.volume_preserving_toLp (Fin 3)
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod (hV.prod hV)
  have hA := (measurePreserving_prodAssoc (volume : Measure ℝ)
    (volume : Measure Published.Velocity) (volume : Measure Published.Velocity)).symm
  exact h.trans hA

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The five-gain pullback applied to physical kinetic densities -/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.FiveGainMap

theorem toKinetic_continuous : Continuous toKinetic := by
  change Continuous (fun z : State =>
    ((z.1,WithLp.toLp 2 z.2.1),WithLp.toLp 2 z.2.2))
  exact (continuous_fst.prodMk ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
    continuous_snd.fst)).prodMk ((PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
      continuous_snd.snd)

theorem thermal_compact_pullback_zero_physical
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {σ μ : Fin 5 → ℝ} {α γ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hμ : ∀ i, 0 < μ i) (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    {K : Set ThermalControls} (hK : IsCompact K) (hKT : K ⊆ controlDomain)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞}
    {ρ : ℕ → ThermalControls → ℝ≥0∞} {B M : ℝ≥0∞}
    (hB : B ≠ ∞) (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n))
    (hρ : ∀ n q, q ∈ controlDomain → ρ n q ≤ B) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q in K,
      ρ n q*g n (toKinetic (thermalMap σ α γ ((env n).val,q)))) atTop (𝓝 0) := by
  apply thermal_compact_pullback_zero_local hMityagin hα hγ hμ t₀ x v hv henv hK hKT
    hB hM (fun n => (hg n).comp toKinetic.measurable) hρ (fun n z => hgM n (toKinetic z))
  intro R hR
  let C := toKinetic '' closedBall (0 : State) R
  have hC : IsCompact C := (isCompact_closedBall (0 : State) R).image toKinetic_continuous
  have hi (n : ℕ) : (∫⁻ z in closedBall (0 : State) R, g n (toKinetic z)) =
      ∫⁻ z in C, g n z := by
    have h := toKinetic_measurePreserving.setLIntegral_comp_preimage hC.measurableSet (hg n)
    simpa only [C,toKinetic.injective.preimage_image] using h
  simpa only [Function.comp_apply,hi] using hL C hC

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Bounded actual five-gain parameter densities

Each factor is the six-parameter density of the physical rescaled core.
Arbitrary retained-path masks are allowed, with their velocity and time
restrictions stated explicitly. The final lemma applies the proved thermal
map pullback theorem to these actual factors.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

theorem stageDensity_bound {r K α γ qexp a b Vmax : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) (env : PositiveEnvironment) (q : ThermalControls)
    (i : Fin 5) (hi : stageGood colors α γ a b Vmax env.val q i) :
    stageDensity colors r η K α γ qexp env.val q i ≤
      parameterSlabBound K α γ qexp a b Vmax :=
  rescaledParameterDensity_slab_bound hr hK hα hγ (env.property i) ha hi.1 hq hb hV
    η _ _ _ _ _ _ hi.2.1 hi.2.2

theorem masked_pathDensity_bound {r K α γ qexp a b Vmax : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) (env : PositiveEnvironment)
    (q : ThermalControls) (m : ℝ≥0∞) (hm : m ≤ 1)
    (hgood : m ≠ 0 → ∀ i, stageGood colors α γ a b Vmax env.val q i) :
    m*pathDensity colors r η K α γ qexp env.val q ≤
      (parameterSlabBound K α γ qexp a b Vmax)^5 := by
  by_cases hz : m = 0
  · simp only [hz,zero_mul]
    exact zero_le
  have hp : pathDensity colors r η K α γ qexp env.val q ≤
      (parameterSlabBound K α γ qexp a b Vmax)^5 := by
    unfold pathDensity
    calc
      _ ≤ ∏ _i : Fin 5, parameterSlabBound K α γ qexp a b Vmax :=
        Finset.prod_le_prod' (fun i _ => stageDensity_bound hr hK hα hγ hq ha hb hV
          colors η env q i (hgood hz i))
      _ = _ := by simp
  simpa only [one_mul] using mul_le_mul' hm hp

theorem five_gain_parameter_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a b Vmax : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) {μ : Fin 5 → ℝ} (hμ : ∀ i, 0 < μ i)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    {D : Set ThermalControls} (hD : IsCompact D) (hDT : D ⊆ controlDomain)
    (mask : ℕ → ThermalControls → ℝ≥0∞)
    (hm : ∀ n q, q ∈ controlDomain → mask n q ≤ 1)
    (hgood : ∀ n q, q ∈ controlDomain → mask n q ≠ 0 →
      ∀ i, stageGood colors α γ a b Vmax (env n).val q i)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q in D,
      (mask n q*pathDensity colors (r n) η K α γ qexp (env n).val q)*
        g n (toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ ((env n).val,q))))
      atTop (𝓝 0) := by
  apply thermal_compact_pullback_zero_physical hMityagin hα.le hγ.le hμ t₀ x v hv henv hD hDT
    (B := (parameterSlabBound K α γ qexp a b Vmax)^5)
    (ENNReal.pow_ne_top (parameterSlabBound_ne_top K α γ qexp a b Vmax)) hM hg ?_ hgM hL
  intro n q hqD
  exact masked_pathDensity_bound (hr n) hK hα hγ hq ha hb hV colors η (env n) q
    (mask n q) (hm n q hqD) (hgood n q hqD)

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Product volume for the five physical collision parameter blocks -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

theorem packControls_measurePreserving : MeasurePreserving packControls :=
  (volume_measurePreserving_arrowProdEquivProdArrow (ℝ × V) V (Fin 5)).trans
    ((volume_measurePreserving_arrowProdEquivProdArrow ℝ V (Fin 5)).prod
      (MeasurePreserving.id volume))

theorem integrateControls_eq (n : ℕ) {F : (Fin n → StageControls) → ℝ≥0∞}
    (hF : Measurable F) : integrateControls n F = ∫⁻ q, F q := by
  induction n with
  | zero =>
    rw [Measure.volume_pi_eq_dirac (Fin.elim0 : Fin 0 → StageControls)]
    simp only [integrateControls,lintegral_dirac' _ hF]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => StageControls) 0
    have he : MeasurePreserving e :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => StageControls) 0
    have heq (p : StageControls × (Fin n → StageControls)) :
        e.symm p = Fin.cons p.1 p.2 := by
      exact Fin.insertNth_zero' p.1 p.2
    have hcons : Measurable (fun p : StageControls × (Fin n → StageControls) =>
        F (Fin.cons p.1 p.2)) := by
      simpa only [Function.comp_def,heq] using hF.comp e.symm.measurable
    have hinner (p : StageControls) : Measurable (fun q => F (Fin.cons p q)) :=
      hcons.comp measurable_prodMk_left
    simp only [integrateControls,ih (hinner _)]
    have hprod := lintegral_prod (μ := (volume : Measure StageControls))
      (ν := (volume : Measure (Fin n → StageControls))) _ hcons.aemeasurable
    change (∫⁻ p, ∫⁻ q, F (Fin.cons p q)) = _
    rw [← hprod]
    simpa only [heq,Measure.volume_eq_prod] using he.symm.lintegral_comp hF

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # A compact parameter box for all five retained collisions -/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

theorem mem_velocityParameterBall (R : ℝ) (v : V) :
    v ∈ velocityParameterBall R ↔ ‖WithLp.toLp 2 v‖ ≤ R := by
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa only [mem_closedBall,dist_zero_right,WithLp.toLp_ofLp] using hw
  · intro hv
    refine ⟨WithLp.toLp 2 v,?_,rfl⟩
    simpa only [mem_closedBall,dist_zero_right] using hv

theorem velocityParameterBall_compact (R : ℝ) : IsCompact (velocityParameterBall R) :=
  (isCompact_closedBall (0 : Velocity) R).image (PiLp.continuous_ofLp 2 (fun _ : Fin 3 => ℝ))

theorem parameterBox_compact (a T R : ℝ) : IsCompact (parameterBox a T R) :=
  ((isCompact_univ_pi (fun _ : Fin 5 => isCompact_Icc)).prod
    (isCompact_univ_pi (fun _ : Fin 5 => velocityParameterBall_compact R))).prod
      (isCompact_univ_pi (fun _ : Fin 5 => velocityParameterBall_compact 1))

theorem mem_parameterBox (a T R : ℝ) (q : ThermalControls) :
    q ∈ parameterBox a T R ↔ ∀ i : Fin 5,
      q.1.1 i ∈ Icc a T ∧ ‖WithLp.toLp 2 (q.1.2 i)‖ ≤ R ∧
        ‖WithLp.toLp 2 (q.2 i)‖ ≤ 1 := by
  constructor
  · rintro ⟨⟨ht,hL⟩,hw⟩ i
    exact ⟨ht i (mem_univ i),(mem_velocityParameterBall R _).mp (hL i (mem_univ i)),
      (mem_velocityParameterBall 1 _).mp (hw i (mem_univ i))⟩
  · intro h
    exact ⟨⟨fun i _ => (h i).1,fun i _ => (mem_velocityParameterBall R _).mpr (h i).2.1⟩,
      fun i _ => (mem_velocityParameterBall 1 _).mpr (h i).2.2⟩

theorem parameterBox_subset_domain {a : ℝ} (ha : 0 < a) (T R : ℝ) :
    parameterBox a T R ⊆ controlDomain := by
  intro q hq i
  exact ha.trans_le ((mem_parameterBox a T R q).mp hq i).1.1

end BoltzmannNonuniqueness.FiveGainMap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteParameterChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite parameterized gain chain as one product integral

This is the Fubini assembly used after replacing each physical collision by its
thermal and redundant-plane parameters. The transition maps and densities are
explicit functions, and the conclusion is an exact integral identity.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

theorem integrateControls_const_mul {c : ℝ≥0∞} (hc : c ≠ ∞) (n : ℕ)
    (F : (Fin n → StageControls) → ℝ≥0∞) :
    integrateControls n (fun q => c*F q) = c*integrateControls n F := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [integrateControls,ih]
    exact lintegral_const_mul' _ _ hc

theorem parameterChain_eq_nested (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞)
    (hfinite : ∀ i z p, density i z p ≠ ∞) (g : State → ℝ≥0∞) (i n : ℕ) (z : State) :
    parameterChain next density g i n z =
      integrateControls n (chainIntegrand next density g i n z) := by
  induction n generalizing i z with
  | zero => rfl
  | succ n ih =>
    simp only [parameterChain,integrateControls]
    apply lintegral_congr
    intro p
    rw [ih]
    have he := integrateControls_const_mul (hfinite i z p) n
      (chainIntegrand next density g (i+1) n (next i z p))
    simpa only [chainIntegrand,Fin.cons_zero,Fin.tail_cons] using he.symm

theorem chainIntegrand_measurable (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞)
    (hnext : ∀ i, Measurable (fun p : State × StageControls => next i p.1 p.2))
    (hdensity : ∀ i, Measurable (fun p : State × StageControls => density i p.1 p.2))
    {g : State → ℝ≥0∞} (hg : Measurable g) (i n : ℕ) :
    Measurable (fun p : State × (Fin n → StageControls) =>
      chainIntegrand next density g i n p.1 p.2) := by
  induction n generalizing i with
  | zero => exact hg.comp measurable_fst
  | succ n ih =>
    have hfirst : Measurable (fun p : State × (Fin (n+1) → StageControls) => (p.1,p.2 0)) :=
      measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)
    have htail : Measurable (fun p : State × (Fin (n+1) → StageControls) => Fin.tail p.2) := by
      exact Measurable.of_eval (fun j => (measurable_pi_apply j.succ).comp measurable_snd)
    exact ((hdensity i).comp hfirst).mul
      ((ih (i+1)).comp (((hnext i).comp hfirst).prodMk htail))

theorem parameterChain_eq_product (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞)
    (hnext : ∀ i, Measurable (fun p : State × StageControls => next i p.1 p.2))
    (hdensity : ∀ i, Measurable (fun p : State × StageControls => density i p.1 p.2))
    (hfinite : ∀ i z p, density i z p ≠ ∞) {g : State → ℝ≥0∞} (hg : Measurable g)
    (i n : ℕ) (z : State) :
    parameterChain next density g i n z =
      ∫⁻ q : Fin n → StageControls, chainIntegrand next density g i n z q := by
  rw [parameterChain_eq_nested next density hfinite g i n z]
  exact integrateControls_eq n ((chainIntegrand_measurable next density hnext hdensity hg i n).comp
    measurable_prodMk_left)

end BoltzmannNonuniqueness.FiveGainMap

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ControlledParameterPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact density product along a finite controlled collision path -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

theorem controlledPath_shift (next : ℕ → State → StageControls → State)
    (controls : ℕ → StageControls) (i n : ℕ) (z : State) :
    controlledPath next controls i z (n+1) =
      controlledPath next controls (i+1) (next i z (controls i)) n := by
  induction n with
  | zero => simp only [controlledPath,Nat.add_zero]
  | succ n ih =>
    change next (i+(n+1)) (controlledPath next controls i z (n+1)) (controls (i+(n+1))) =
      next ((i+1)+n) (controlledPath next controls (i+1) (next i z (controls i)) n)
        (controls ((i+1)+n))
    have he : i+(n+1) = (i+1)+n := by omega
    rw [ih,he]

theorem controlledPath_zero (next : ℕ → State → StageControls → State)
    (controls : ℕ → StageControls) (i : ℕ) (z : State) :
    controlledPath next controls i z 0 = z := rfl

theorem chainIntegrand_eq_pathProduct (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞) (g : State → ℝ≥0∞)
    (controls : ℕ → StageControls) (i n : ℕ) (z : State) :
    chainIntegrand next density g i n z (fun j => controls (i+j.val)) =
      (∏ j : Fin n, density (i+j.val) (controlledPath next controls i z j.val)
        (controls (i+j.val))) * g (controlledPath next controls i z n) := by
  induction n generalizing i z with
  | zero => simp only [chainIntegrand,controlledPath,Fin.prod_univ_zero,one_mul]
  | succ n ih =>
    rw [chainIntegrand]
    have htail : Fin.tail (fun j : Fin (n+1) => controls (i+j.val)) =
        (fun j : Fin n => controls ((i+1)+j.val)) := by
      funext j
      change controls (i+(j.val+1)) = controls ((i+1)+j.val)
      congr 1
      omega
    rw [htail,ih]
    rw [Fin.prod_univ_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ,controlledPath_shift,controlledPath_zero]
    have he (j : Fin n) : i+(j.val+1) = (i+1)+j.val := by omega
    simp only [he,mul_assoc]

end BoltzmannNonuniqueness.FiveGainMap

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_StageParameterIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrating a collision parameter block in physical time, thermal, plane order -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

theorem splitStage_measurePreserving : MeasurePreserving splitStage :=
  (measurePreserving_prodAssoc volume volume volume).trans
    ((MeasurePreserving.id volume).prod
      (Measure.measurePreserving_swap (μ := volume) (ν := volume)))

theorem lintegral_stage {F : StageControls → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p) = ∫⁻ t : ℝ, ∫⁻ w : V, ∫⁻ L : V, F ((t,L),w) := by
  have h : Measurable (fun p : ℝ × (V × V) => F (splitStage.symm p)) :=
    hF.comp splitStage.symm.measurable
  calc
    _ = ∫⁻ p : ℝ × (V × V), F (splitStage.symm p) :=
      (splitStage_measurePreserving.symm.lintegral_comp hF).symm
    _ = ∫⁻ t : ℝ, ∫⁻ p : V × V, F (splitStage.symm (t,p)) := by
      rw [Measure.volume_eq_prod]
      exact lintegral_prod _ h.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro t
      rw [Measure.volume_eq_prod]
      exact lintegral_prod _ ((h.comp measurable_prodMk_left).aemeasurable)

end BoltzmannNonuniqueness.FiveGainMap

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_ThermalParameterChain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual positive core step in thermal collision coordinates -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.FiveGainMap

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem flight_toKinetic (z : State) (t : ℝ) :
    PositiveIteration.flight (toKinetic z) t =
      toKinetic (t,z.2.1-(z.1-t) • z.2.2,z.2.2) := rfl

theorem toKinetic_thermalStep (α γ μ d t : ℝ) (color : Bool) (w L : V) (z : State) :
    toKinetic (thermalStep (JetPrototype.sign color) α γ μ d t L w z) =
      ((t,WithLp.toLp 2 (z.2.1-(z.1-t) • z.2.2)),
        parameterPoint α γ μ d t color (jetPosition (z.2.1-(z.1-t) • z.2.2))
          (WithLp.toLp 2 z.2.2) w L) := by
  rw [thermalStep_eq_parameterPoint]
  rfl

theorem dilatedFreeKernel_parameter_integral {r α γ μ d : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hd : 0 < d)
    (η K q : ℝ) (color : Bool) (z : State) (ht : 0 ≤ z.1)
    (hv : transverse (WithLp.toLp 2 z.2.2) ≠ 0)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂dilatedFreeKernel r η K α γ (r*μ) d q color (toKinetic z)) =
      ∫⁻ w : V, ∫⁻ L : V,
        rescaledParameterDensity r η K α γ μ d z.1 q color
          (jetPosition z.2.1) (WithLp.toLp 2 z.2.2) w L *
          f (parameterPoint α γ μ d z.1 color (jetPosition z.2.1)
            (WithLp.toLp 2 z.2.2) w L) := by
  rw [dilatedFreeKernel_eq_rescaled hr]
  have hdiv : r*μ/r = μ := by field_simp
  rw [hdiv]
  exact rescaledCoreMeasure_parameter_integral hr hα hγ hμ hd ht η K q color
    (jetPosition z.2.1) (WithLp.toLp 2 z.2.2) hv hf

theorem step_thermal_core {r α γ μ d a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hd : 0 < d) (ha : 0 ≤ a)
    (η K q : ℝ) (color : Bool) (z : State)
    (hv : transverse (WithLp.toLp 2 z.2.2) ≠ 0)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    PositiveIteration.step a (dilatedFreeKernel r η K α γ (r*μ) d q color) f (toKinetic z) =
      ∫⁻ t in Ioc a z.1, ∫⁻ w : V, ∫⁻ L : V,
        rescaledParameterDensity r η K α γ μ d t q color
          (jetPosition (z.2.1-(z.1-t) • z.2.2)) (WithLp.toLp 2 z.2.2) w L *
          f (toKinetic (thermalStep (JetPrototype.sign color) α γ μ d t L w z)) := by
  unfold PositiveIteration.step
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [flight_toKinetic]
  have he := dilatedFreeKernel_parameter_integral hr hα hγ hμ hd η K q color
    (t,z.2.1-(z.1-t) • z.2.2,z.2.2) (ha.trans ht.1.le) hv
    (f := fun ξ => f ((t,WithLp.toLp 2 (z.2.1-(z.1-t) • z.2.2)),ξ))
    (hf.comp (measurable_const.prodMk measurable_id))
  refine he.trans ?_
  apply lintegral_congr
  intro w
  apply lintegral_congr
  intro L
  rw [toKinetic_thermalStep]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Measurable time and collision parameters for one actual positive core gain -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem stageArguments_measurable :
    Measurable (fun p : State × StageControls => stageArguments p.1 p.2) := by
  unfold stageArguments jetPosition transverse
  fun_prop

theorem validStage_measurable (a : ℝ) : MeasurableSet (validStage a) := by
  have h₁ : MeasurableSet {p : State × StageControls | a < p.2.1.1} :=
    measurableSet_lt measurable_const (by fun_prop)
  have h₂ : MeasurableSet {p : State × StageControls | p.2.1.1 ≤ p.1.1} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have h₃ : MeasurableSet {p : State × StageControls |
      transverse (WithLp.toLp 2 p.1.2.2) ≠ 0} :=
    (measurableSet_eq_fun (by unfold transverse; fun_prop) measurable_const).compl
  exact h₁.inter (h₂.inter h₃)

theorem coreNext_measurable {α γ μ : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ)
    (d : ℝ) (color : Bool) :
    Measurable (fun p : State × StageControls => coreNext α γ μ d color p.1 p.2) := by
  have hp := (clamped_parameterPoint_measurable hα hγ hμ d color).comp stageArguments_measurable
  have hv : Measurable (fun p : State × StageControls =>
      WithLp.ofLp (parameterPoint α γ μ d (max 0 p.2.1.1) color
        (stageArguments p.1 p.2).1.2 (stageArguments p.1 p.2).2.1 p.2.2 p.2.1.2)) :=
    (MeasurableEquiv.toLp 2 V).symm.measurable.comp hp
  exact (by fun_prop : Measurable (fun p : State × StageControls => max 0 p.2.1.1)).prodMk
    ((by fun_prop : Measurable (fun p : State × StageControls =>
      p.1.2.1-(p.1.1-max 0 p.2.1.1) • p.1.2.2)).prodMk hv)

theorem coreDensity_measurable {r α γ μ : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (η K d q a : ℝ) (color : Bool) :
    Measurable (fun p : State × StageControls => coreDensity r η K α γ μ d q a color p.1 p.2) :=
  ((clamped_rescaledParameterDensity_measurable hr hα hγ hμ η K d q color).comp
    stageArguments_measurable).indicator (validStage_measurable a)

theorem coreNext_eq_thermalStep {α γ μ d : ℝ} (color : Bool) (z : State)
    (p : StageControls) (ht : 0 ≤ p.1.1) :
    coreNext α γ μ d color z p =
      thermalStep (JetPrototype.sign color) α γ μ d p.1.1 p.1.2 p.2 z := by
  rw [thermalStep_eq_parameterPoint]
  unfold coreNext stageArguments
  rw [max_eq_right ht]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Exact identification of the positive physical step with a parameter block -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem coreDensity_ne_top (r η K α γ μ d q a : ℝ) (color : Bool)
    (z : State) (p : StageControls) : coreDensity r η K α γ μ d q a color z p ≠ ∞ := by
  unfold coreDensity
  by_cases h : (z,p) ∈ validStage a
  · rw [indicator_of_mem h]
    unfold rescaledParameterDensity parameterDensity
    have hn (x : ℝ) : RedundantPlane.normalDensity x ≠ ∞ :=
      ne_top_of_le_ne_top (by norm_num) (RedundantPlane.normalDensity_le_one x)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) (hn _)) ENNReal.ofReal_ne_top)
  · rw [indicator_of_notMem h]
    exact ENNReal.zero_ne_top

theorem step_eq_parameter_block {r α γ μ d a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hd : 0 < d) (ha : 0 ≤ a)
    (η K q : ℝ) (color : Bool) (z : State)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    PositiveIteration.step a (dilatedFreeKernel r η K α γ (r*μ) d q color) f (toKinetic z) =
      ∫⁻ p : StageControls, coreDensity r η K α γ μ d q a color z p *
        f (toKinetic (coreNext α γ μ d color z p)) := by
  have hD : Measurable (fun p : StageControls => coreDensity r η K α γ μ d q a color z p) :=
    (coreDensity_measurable hr hα hγ hμ η K d q a color).comp measurable_prodMk_left
  have hN : Measurable (fun p : StageControls => coreNext α γ μ d color z p) :=
    (coreNext_measurable hα hγ hμ d color).comp measurable_prodMk_left
  have hF : Measurable (fun p : StageControls => coreDensity r η K α γ μ d q a color z p *
      f (toKinetic (coreNext α γ μ d color z p))) :=
    hD.mul (hf.comp (toKinetic.measurable.comp hN))
  by_cases hv : transverse (WithLp.toLp 2 z.2.2) = 0
  · have hzero (p : StageControls) : coreDensity r η K α γ μ d q a color z p = 0 := by
      apply indicator_of_notMem
      intro h
      exact h.2.2 hv
    have hkernel (t : ℝ) :
        dilatedFreeKernel r η K α γ (r*μ) d q color (PositiveIteration.flight (toKinetic z) t) = 0 := by
      apply ChartKernel.offAxis_axis
      exact hv
    simp only [PositiveIteration.step,hkernel,lintegral_zero_measure,lintegral_zero,hzero,zero_mul]
  · rw [step_thermal_core hr hα hγ hμ hd ha η K q color z hv hf,lintegral_stage hF]
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ Ioc a z.1
    · rw [indicator_of_mem ht]
      apply lintegral_congr
      intro w
      apply lintegral_congr
      intro L
      have hvalid : (z,((t,L),w)) ∈ validStage a := ⟨ht.1,ht.2,hv⟩
      rw [coreDensity,indicator_of_mem hvalid,coreNext_eq_thermalStep color z _ (ha.trans ht.1.le)]
      dsimp only [stageArguments]
      rw [max_eq_right (ha.trans ht.1.le)]
    · rw [indicator_of_notMem ht]
      symm
      have hz (w L : FiveGainMap.V) :
          coreDensity r η K α γ μ d q a color z ((t,L),w) = 0 := by
        apply indicator_of_notMem
        intro h
        exact ht ⟨h.1,h.2.1⟩
      simp only [hz,zero_mul,lintegral_zero]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedThermalChain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Multiplicative state restrictions along a finite collision path -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.FiveGainMap

theorem statePathWeight_le_one (next : ℕ → State → StageControls → State)
    (weight : ℕ → State → ℝ≥0∞) (hw : ∀ i z, weight i z ≤ 1)
    (controls : ℕ → StageControls) (i n : ℕ) (z : State) :
    statePathWeight next weight controls i n z ≤ 1 :=
  Finset.prod_le_one' (fun j _ => hw (i+j.val) _)

attribute [local irreducible] controlledPath

theorem chainIntegrand_weighted (next : ℕ → State → StageControls → State)
    (density : ℕ → State → StageControls → ℝ≥0∞)
    (weight : ℕ → State → ℝ≥0∞) (g : State → ℝ≥0∞)
    (controls : ℕ → StageControls) (i n : ℕ) (z : State) :
    chainIntegrand next (fun i z p => density i z p*weight i (next i z p)) g i n z
        (fun j => controls (i+j.val)) =
      statePathWeight next weight controls i n z *
        chainIntegrand next density g i n z (fun j => controls (i+j.val)) := by
  rw [chainIntegrand_eq_pathProduct,chainIntegrand_eq_pathProduct]
  have hstep (j : Fin n) :
      next (i+j.val) (controlledPath next controls i z j.val) (controls (i+j.val)) =
        controlledPath next controls i z (j.val+1) := by
    rw [controlledPath]
  simp only [hstep,Finset.prod_mul_distrib,statePathWeight]
  ring

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Actual physical core chains with spatial and velocity restrictions -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem weightedCoreChain_measurable (r η K α γ q a : ℝ) (μ d : ℕ → ℝ) (colors : ℕ → Bool)
    {weight : ℕ → Published.KineticPhase → ℝ≥0∞} (hw : ∀ i, Measurable (weight i))
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) :
    Measurable (weightedCoreChain r η K α γ q a μ d colors weight f i n) := by
  induction n generalizing i with
  | zero => exact hf
  | succ n ih => exact PositiveIteration.step_measurable a _ ((hw i).mul (ih (i+1)))

theorem weightedCoreChain_eq_parameters {r α γ a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 ≤ a) (η K q : ℝ)
    (μ d : ℕ → ℝ) (colors : ℕ → Bool) (hμ : ∀ i, 0 < μ i) (hd : ∀ i, 0 < d i)
    {weight : ℕ → Published.KineticPhase → ℝ≥0∞} (hw : ∀ i, Measurable (weight i))
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) (z : State) :
    weightedCoreChain r η K α γ q a μ d colors weight f i n (toKinetic z) =
      parameterChain (fun i => coreNext α γ (μ i) (d i) (colors i))
        (fun i z p => coreDensity r η K α γ (μ i) (d i) q a (colors i) z p *
          weight i (toKinetic (coreNext α γ (μ i) (d i) (colors i) z p)))
        (fun z => f (toKinetic z)) i n z := by
  induction n generalizing i z with
  | zero => rfl
  | succ n ih =>
    change PositiveIteration.step a _ _ (toKinetic z) = _
    rw [step_eq_parameter_block (f := fun y => weight i y *
      weightedCoreChain r η K α γ q a μ d colors weight f (i+1) n y)
      hr hα hγ (hμ i) (hd i) ha η K q (colors i) z
      ((hw i).mul (weightedCoreChain_measurable r η K α γ q a μ d colors hw hf (i+1) n))]
    simp only [parameterChain]
    apply lintegral_congr
    intro p
    rw [ih,mul_assoc]

theorem weightedCoreChain_product_integral {r α γ a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 ≤ a) (η K q : ℝ)
    (μ d : ℕ → ℝ) (colors : ℕ → Bool) (hμ : ∀ i, 0 < μ i) (hd : ∀ i, 0 < d i)
    {weight : ℕ → Published.KineticPhase → ℝ≥0∞} (hw : ∀ i, Measurable (weight i))
    (hwfin : ∀ i z, weight i z ≠ ∞)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) (z : State) :
    weightedCoreChain r η K α γ q a μ d colors weight f i n (toKinetic z) =
      ∫⁻ p : Fin n → StageControls,
        chainIntegrand (fun i => coreNext α γ (μ i) (d i) (colors i))
          (fun i z p => coreDensity r η K α γ (μ i) (d i) q a (colors i) z p *
            weight i (toKinetic (coreNext α γ (μ i) (d i) (colors i) z p)))
          (fun z => f (toKinetic z)) i n z p := by
  rw [weightedCoreChain_eq_parameters hr hα hγ ha η K q μ d colors hμ hd hw hf]
  apply parameterChain_eq_product
  · exact fun i => coreNext_measurable hα hγ (hμ i) (d i) (colors i)
  · intro i
    exact (coreDensity_measurable hr hα hγ (hμ i) η K (d i) q a (colors i)).mul
      ((hw i).comp (toKinetic.measurable.comp (coreNext_measurable hα hγ (hμ i) (d i) (colors i))))
  · exact fun i z p => ENNReal.mul_ne_top
      (coreDensity_ne_top r η K α γ (μ i) (d i) q a (colors i) z p) (hwfin i _)
  · exact hf.comp toKinetic.measurable

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FiveGainConvergence
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Identification of the five actual thermal transitions with the analytic path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

theorem cycleFive_apply {A : Type*} (f : Fin 5 → A) (i : Fin 5) : cycleFive f i.val = f i := by
  unfold cycleFive
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem controlBlocks_eq (q : ThermalControls) : controlBlocks q = packControls.symm q := rfl

theorem actualNext_controlBlock (colors : Fin 5 → Bool) (α γ : ℝ)
    (env : ThermalEnvironment) {q : ThermalControls} (hq : q ∈ controlDomain)
    (i : Fin 5) (z : State) :
    actualNext colors α γ env i.val z (cycleFive (controlBlocks q) i.val) =
      thermalStep (JetPrototype.sign (colors i)) α γ (env.1 i) (env.2.1 i)
        (q.1.1 i) (q.1.2 i) (q.2 i) z := by
  simp only [actualNext,cycleFive_apply,controlBlocks]
  exact coreNext_eq_thermalStep (colors i) z _ (hq i).le

attribute [local irreducible] thermalPath actualNext

theorem actualPath_eq_thermalPath (colors : Fin 5 → Bool) (α γ : ℝ)
    (env : ThermalEnvironment) {q : ThermalControls} (hq : q ∈ controlDomain)
    {n : ℕ} (hn : n ≤ 5) :
    controlledPath (actualNext colors α γ env) (cycleFive (controlBlocks q)) 0 env.2.2 n =
      thermalPath (fun i => JetPrototype.sign (colors i)) α γ env q n := by
  induction n with
  | zero => simp only [controlledPath,thermalPath]
  | succ n ih =>
    have hnlt : n < 5 := by omega
    have hprev := ih (by omega)
    rw [controlledPath,hprev]
    simp only [Nat.zero_add,thermalPath,dite_eq_left hnlt]
    let i : Fin 5 := ⟨n,hnlt⟩
    exact actualNext_controlBlock colors α γ env hq i _

theorem stageValidity_le_one (colors : Fin 5 → Bool) (α γ a : ℝ)
    (env : ThermalEnvironment) (q : ThermalControls) (i : Fin 5) :
    stageValidity colors α γ a env q i ≤ 1 := by
  unfold stageValidity
  exact indicator_le_self' (fun _ _ => zero_le) _

theorem coreDensity_eq_stage {r η K α γ qexp a : ℝ} (colors : Fin 5 → Bool)
    (env : ThermalEnvironment) {q : ThermalControls} (hq : q ∈ controlDomain) (i : Fin 5) :
    coreDensity r η K α γ (env.1 i) (env.2.1 i) qexp a (colors i)
      (stagePrevious colors α γ env q i) (controlBlocks q i) =
        stageValidity colors α γ a env q i * stageDensity colors r η K α γ qexp env q i := by
  unfold coreDensity stageValidity
  by_cases hv : (stagePrevious colors α γ env q i,controlBlocks q i) ∈ validStage a
  · rw [indicator_of_mem hv,indicator_of_mem hv,one_mul]
    simp only [controlBlocks,stageArguments,max_eq_right (hq i).le]
    rfl
  · rw [indicator_of_notMem hv,indicator_of_notMem hv,zero_mul]

theorem pathValidity_le_one (colors : Fin 5 → Bool) (α γ a : ℝ)
    (env : ThermalEnvironment) (q : ThermalControls) : pathValidity colors α γ a env q ≤ 1 := by
  unfold pathValidity
  calc
    _ ≤ ∏ _i : Fin 5, (1 : ℝ≥0∞) := Finset.prod_le_prod' (fun i _ =>
      stageValidity_le_one colors α γ a env q i)
    _ = _ := by simp

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # The actual five-collision integrand is the bounded thermal path density -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] thermalPath actualNext actualDensity coreDensity stageDensity

theorem actualFiveIntegrand_eq (colors : Fin 5 → Bool) (r η K α γ qexp a : ℝ)
    (env : ThermalEnvironment) (f : Published.KineticPhase → ℝ≥0∞)
    {q : ThermalControls} (hq : q ∈ controlDomain) :
    actualFiveIntegrand colors r η K α γ qexp a env f q =
      (pathValidity colors α γ a env q * pathDensity colors r η K α γ qexp env q) *
        f (toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ (env,q))) := by
  let next := actualNext colors α γ env
  let density := actualDensity colors r η K α γ qexp a env
  let controls := cycleFive (controlBlocks q)
  have he := chainIntegrand_eq_pathProduct next density (fun z => f (toKinetic z))
    controls 0 5 env.2.2
  simp only [Nat.zero_add] at he
  have hcontrols : (fun j : Fin 5 => controls j.val) = controlBlocks q := by
    funext j
    exact cycleFive_apply (controlBlocks q) j
  rw [hcontrols] at he
  have hp (n : ℕ) (hn : n ≤ 5) : controlledPath next controls 0 env.2.2 n =
      thermalPath (fun i => JetPrototype.sign (colors i)) α γ env q n :=
    actualPath_eq_thermalPath colors α γ env hq hn
  have hfactor (i : Fin 5) : density i.val (controlledPath next controls 0 env.2.2 i.val)
      (controls i.val) = stageValidity colors α γ a env q i *
        stageDensity colors r η K α γ qexp env q i := by
    rw [hp i.val i.isLt.le]
    simp only [density,actualDensity,controls,cycleFive_apply]
    exact coreDensity_eq_stage colors env hq i
  have hprod : (∏ i : Fin 5, density i.val (controlledPath next controls 0 env.2.2 i.val)
      (controls i.val)) = ∏ i : Fin 5, stageValidity colors α γ a env q i *
        stageDensity colors r η K α γ qexp env q i :=
    Finset.prod_congr rfl (fun i _ => hfactor i)
  calc
    _ = (∏ i : Fin 5, density i.val (controlledPath next controls 0 env.2.2 i.val)
        (controls i.val)) * f (toKinetic (controlledPath next controls 0 env.2.2 5)) := he
    _ = (∏ i : Fin 5, stageValidity colors α γ a env q i *
        stageDensity colors r η K α γ qexp env q i) *
          f (toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ (env,q))) := by
      rw [hprod,hp 5 le_rfl]
      rfl
    _ = _ := by rw [Finset.prod_mul_distrib]; rfl

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Physical five-collision integrals have only positive collision times -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] actualNext actualDensity coreDensity thermalPath

theorem actualFiveIntegrand_zero_outside {a : ℝ} (ha : 0 ≤ a)
    (colors : Fin 5 → Bool) (r η K α γ qexp : ℝ) (env : ThermalEnvironment)
    (f : Published.KineticPhase → ℝ≥0∞) {q : ThermalControls} (hq : q ∉ controlDomain) :
    actualFiveIntegrand colors r η K α γ qexp a env f q = 0 := by
  classical
  have hbad : ∃ i : Fin 5, q.1.1 i ≤ 0 := by
    change ¬ (∀ i : Fin 5, 0 < q.1.1 i) at hq
    push Not at hq
    exact hq
  obtain ⟨i,hi⟩ := hbad
  let next := actualNext colors α γ env
  let density := actualDensity colors r η K α γ qexp a env
  let controls := cycleFive (controlBlocks q)
  have he := chainIntegrand_eq_pathProduct next density (fun z => f (toKinetic z))
    controls 0 5 env.2.2
  simp only [Nat.zero_add] at he
  have hcontrols : (fun j : Fin 5 => controls j.val) = controlBlocks q := by
    funext j
    exact cycleFive_apply (controlBlocks q) j
  rw [hcontrols] at he
  have hzero : density i.val (controlledPath next controls 0 env.2.2 i.val) (controls i.val) = 0 := by
    unfold density actualDensity controls
    rw [cycleFive_apply,cycleFive_apply,cycleFive_apply,cycleFive_apply]
    unfold coreDensity
    apply indicator_of_notMem
    intro h
    exact (not_lt_of_ge (hi.trans ha)) h.1
  have hp : (∏ j : Fin 5, density j.val (controlledPath next controls 0 env.2.2 j.val)
      (controls j.val)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hzero
  rw [hp,zero_mul] at he
  exact he

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Compact retained physical five-core integrals vanish by the published scalar input -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.FiveGainMap

theorem actual_five_core_masked_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a b Vmax : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) {μ : Fin 5 → ℝ} (hμ : ∀ i, 0 < μ i)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    {D : Set ThermalControls} (hD : IsCompact D) (hDT : D ⊆ controlDomain)
    (mask : ℕ → ThermalControls → ℝ≥0∞)
    (hm : ∀ n q, q ∈ controlDomain → mask n q ≤ 1)
    (hgood : ∀ n q, q ∈ controlDomain → mask n q ≠ 0 →
      pathValidity colors α γ a (env n).val q ≠ 0 →
      ∀ i, stageGood colors α γ a b Vmax (env n).val q i)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q in D, mask n q*
      actualFiveIntegrand colors (r n) η K α γ qexp a (env n).val (g n) q)
      atTop (𝓝 0) := by
  let retained : ℕ → ThermalControls → ℝ≥0∞ :=
    fun n q => mask n q*pathValidity colors α γ a (env n).val q
  have hretained : ∀ n q, q ∈ controlDomain → retained n q ≤ 1 := by
    intro n q hqt
    simpa only [one_mul] using mul_le_mul' (hm n q hqt)
      (pathValidity_le_one colors α γ a (env n).val q)
  have hrGood : ∀ n q, q ∈ controlDomain → retained n q ≠ 0 →
      ∀ i, stageGood colors α γ a b Vmax (env n).val q i := by
    intro n q hqt hne
    have hn := mul_ne_zero_iff.mp hne
    exact hgood n q hqt hn.1 hn.2
  have hlim := five_gain_parameter_tendsto hMityagin hK hα hγ hq ha hb hV colors η hμ
    t₀ x v hv henv r hr hD hDT retained hretained hrGood hM hg hgM hL
  have he : (fun n => ∫⁻ q in D, mask n q*
        actualFiveIntegrand colors (r n) η K α γ qexp a (env n).val (g n) q) =
      (fun n => ∫⁻ q in D,
        (retained n q*pathDensity colors (r n) η K α γ qexp (env n).val q)*
          g n (toKinetic (thermalMap (fun i => JetPrototype.sign (colors i)) α γ ((env n).val,q)))) := by
    funext n
    apply setLIntegral_congr_fun hD.measurableSet
    intro q hqd
    dsimp only
    rw [actualFiveIntegrand_eq colors (r n) η K α γ qexp a (env n).val (g n) (hDT hqd)]
    dsimp only [retained]
    ring
  rw [he]
  exact hlim

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Exact physical five-core integrals with all state restrictions retained -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

theorem actualPathWeight_le_one (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞) (hw : ∀ i z, weight i z ≤ 1)
    (q : ThermalControls) : actualPathWeight colors α γ env weight q ≤ 1 :=
  statePathWeight_le_one _ _ (fun _i z => hw _ (toKinetic z)) _ _ _ _

attribute [local irreducible] actualNext actualDensity actualFiveIntegrand controlledPath

theorem weighted_five_integrand (colors : Fin 5 → Bool) (r η K α γ qexp a : ℝ)
    (env : ThermalEnvironment) (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞)
    (f : Published.KineticPhase → ℝ≥0∞) (q : ThermalControls) :
    chainIntegrand (actualNext colors α γ env)
      (fun i z p => actualDensity colors r η K α γ qexp a env i z p *
        cycleFive weight i (toKinetic (actualNext colors α γ env i z p)))
      (fun z => f (toKinetic z)) 0 5 env.2.2 (controlBlocks q) =
        actualPathWeight colors α γ env weight q *
          actualFiveIntegrand colors r η K α γ qexp a env f q := by
  have h := chainIntegrand_weighted (actualNext colors α γ env)
    (actualDensity colors r η K α γ qexp a env)
    (fun i z => cycleFive weight i (toKinetic z)) (fun z => f (toKinetic z))
    (cycleFive (controlBlocks q)) 0 5 env.2.2
  have hc : (fun j : Fin 5 => cycleFive (controlBlocks q) (0+j.val)) = controlBlocks q := by
    funext j
    simpa only [Nat.zero_add] using cycleFive_apply (controlBlocks q) j
  rw [hc] at h
  simpa only [actualPathWeight,actualFiveIntegrand] using h

theorem actual_weighted_five_integral {r α γ a : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 ≤ a) (colors : Fin 5 → Bool)
    (η K qexp : ℝ) (env : PositiveEnvironment) (hd : ∀ i, 0 < env.val.2.1 i)
    (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞)
    (hw : ∀ i, Measurable (weight i)) (hwfin : ∀ i z, weight i z ≠ ∞)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) :
    weightedCoreChain r η K α γ qexp a (cycleFive env.val.1) (cycleFive env.val.2.1)
      (cycleFive colors) (cycleFive weight) f 0 5 (toKinetic env.val.2.2) =
        ∫⁻ q, actualPathWeight colors α γ env.val weight q *
          actualFiveIntegrand colors r η K α γ qexp a env.val f q := by
  let F : ThermalControls → ℝ≥0∞ := fun q =>
    chainIntegrand (actualNext colors α γ env.val)
      (fun i z p => actualDensity colors r η K α γ qexp a env.val i z p *
        cycleFive weight i (toKinetic (actualNext colors α γ env.val i z p)))
      (fun z => f (toKinetic z)) 0 5 env.val.2.2 (controlBlocks q)
  have hnext (i : ℕ) : Measurable (fun p : State × StageControls =>
      actualNext colors α γ env.val i p.1 p.2) := by
    unfold actualNext
    exact coreNext_measurable hα hγ (env.property _) _ _
  have hdensity (i : ℕ) : Measurable (fun p : State × StageControls =>
      actualDensity colors r η K α γ qexp a env.val i p.1 p.2 *
        cycleFive weight i (toKinetic (actualNext colors α γ env.val i p.1 p.2))) := by
    apply Measurable.mul
    · unfold actualDensity
      exact coreDensity_measurable hr hα hγ (env.property _) η K _ qexp a _
    · exact (hw _).comp (toKinetic.measurable.comp (hnext i))
  have hinput : Measurable (fun q : ThermalControls => (env.val.2.2,packControls.symm q)) :=
    measurable_const.prodMk packControls.symm.measurable
  have hF : Measurable F := by
    have hh := (chainIntegrand_measurable (actualNext colors α γ env.val)
      (fun i z p => actualDensity colors r η K α γ qexp a env.val i z p *
        cycleFive weight i (toKinetic (actualNext colors α γ env.val i z p))) hnext hdensity
      (hf.comp toKinetic.measurable) 0 5).comp hinput
    simpa only [F,controlBlocks_eq,Function.comp_def] using hh
  have he := packControls_measurePreserving.lintegral_comp hF
  calc
    _ = ∫⁻ p : Fin 5 → StageControls,
        chainIntegrand (actualNext colors α γ env.val)
          (fun i z p => actualDensity colors r η K α γ qexp a env.val i z p *
            cycleFive weight i (toKinetic (actualNext colors α γ env.val i z p)))
          (fun z => f (toKinetic z)) 0 5 env.val.2.2 p := by
      unfold actualNext actualDensity
      exact weightedCoreChain_product_integral hr hα hγ ha η K qexp _ _ _
        (fun _ => env.property _) (fun _ => hd _) (fun _ => hw _) (fun _ z => hwfin _ z)
        hf 0 5 env.val.2.2
    _ = ∫⁻ q, F q := by
      convert he using 1
      all_goals try with_reducible_and_instances rfl
      apply lintegral_congr
      intro p
      dsimp only [F]
      rw [controlBlocks_eq,packControls.symm_apply_apply]
    _ = _ := by
      apply lintegral_congr
      intro q
      exact weighted_five_integrand colors r η K α γ qexp a env.val weight f q

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Uniform compact support of a retained physical five-collision path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.FiveGainMap

theorem retainedPath_stageGood {colors : Fin 5 → Bool} {α γ a T b Vmax : ℝ}
    {env : ThermalEnvironment} {q : ThermalControls}
    (h : retainedPath colors α γ a T b Vmax env q) (i : Fin 5) :
    stageGood colors α γ a b Vmax env q i :=
  ⟨(h i).1.1,(h i).2.1,(h i).2.2.2.2⟩

theorem retainedPath_density_support {r α γ a T b Vmax : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η K qexp : ℝ) (env : PositiveEnvironment)
    (hd : ∀ i, 0 < env.val.2.1 i) (hdmax : ∀ i, env.val.2.1 i ≤ 1)
    (hthin : ∀ i, env.val.2.1 i ≤ b/2) {q : ThermalControls}
    (hpath : retainedPath colors α γ a T b Vmax env.val q)
    (hpositive : pathDensity colors r η K α γ qexp env.val q ≠ 0) :
    q ∈ parameterBox a T (retainedPlaneBound α b Vmax) := by
  apply (mem_parameterBox a T _ q).mpr
  intro i
  have hfactor : stageDensity colors r η K α γ qexp env.val q i ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hpositive) i (Finset.mem_univ i)
  have hs := rescaledParameterDensity_support hr hα hγ (env.property i)
    (ha.le.trans (hpath i).1.1) (hd i) (hdmax i) hb (hthin i) hV η K qexp (colors i)
    (jetPosition (stagePosition colors α γ env.val q i))
    (WithLp.toLp 2 (stagePrevious colors α γ env.val q i).2.2) (q.2 i) (q.1.2 i)
    (hpath i).2.1 (hpath i).2.2.1 (hpath i).2.2.2.1 hfactor
  exact ⟨(hpath i).1,hs.2,hs.1.le⟩

theorem retained_integrand_zero_outside {r α γ a T b Vmax : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η K qexp : ℝ) (env : PositiveEnvironment)
    (hd : ∀ i, 0 < env.val.2.1 i) (hdmax : ∀ i, env.val.2.1 i ≤ 1)
    (hthin : ∀ i, env.val.2.1 i ≤ b/2) (mask : ThermalControls → ℝ≥0∞)
    (hpath : ∀ q, mask q ≠ 0 → q ∈ controlDomain →
      pathValidity colors α γ a env.val q ≠ 0 →
      retainedPath colors α γ a T b Vmax env.val q)
    (f : Published.KineticPhase → ℝ≥0∞) {q : ThermalControls}
    (hq : q ∉ parameterBox a T (retainedPlaneBound α b Vmax)) :
    mask q*actualFiveIntegrand colors r η K α γ qexp a env.val f q = 0 := by
  by_cases hm : mask q = 0
  · rw [hm,zero_mul]
  by_cases hqt : q ∈ controlDomain
  · rw [actualFiveIntegrand_eq colors r η K α γ qexp a env.val f hqt]
    by_cases hv : pathValidity colors α γ a env.val q = 0
    · rw [hv,zero_mul,zero_mul,mul_zero]
    have hz : pathDensity colors r η K α γ qexp env.val q = 0 := by
      by_contra hn
      exact hq (retainedPath_density_support hr hα hγ ha hb hV colors η K qexp env hd hdmax
        hthin (hpath q hm hqt hv) hn)
    rw [hz,mul_zero,zero_mul,mul_zero]
  · rw [actualFiveIntegrand_zero_outside ha.le colors r η K α γ qexp env.val f hqt,mul_zero]

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Full retained five-core integrals vanish on their actual compact support -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.FiveGainMap

theorem retained_integral_eq_box {r α γ a T b Vmax : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η K qexp : ℝ) (env : PositiveEnvironment)
    (hd : ∀ i, 0 < env.val.2.1 i) (hdmax : ∀ i, env.val.2.1 i ≤ 1)
    (hthin : ∀ i, env.val.2.1 i ≤ b/2) (mask : ThermalControls → ℝ≥0∞)
    (hpath : ∀ q, mask q ≠ 0 → q ∈ controlDomain →
      pathValidity colors α γ a env.val q ≠ 0 →
      retainedPath colors α γ a T b Vmax env.val q)
    (f : Published.KineticPhase → ℝ≥0∞) :
    (∫⁻ q, mask q*actualFiveIntegrand colors r η K α γ qexp a env.val f q) =
      ∫⁻ q in parameterBox a T (retainedPlaneBound α b Vmax),
        mask q*actualFiveIntegrand colors r η K α γ qexp a env.val f q := by
  symm
  apply setLIntegral_eq_of_support_subset
  intro q hq
  by_contra hout
  exact hq (retained_integrand_zero_outside hr hα hγ ha hb hV colors η K qexp env
    hd hdmax hthin mask hpath f hout)

theorem actual_five_retained_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) {μ : Fin 5 → ℝ} (hμ : ∀ i, 0 < μ i)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hd : ∀ᶠ n in atTop, ∀ i, 0 < (env n).val.2.1 i ∧
      (env n).val.2.1 i ≤ 1 ∧ (env n).val.2.1 i ≤ b/2)
    (mask : ℕ → ThermalControls → ℝ≥0∞)
    (hm : ∀ n q, q ∈ controlDomain → mask n q ≤ 1)
    (hpath : ∀ n q, mask n q ≠ 0 → q ∈ controlDomain →
      pathValidity colors α γ a (env n).val q ≠ 0 →
      retainedPath colors α γ a T b Vmax (env n).val q)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ q, mask n q*
      actualFiveIntegrand colors (r n) η K α γ qexp a (env n).val (g n) q)
      atTop (𝓝 0) := by
  have hlim := actual_five_core_masked_tendsto hMityagin hK hα hγ hq ha hb hV
    colors η hμ t₀ x v hv henv r hr (parameterBox_compact a T (retainedPlaneBound α b Vmax))
    (parameterBox_subset_domain ha T (retainedPlaneBound α b Vmax)) mask hm
    (fun n q hqt hm hv i => retainedPath_stageGood (hpath n q hm hqt hv) i) hM hg hgM hL
  apply (tendsto_congr' ?_).mpr hlim
  filter_upwards [hd] with n hn
  exact retained_integral_eq_box (hr n) hα.le hγ.le ha hb hV colors η K qexp (env n)
    (fun i => (hn i).1) (fun i => (hn i).2.1) (fun i => (hn i).2.2)
    (mask n) (hpath n) (g n)

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # State restrictions give the bounds of the retained five-collision path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.FiveGainMap

attribute [local irreducible] thermalPath actualNext controlledPath

theorem thermalPath_succ (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) :
    thermalPath (fun j => JetPrototype.sign (colors j)) α γ env q (i.val+1) =
      thermalStep (JetPrototype.sign (colors i)) α γ (env.1 i) (env.2.1 i)
        (q.1.1 i) (q.1.2 i) (q.2 i) (stagePrevious colors α γ env q i) := by
  rw [thermalPath,dite_eq_left i.isLt]
  rfl

theorem thermalPath_succ_time (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) :
    (thermalPath (fun j => JetPrototype.sign (colors j)) α γ env q (i.val+1)).1 = q.1.1 i := by
  rw [thermalPath_succ]
  rfl

theorem thermalPath_succ_velocity (colors : Fin 5 → Bool) (α γ : ℝ) (env : ThermalEnvironment)
    (q : ThermalControls) (i : Fin 5) :
    WithLp.toLp 2
      (thermalPath (fun j => JetPrototype.sign (colors j)) α γ env q (i.val+1)).2.2 =
        stagePoint colors α γ env q i := by
  rw [thermalPath_succ,thermalStep_eq_parameterPoint]
  rfl

theorem actualPathWeight_factor_ne_zero (colors : Fin 5 → Bool) (α γ : ℝ)
    (env : ThermalEnvironment) (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞)
    {q : ThermalControls} (hqt : q ∈ controlDomain)
    (hw : actualPathWeight colors α γ env weight q ≠ 0) (i : Fin 5) :
    weight i (toKinetic
      (thermalPath (fun j => JetPrototype.sign (colors j)) α γ env q (i.val+1))) ≠ 0 := by
  unfold actualPathWeight statePathWeight at hw
  have hi := (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ i)
  change cycleFive weight (0+i.val)
    (toKinetic (controlledPath (actualNext colors α γ env) (cycleFive (controlBlocks q))
      0 env.2.2 (i.val+1))) ≠ 0 at hi
  rw [Nat.zero_add,cycleFive_apply,
    actualPath_eq_thermalPath colors α γ env hqt (by omega)] at hi
  exact hi

/-- Any additional spatial masks are permitted: only their nonzero support matters. -/
theorem actualPathWeight_retained (colors : Fin 5 → Bool) (α γ a T b Vmax : ℝ)
    (env : ThermalEnvironment) (weight : Fin 5 → Published.KineticPhase → ℝ≥0∞)
    (hweight : ∀ i z, weight i z ≠ 0 →
      z.1.1 ∈ Icc a T ∧ ‖z.2‖ ≤ Vmax ∧ b ≤ ‖transverse z.2‖)
    (hinit : ‖WithLp.toLp 2 env.2.2.2.2‖ ≤ Vmax ∧
      b ≤ ‖transverse (WithLp.toLp 2 env.2.2.2.2)‖)
    {q : ThermalControls} (hqt : q ∈ controlDomain)
    (hw : actualPathWeight colors α γ env weight q ≠ 0) :
    retainedPath colors α γ a T b Vmax env q := by
  have hnext (i : Fin 5) := hweight i _
    (actualPathWeight_factor_ne_zero colors α γ env weight hqt hw i)
  have hnext' (i : Fin 5) : q.1.1 i ∈ Icc a T ∧
      ‖stagePoint colors α γ env q i‖ ≤ Vmax ∧
      b ≤ ‖transverse (stagePoint colors α γ env q i)‖ := by
    simpa only [toKinetic_apply,thermalPath_succ_time,thermalPath_succ_velocity] using hnext i
  intro i
  have hprev : ‖WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2‖ ≤ Vmax ∧
      b ≤ ‖transverse (WithLp.toLp 2 (stagePrevious colors α γ env q i).2.2)‖ := by
    by_cases hi : i.val = 0
    · simpa only [stagePrevious,hi,thermalPath] using hinit
    · let j : Fin 5 := ⟨i.val-1,by omega⟩
      have hj : j.val+1 = i.val := by dsimp [j]; omega
      have he := (hnext j).2
      simpa only [toKinetic_apply,hj,stagePrevious] using he
  exact ⟨(hnext' i).1,hprev.1,hprev.2,(hnext' i).2⟩

end BoltzmannNonuniqueness.FiveGainMap

end

end

section

/-! # Vanishing of the actual restricted five-core chain -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.FiveGainMap

theorem thermal_widths_eventually_small {μ : Fin 5 → ℝ} (hμ : ∀ i, 0 < μ i)
    (t₀ : ℝ) (x v : V) {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    {b : ℝ} (hb : 0 < b) :
    ∀ᶠ n in atTop, ∀ i, (env n).val.2.1 i ≤ 1 ∧ (env n).val.2.1 i ≤ b/2 := by
  have hi (i : Fin 5) : ∀ᶠ n in atTop,
      (env n).val.2.1 i ≤ 1 ∧ (env n).val.2.1 i ≤ b/2 := by
    have hcont : Continuous (fun e : PositiveEnvironment => e.val.2.1 i) := by fun_prop
    have hlim : Tendsto (fun n => (env n).val.2.1 i) atTop (𝓝 0) := by
      simpa only [Pi.zero_apply,Function.comp_def] using (hcont.tendsto _).comp henv
    filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
      hlim.eventually (gt_mem_nhds (half_pos hb))] with n h1 h2
    exact ⟨h1.le,h2.le⟩
  filter_upwards [(Finset.eventually_all (Finset.univ : Finset (Fin 5))).mpr
    (fun i _ => hi i)] with n hn i
  exact hn i (Finset.mem_univ i)

theorem actual_weighted_five_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → Bool) (η : ℝ) {μ : Fin 5 → ℝ} (hμ : ∀ i, 0 < μ i)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    {env : ℕ → PositiveEnvironment}
    (henv : Tendsto env atTop (𝓝 (⟨(μ,0,(t₀,x,v)),hμ⟩ : PositiveEnvironment)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hd : ∀ n i, 0 < (env n).val.2.1 i)
    (hinit : ∀ n, ‖WithLp.toLp 2 (env n).val.2.2.2.2‖ ≤ Vmax ∧
      b ≤ ‖transverse (WithLp.toLp 2 (env n).val.2.2.2.2)‖)
    (weight : ℕ → Fin 5 → Published.KineticPhase → ℝ≥0∞)
    (hwm : ∀ n i, Measurable (weight n i)) (hw : ∀ n i z, weight n i z ≤ 1)
    (hweight : ∀ n i z, weight n i z ≠ 0 →
      z.1.1 ∈ Icc a T ∧ ‖z.2‖ ≤ Vmax ∧ b ≤ ‖transverse z.2‖)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => weightedCoreChain (r n) η K α γ qexp a
      (cycleFive (env n).val.1) (cycleFive (env n).val.2.1) (cycleFive colors)
      (cycleFive (weight n)) (g n) 0 5 (toKinetic (env n).val.2.2)) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ n in atTop, ∀ i, 0 < (env n).val.2.1 i ∧
      (env n).val.2.1 i ≤ 1 ∧ (env n).val.2.1 i ≤ b/2 := by
    filter_upwards [thermal_widths_eventually_small hμ t₀ x v henv hb] with n hn i
    exact ⟨hd n i,hn i⟩
  have hlim := actual_five_retained_tendsto hMityagin hK hα hγ hq ha hb hV colors η
    hμ t₀ x v hv henv r hr hsmall
    (fun n => actualPathWeight colors α γ (env n).val (weight n))
    (fun n q _ => actualPathWeight_le_one colors α γ (env n).val (weight n) (hw n) q)
    (fun n q hm hqt _ => actualPathWeight_retained colors α γ a T b Vmax (env n).val
      (weight n) (hweight n) (hinit n) hqt hm) hM hg hgM hL
  apply hlim.congr'
  exact Eventually.of_forall (fun n => (actual_weighted_five_integral (hr n) hα.le hγ.le ha.le
    colors η K qexp (env n) (hd n) (weight n) (hwm n)
    (fun i z => ne_top_of_le_ne_top (by norm_num) (hw n i z)) (hg n)).symm)

end BoltzmannNonuniqueness.FiveGainMap

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteThermalLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Expansion of a finite selected gain into its collision-label tuples -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.Published

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_finset_sum {I : Type*} (s : Finset I) (a : ℝ)
    (K : Kernel KineticPhase Velocity) [IsSFiniteKernel K]
    (f : I → KineticPhase → ℝ≥0∞) (hf : ∀ i ∈ s, Measurable (f i)) :
    step a K (fun z => ∑ i ∈ s, f i z) = fun z => ∑ i ∈ s, step a K (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    funext z
    simp only [Finset.sum_empty]
    unfold step
    simp only [lintegral_zero]
  | @insert i s hi ih =>
    have hm := hf i (Finset.mem_insert_self i s)
    have ht := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    have he := step_add a K (g := fun z => ∑ j ∈ s, f j z) hm
    rw [show (fun z => f i z+∑ j ∈ s, f j z) = f i+(fun z => ∑ j ∈ s, f j z) from rfl,
      he,ht]
    rfl

theorem chosenGainChain_measurable {I : Type*} (a : ℝ)
    (K : ℕ → I → Kernel KineticPhase Velocity) [∀ i j, IsSFiniteKernel (K i j)]
    {weight : ℕ → I → KineticPhase → ℝ≥0∞} (hw : ∀ i j, Measurable (weight i j))
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) (labels : Fin n → I) :
    Measurable (chosenGainChain a K weight f i n labels) := by
  induction n generalizing i with
  | zero => exact hf
  | succ n ih => exact step_measurable a _ ((hw i (labels 0)).mul (ih (i+1) (Fin.tail labels)))

theorem finiteGainChain_eq_sum {I : Type*} [Fintype I] (a : ℝ)
    (K : ℕ → I → Kernel KineticPhase Velocity) [∀ i j, IsSFiniteKernel (K i j)]
    {weight : ℕ → I → KineticPhase → ℝ≥0∞} (hw : ∀ i j, Measurable (weight i j))
    {f : KineticPhase → ℝ≥0∞} (hf : Measurable f) (i n : ℕ) (z : KineticPhase) :
    finiteGainChain a K weight f i n z = ∑ labels : Fin n → I,
      chosenGainChain a K weight f i n labels z := by
  classical
  induction n generalizing i z with
  | zero => simp only [finiteGainChain,chosenGainChain,Finset.sum_const,Finset.card_univ,
      Fintype.card_fun,Fintype.card_fin,pow_zero,one_smul]
  | succ n ih =>
    have ht : (∑ labels : Fin (n+1) → I, chosenGainChain a K weight f i (n+1) labels z) =
        ∑ j : I, ∑ labels : Fin n → I, step a (K i j) (fun y => weight i j y *
          chosenGainChain a K weight f (i+1) n labels y) z := by
      rw [← (Fin.consEquiv (fun _ : Fin (n+1) => I)).sum_comp,Fintype.sum_prod_type]
      change (∑ j : I, ∑ labels : Fin n → I,
        chosenGainChain a K weight f i (n+1) (Fin.cons j labels) z) = _
      simp only [chosenGainChain,Fin.cons_zero,Fin.tail_cons]
    rw [ht]
    apply Finset.sum_congr rfl
    intro j _
    have hfuns : (fun y => weight i j y * finiteGainChain a K weight f (i+1) n y) =
        fun y => ∑ labels : Fin n → I, weight i j y * chosenGainChain a K weight f (i+1) n labels y := by
      funext y
      rw [ih,Finset.mul_sum]
    change step a (K i j) _ z = _
    rw [hfuns]
    exact congrFun (step_finset_sum Finset.univ a (K i j)
      (fun labels y => weight i j y * chosenGainChain a K weight f (i+1) n labels y)
      (fun labels _ => (hw i j).mul
        (chosenGainChain_measurable a K hw hf (i+1) n labels))) z

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # A finite chain depends only on its actual collision-stage weights -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.PositiveIteration

theorem finiteGainChain_congr_weights {I : Type*} [Fintype I] (a : ℝ)
    (K : ℕ → I → Kernel Published.KineticPhase Velocity)
    (w w' : ℕ → I → Published.KineticPhase → ℝ≥0∞)
    (f : Published.KineticPhase → ℝ≥0∞) (i n : ℕ) :
    (∀ k, i ≤ k → k < i+n → w k = w' k) → ∀ z,
      finiteGainChain a K w f i n z = finiteGainChain a K w' f i n z := by
  induction n generalizing i with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro h z
    have hi : w i = w' i := h i le_rfl (by omega)
    have ht : ∀ k, i+1 ≤ k → k < (i+1)+n → w k = w' k := by
      intro k hk hkn
      exact h k (by omega) (by omega)
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (fun g => step a (K i j) g z)
    funext y
    rw [hi,ih (i+1) ht y]

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # Finite physical thermal families expand into the actual weighted chains -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCoreSheet

instance thermalKernelFamily_sFinite {I : Type*} (r η K α γ q : ℝ)
    (μ d : ℕ → I → ℝ) (colors : ℕ → I → Bool) (i : ℕ) (j : I) :
    IsSFiniteKernel (thermalKernelFamily r η K α γ q μ d colors i j) := by
  unfold thermalKernelFamily
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem chosenThermalChain_eq_weighted {I : Type*} (r η K α γ q a : ℝ)
    (μ d : ℕ → I → ℝ) (colors : ℕ → I → Bool)
    (weight : ℕ → I → Published.KineticPhase → ℝ≥0∞)
    (f : Published.KineticPhase → ℝ≥0∞) (labels : ℕ → I) (i n : ℕ) :
    chosenGainChain a (thermalKernelFamily r η K α γ q μ d colors) weight f i n
      (fun j => labels (i+j.val)) =
      weightedCoreChain r η K α γ q a (fun i => μ i (labels i)) (fun i => d i (labels i))
        (fun i => colors i (labels i)) (fun i => weight i (labels i)) f i n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp only [chosenGainChain,weightedCoreChain]
    have htail : Fin.tail (fun j : Fin (n+1) => labels (i+j.val)) =
        (fun j : Fin n => labels ((i+1)+j.val)) := by
      funext j
      change labels (i+(j.val+1)) = labels ((i+1)+j.val)
      congr 1
      omega
    rw [htail,ih]
    rfl

theorem chosenThermalFive_eq_weighted {I : Type*} (r η K α γ q a : ℝ)
    (μ d : Fin 5 → I → ℝ) (colors : Fin 5 → I → Bool)
    (weight : Fin 5 → I → Published.KineticPhase → ℝ≥0∞)
    (f : Published.KineticPhase → ℝ≥0∞) (labels : Fin 5 → I) :
    chosenGainChain a
      (thermalKernelFamily r η K α γ q (cycleFive μ) (cycleFive d) (cycleFive colors))
      (cycleFive weight) f 0 5 labels =
      weightedCoreChain r η K α γ q a (cycleFive (fun i => μ i (labels i)))
        (cycleFive (fun i => d i (labels i))) (cycleFive (fun i => colors i (labels i)))
        (cycleFive (fun i => weight i (labels i))) f 0 5 := by
  have h := chosenThermalChain_eq_weighted r η K α γ q a
    (cycleFive μ) (cycleFive d) (cycleFive colors) (cycleFive weight) f (cycleFive labels) 0 5
  have he : (fun j : Fin 5 => cycleFive labels (0+j.val)) = labels := by
    funext j
    simpa only [Nat.zero_add] using cycleFive_apply labels j
  rw [he] at h
  exact h

theorem finiteThermalFive_eq_sum {I : Type*} [Fintype I] (r η K α γ q a : ℝ)
    (μ d : Fin 5 → I → ℝ) (colors : Fin 5 → I → Bool)
    (weight : Fin 5 → I → Published.KineticPhase → ℝ≥0∞)
    (hw : ∀ i j, Measurable (weight i j))
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (z : Published.KineticPhase) :
    finiteGainChain a
      (thermalKernelFamily r η K α γ q (cycleFive μ) (cycleFive d) (cycleFive colors))
      (cycleFive weight) f 0 5 z =
      ∑ labels : Fin 5 → I,
        weightedCoreChain r η K α γ q a (cycleFive (fun i => μ i (labels i)))
          (cycleFive (fun i => d i (labels i))) (cycleFive (fun i => colors i (labels i)))
          (cycleFive (fun i => weight i (labels i))) f 0 5 z := by
  rw [finiteGainChain_eq_sum (weight := cycleFive weight) a _ (fun _ j => hw _ j) hf]
  apply Finset.sum_congr rfl
  intro labels _
  exact congrFun (chosenThermalFive_eq_weighted r η K α γ q a μ d colors weight f labels) z

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Every fixed finite retained physical thermal family has vanishing fifth gain -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem finite_thermal_five_tendsto {I : Type*} [Fintype I]
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (colors : Fin 5 → I → Bool) (η : ℝ) (μ : Fin 5 → I → ℝ) (hμ : ∀ i j, 0 < μ i j)
    (μn dn : ℕ → Fin 5 → I → ℝ) (hμn : ∀ n i j, 0 < μn n i j)
    (hdn : ∀ n i j, 0 < dn n i j)
    (hμlim : ∀ i j, Tendsto (fun n => μn n i j) atTop (𝓝 (μ i j)))
    (hdlim : ∀ i j, Tendsto (fun n => dn n i j) atTop (𝓝 0))
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hinit : ∀ n, ‖WithLp.toLp 2 (states n).2.2‖ ≤ Vmax ∧
      b ≤ ‖transverse (WithLp.toLp 2 (states n).2.2)‖)
    (weight : ℕ → Fin 5 → I → Published.KineticPhase → ℝ≥0∞)
    (hwm : ∀ n i j, Measurable (weight n i j)) (hw : ∀ n i j z, weight n i j z ≤ 1)
    (hweight : ∀ n i j z, weight n i j z ≠ 0 →
      z.1.1 ∈ Icc a T ∧ ‖z.2‖ ≤ Vmax ∧ b ≤ ‖transverse z.2‖)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => finiteGainChain a
      (thermalKernelFamily (r n) η K α γ qexp (cycleFive (μn n)) (cycleFive (dn n))
        (cycleFive colors)) (cycleFive (weight n)) (g n) 0 5 (toKinetic (states n)))
      atTop (𝓝 0) := by
  classical
  have htuple (labels : Fin 5 → I) : Tendsto (fun n =>
      weightedCoreChain (r n) η K α γ qexp a (cycleFive (fun i => μn n i (labels i)))
        (cycleFive (fun i => dn n i (labels i))) (cycleFive (fun i => colors i (labels i)))
        (cycleFive (fun i => weight n i (labels i))) (g n) 0 5 (toKinetic (states n)))
      atTop (𝓝 0) := by
    let env : ℕ → PositiveEnvironment := fun n =>
      ⟨((fun i => μn n i (labels i)),(fun i => dn n i (labels i)),states n),
        fun i => hμn n i (labels i)⟩
    have henv : Tendsto env atTop
        (𝓝 (⟨((fun i => μ i (labels i)),0,(t₀,x,v)),fun i => hμ i (labels i)⟩ :
          PositiveEnvironment)) := by
      apply tendsto_subtype_rng.mpr
      exact (tendsto_pi_nhds.mpr (fun i => hμlim i (labels i))).prodMk_nhds
        ((tendsto_pi_nhds.mpr (fun i => hdlim i (labels i))).prodMk_nhds hstates)
    exact actual_weighted_five_tendsto hMityagin hK hα hγ hq ha hb hV
      (fun i => colors i (labels i)) η (fun i => hμ i (labels i)) t₀ x v hv henv r hr
      (fun n i => hdn n i (labels i)) hinit (fun n i => weight n i (labels i))
      (fun n i => hwm n i (labels i)) (fun n i => hw n i (labels i))
      (fun n i => hweight n i (labels i)) hM hg hgM hL
  have hs := tendsto_finsetSum (Finset.univ : Finset (Fin 5 → I)) (fun labels _ => htuple labels)
  simp only [Finset.sum_const_zero] at hs
  apply hs.congr'
  exact Eventually.of_forall (fun n => (finiteThermalFive_eq_sum (r n) η K α γ qexp a
    (μn n) (dn n) colors (weight n) (hwm n) (hg n) (toKinetic (states n))).symm)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_GeometricTwoCoreUniform
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The finite retained geometric mesh has vanishing fifth gain -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.GeometricMesh

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem geometric_thermal_five_tendsto
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax s₀ η d₀ θ : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ)
    (hq : 0 ≤ qexp) (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (hs₀ : 0 < s₀) (hη : 0 < η) (hd₀ : 0 < d₀) (hθ : 0 < θ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (J : Finset ℤ)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (hinit : ∀ n, ‖WithLp.toLp 2 (states n).2.2‖ ≤ Vmax ∧
      b ≤ ‖transverse (WithLp.toLp 2 (states n).2.2)‖)
    (weight : ℕ → Fin 5 → MeshLabel J → Published.KineticPhase → ℝ≥0∞)
    (hwm : ∀ n i j, Measurable (weight n i j)) (hw : ∀ n i j z, weight n i j z ≤ 1)
    (hweight : ∀ n i j z, weight n i j z ≠ 0 →
      z.1.1 ∈ Icc a T ∧ ‖z.2‖ ≤ Vmax ∧ b ≤ ‖transverse z.2‖)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {M : ℝ≥0∞}
    (hM : M ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgM : ∀ n z, g n z ≤ M)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => finiteGainChain a
      (thermalKernelFamily (r n) η K α γ qexp
        (fun _ j => meshScale s₀ η r n j/r n)
        (fun _ j => d₀*meshScale s₀ η r n j^10) (fun _ j => j.2))
      (cycleFive (weight n)) (g n) 0 5 (toKinetic (states n))) atTop (𝓝 0) := by
  have hs (n : ℕ) (j : MeshLabel J) : 0 < meshScale s₀ η r n j :=
    DatumBounds.scale_pos hs₀ _
  apply finite_thermal_five_tendsto hMityagin hK hα hγ hq ha hb hV
    (fun _ j => j.2) η (fun _ j => θ*Real.exp (η*(j.1.val:ℝ)))
    (fun _ _ => mul_pos hθ (Real.exp_pos _))
    (fun n _ j => meshScale s₀ η r n j/r n)
    (fun n _ j => d₀*meshScale s₀ η r n j^10)
    (fun n _ j => div_pos (hs n j) (hr n))
    (fun n _ j => mul_pos hd₀ (pow_pos (hs n j) 10))
    (fun _ j => jet_scale_approximation hs₀ hη hr hrlim hphase j.1.val)
    (fun _ j => mesh_width_tendsto_zero hs₀ hη hr hrlim hphase d₀ j.1.val)
    t₀ x v hv states hstates r hr hinit weight hwm hw hweight hM hg hgM hL

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_SelectedLargeOutput
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual selected-kernel velocity tails and large-scale truncation -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

instance retainedFreeKernel_sFinite (r s₀ η K α γ d₀ q M : ℝ) (N : ℕ) :
    IsSFiniteKernel (retainedFreeKernel r s₀ η K α γ d₀ q M N) := by
  unfold retainedFreeKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

instance discardedFreeKernel_sFinite (r s₀ η K α γ d₀ q M : ℝ) (N : ℕ) :
    IsSFiniteKernel (discardedFreeKernel r s₀ η K α γ d₀ q M N) := by
  unfold discardedFreeKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_OriginMeshStep
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual selected kernel restricted to one origin and a compact scale window -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

instance originScaleKernel_sFinite (r s₀ η K α γ d₀ q δ M : ℝ) (N : ℕ) (k : Lattice) :
    IsSFiniteKernel (originScaleKernel r s₀ η K α γ d₀ q δ M N k) := by
  unfold originScaleKernel
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem originScaleKernel_eq_copy {r s₀ η K α γ d₀ q δ M : ℝ} {N : ℕ} {k : Lattice}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    {i : Label} {z : Published.KineticPhase} (hi : z.1 ∈ mainCoreRegion s₀ η r N i)
    (hk : i.lattice = k) (hlo : δ ≤ JetGeometry.jetScale s₀ η i.annulus/r)
    (hhi : JetGeometry.jetScale s₀ η i.annulus/r ≤ M) :
    originScaleKernel r s₀ η K α γ d₀ q δ M N k z = copyFreeKernel r s₀ η K α γ d₀ q i z := by
  classical
  have hz : z.1 ∈ originScaleRegion s₀ η r δ M N k :=
    mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨⟨hk,hlo,hhi⟩,hi⟩⟩
  simp only [originScaleKernel,Kernel.piecewise_apply,mem_preimage,hz,ite_true, if_true]
  exact selectedFreeKernel_eq_copy hs₀ hsmax hη hηmax hi

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Exact finite mesh labels for the selected origin and scale window -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.GeometricMesh
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem meshLabelRegion_measurable (s₀ η δ M : ℝ) (r : ℕ → ℝ) (N : ℕ) {J : Finset ℤ}
    (n : ℕ) (j : MeshLabel J) : MeasurableSet (meshLabelRegion s₀ η δ M r N n j) := by
  unfold meshLabelRegion
  have hc (p : Prop) : MeasurableSet {_z : Published.KineticPhase | p} := by
    by_cases h : p <;> simp [h]
  exact (hc _).inter ((hc _).inter
    ((hc _).inter ((measurableSet_mainCoreRegion s₀ η (r n) N _).preimage measurable_fst)))

theorem meshLabelRegion_originScale {s₀ η δ M : ℝ} {r : ℕ → ℝ} {N : ℕ} {J : Finset ℤ}
    {n : ℕ} {j : MeshLabel J} {z : Published.KineticPhase}
    (h : z ∈ meshLabelRegion s₀ η δ M r N n j) :
    z.1 ∈ originScaleRegion s₀ η (r n) δ M N 0 :=
  mem_iUnion.mpr ⟨meshLabel s₀ η r n j,mem_iUnion.mpr ⟨⟨rfl,h.2.1,h.2.2.1⟩,h.2.2.2⟩⟩

theorem meshLabelRegion_disjoint {s₀ η δ M : ℝ} {r : ℕ → ℝ} {N : ℕ} {J : Finset ℤ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    {n : ℕ} {j k : MeshLabel J} {z : Published.KineticPhase}
    (hj : z ∈ meshLabelRegion s₀ η δ M r N n j)
    (hk : z ∈ meshLabelRegion s₀ η δ M r N n k) : j = k := by
  have he := mainCoreRegion_unique hs₀ hsmax hη hηmax hj.2.2.2 hk.2.2.2
  apply Prod.ext
  · apply Subtype.ext
    exact hj.1.symm.trans ((congrArg (fun i : Label => jetMeshIndex s₀ η (r n) i.annulus) he).trans hk.1)
  · exact congrArg Label.positive he

theorem originScale_mem_meshLabel {s₀ η δ M : ℝ} {r : ℕ → ℝ} {N : ℕ} {n : ℕ}
    (hs₀ : 0 < s₀) (hη : 0 < η) (hr : 0 < r n) (hδ : 0 < δ)
    {z : Published.KineticPhase} (hz : z.1 ∈ originScaleRegion s₀ η (r n) δ M N 0) :
    ∃ j : MeshLabel (windowMesh η δ M), z ∈ meshLabelRegion s₀ η δ M r N n j := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp hz
  obtain ⟨h,hi⟩ := mem_iUnion.mp hi
  have hwin : jetMeshIndex s₀ η (r n) i.annulus ∈ windowMesh η δ M := by
    have hs := h.2
    rw [jetScale_ratio_exact hs₀ hr hη] at hs
    exact Finset.mem_Icc.mpr (point_window (phase_bounds hη _).1 (phase_bounds hη _).2
      hη hδ hs.1 hs.2)
  let j : MeshLabel (windowMesh η δ M) := ⟨⟨jetMeshIndex s₀ η (r n) i.annulus,hwin⟩,i.positive⟩
  have he : meshLabel s₀ η r n j = i := by
    change Label.mk (jetIndex s₀ η r (jetMeshIndex s₀ η (r n) i.annulus) n) i.positive 0 = i
    rw [jetIndex_at_meshIndex]
    cases i
    congr
    exact h.1.symm
  have hscale : meshScale s₀ η r n j = JetGeometry.jetScale s₀ η i.annulus :=
    congrArg (fun l : Label => JetGeometry.jetScale s₀ η l.annulus) he
  refine ⟨j,?_⟩
  change jetMeshIndex s₀ η (r n) (meshLabel s₀ η r n j).annulus = j.1.val ∧ _
  rw [he,hscale]
  exact ⟨rfl,h.2.1,h.2.2,hi⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The fixed-origin selected kernel is exactly a finite sum of physical cores -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetLattice
open BoltzmannNonuniqueness.JetCoreSheet

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem copy_meshLabel_eq {s₀ η K α γ d₀ q : ℝ} {r : ℕ → ℝ}
    {J : Finset ℤ} (n : ℕ) (j : MeshLabel J) (z : Published.KineticPhase) :
    copyFreeKernel (r n) s₀ η K α γ d₀ q (meshLabel s₀ η r n j) z =
      dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
        (d₀*meshScale s₀ η r n j^10) q j.2 z := by
  have h0 : latticeVector (0 : Lattice) = 0 := by
    simp [latticeVector]
    rfl
  rw [copyFreeKernel_eq]
  simp only [meshLabel,h0,smul_zero,sub_zero]
  rfl

theorem originScale_lintegral_eq_mesh_sum {s₀ η K α γ d₀ q δ M : ℝ}
    {r : ℕ → ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (n : ℕ) (hr : 0 < r n) (hδ : 0 < δ) (N : ℕ)
    (z : Published.KineticPhase) (f : Velocity → ℝ≥0∞) :
    (∫⁻ v, f v ∂originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0 z) =
      ∑ j : MeshLabel (windowMesh η δ M),
        (meshLabelRegion s₀ η δ M r N n j).indicator (fun y =>
          ∫⁻ v, f v ∂dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
            (d₀*meshScale s₀ η r n j^10) q j.2 y) z := by
  classical
  by_cases hz : z.1 ∈ originScaleRegion s₀ η (r n) δ M N 0
  · obtain ⟨j,hj⟩ := originScale_mem_meshLabel hs₀ hη hr hδ hz
    rw [Finset.sum_eq_single j]
    · rw [indicator_of_mem hj]
      have he := originScaleKernel_eq_copy (K := K) (α := α) (γ := γ) (d₀ := d₀) (q := q) hs₀ hsmax hη hηmax hj.2.2.2
        (show (meshLabel s₀ η r n j).lattice = 0 from rfl) hj.2.1 hj.2.2.1
      rw [he,copy_meshLabel_eq]
    · intro k _ hkj
      apply indicator_of_notMem
      intro hk
      exact hkj (meshLabelRegion_disjoint hs₀ hsmax hη hηmax hk hj)
    · simp
  · have hk : originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0 z = 0 := by
      simp [originScaleKernel,ProbabilityTheory.Kernel.piecewise_apply,hz]
    rw [hk,lintegral_zero_measure]
    symm
    apply Finset.sum_eq_zero
    intro j _
    exact indicator_of_notMem (fun hj => hz (meshLabelRegion_originScale hj)) _

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The selected fixed-origin step equals the finite masked physical-core step -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem meshRegion_lintegral_indicator (s₀ η δ M : ℝ) (r : ℕ → ℝ) (N n : ℕ)
    {J : Finset ℤ} (j : MeshLabel J) (z : Published.KineticPhase)
    (μ : Measure Velocity) (f : Published.KineticPhase → ℝ≥0∞) :
    (∫⁻ v, (meshLabelRegion s₀ η δ M r N n j).indicator f (z.1,v) ∂μ) =
      (meshLabelRegion s₀ η δ M r N n j).indicator (fun _ => ∫⁻ v, f (z.1,v) ∂μ) z := by
  classical
  have hm (v : Velocity) : (z.1,v) ∈ meshLabelRegion s₀ η δ M r N n j ↔
      z ∈ meshLabelRegion s₀ η δ M r N n j := Iff.rfl
  by_cases hz : z ∈ meshLabelRegion s₀ η δ M r N n j
  · rw [indicator_of_mem hz]
    apply lintegral_congr
    intro v
    exact indicator_of_mem ((hm v).mpr hz) f
  · rw [indicator_of_notMem hz]
    have hzero : (fun v => (meshLabelRegion s₀ η δ M r N n j).indicator f (z.1,v)) = fun _ => 0 := by
      funext v
      exact indicator_of_notMem ((not_congr (hm v)).mpr hz) f
    rw [hzero,lintegral_zero]

theorem originScale_step_eq_mesh_sum {s₀ η K α γ d₀ q δ M : ℝ}
    {r : ℕ → ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (n : ℕ) (hr : 0 < r n) (hδ : 0 < δ) (N : ℕ) (a : ℝ)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (z : Published.KineticPhase) :
    step a (originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0) f z =
      ∑ j : MeshLabel (windowMesh η δ M),
        step a (dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
          (d₀*meshScale s₀ η r n j^10) q j.2)
          ((meshLabelRegion s₀ η δ M r N n j).indicator f) z := by
  let F (j : MeshLabel (windowMesh η δ M)) (s : ℝ) : ℝ≥0∞ :=
    ∫⁻ v, (meshLabelRegion s₀ η δ M r N n j).indicator f ((flight z s).1,v)
      ∂dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
        (d₀*meshScale s₀ η r n j^10) q j.2 (flight z s)
  have hF (j : MeshLabel (windowMesh η δ M)) : Measurable (F j) :=
    step_inner_measurable _ (hf.indicator (meshLabelRegion_measurable s₀ η δ M r N n j)) z
  have he (s : ℝ) :
      (∫⁻ v, f ((flight z s).1,v)
        ∂originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0 (flight z s)) =
          ∑ j : MeshLabel (windowMesh η δ M), F j s := by
    rw [originScale_lintegral_eq_mesh_sum hs₀ hsmax hη hηmax n hr hδ N]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [F]
    rw [meshRegion_lintegral_indicator]
    by_cases hj : flight z s ∈ meshLabelRegion s₀ η δ M r N n j
    · simp only [indicator_of_mem hj]
    · simp only [indicator_of_notMem hj]
  unfold step
  simp_rw [he]
  exact lintegral_finsetSum _ (fun j _ => hF j)

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedMeshStep
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual spatial and velocity masks for the finite mesh representation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem boundedMeshWeight_measurable (s₀ η δ M a T : ℝ) (r : ℕ → ℝ) (N n : ℕ)
    {J : Finset ℤ} {S : Set Velocity} (hS : MeasurableSet S) (j : MeshLabel J) :
    Measurable (boundedMeshWeight s₀ η δ M a T r N n S j) := by
  apply measurable_const.indicator
  exact (meshLabelRegion_measurable s₀ η δ M r N n j).inter
    ((measurableSet_Icc.preimage (by fun_prop)).inter (hS.preimage measurable_snd))

theorem boundedMeshWeight_le_one (s₀ η δ M a T : ℝ) (r : ℕ → ℝ) (N n : ℕ)
    {J : Finset ℤ} (S : Set Velocity) (j : MeshLabel J) (z : Published.KineticPhase) :
    boundedMeshWeight s₀ η δ M a T r N n S j z ≤ 1 := by
  classical
  by_cases h : z ∈ meshLabelRegion s₀ η δ M r N n j ∩ {z | z.1.1 ∈ Icc a T ∧ z.2 ∈ S}
  · simp only [boundedMeshWeight,indicator_of_mem h,le_refl]
  · simp only [boundedMeshWeight,indicator_of_notMem h]
    exact zero_le

theorem boundedMeshWeight_support {s₀ η δ M a T V b : ℝ} {r : ℕ → ℝ} {N n : ℕ}
    {J : Finset ℤ} {S : Set Velocity}
    (hS : ∀ v, v ∈ S → ‖v‖ ≤ V ∧ b ≤ ‖VelocityWeight.transverse v‖)
    (j : MeshLabel J) (z : Published.KineticPhase)
    (hz : boundedMeshWeight s₀ η δ M a T r N n S j z ≠ 0) :
    z.1.1 ∈ Icc a T ∧ ‖z.2‖ ≤ V ∧ b ≤ ‖VelocityWeight.transverse z.2‖ := by
  have hm : z ∈ meshLabelRegion s₀ η δ M r N n j ∩ {z | z.1.1 ∈ Icc a T ∧ z.2 ∈ S} := by
    by_contra h
    exact hz (indicator_of_notMem h _)
  exact ⟨hm.2.1,hS z.2 hm.2.2⟩

theorem boundedMeshWeight_mul {s₀ η δ M a T : ℝ} {r : ℕ → ℝ} {N n : ℕ}
    {J : Finset ℤ} (S : Set Velocity) (j : MeshLabel J)
    (f : Published.KineticPhase → ℝ≥0∞) {z : Published.KineticPhase}
    (hz : z.1.1 ∈ Icc a T) :
    boundedMeshWeight s₀ η δ M a T r N n S j z*f z =
      (meshLabelRegion s₀ η δ M r N n j).indicator ({y | y.2 ∈ S}.indicator f) z := by
  classical
  by_cases hR : z ∈ meshLabelRegion s₀ η δ M r N n j
  · by_cases hS : z.2 ∈ S
    · have hm : z ∈ meshLabelRegion s₀ η δ M r N n j ∩
        {z | z.1.1 ∈ Icc a T ∧ z.2 ∈ S} := ⟨hR,hz,hS⟩
      simp only [boundedMeshWeight,indicator_of_mem hm,one_mul,indicator_of_mem hR,
        indicator_of_mem (show z ∈ {y : Published.KineticPhase | y.2 ∈ S} from hS)]
    · simp [boundedMeshWeight,hR,hS]
  · simp [boundedMeshWeight,hR]

end BoltzmannNonuniqueness.JetCopyDatum

namespace BoltzmannNonuniqueness.PositiveIteration

theorem step_restrict_eq_indicator (a : ℝ) (K : ProbabilityTheory.Kernel Published.KineticPhase Velocity)
    {S : Set Velocity} (hS : MeasurableSet S) (f : Published.KineticPhase → ℝ≥0∞) :
    step a (K.restrict hS) f = step a K ({y | y.2 ∈ S}.indicator f) := by
  funext z
  apply lintegral_congr
  intro s
  change (∫⁻ v in S, f ((flight z s).1,v) ∂K (flight z s)) = _
  rw [← lintegral_indicator hS]
  rfl

end BoltzmannNonuniqueness.PositiveIteration

end

end

section

/-! # The restricted selected step has the exact bounded mesh weights -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem originScale_restricted_step_eq {s₀ η K α γ d₀ q δ M a T : ℝ}
    {r : ℕ → ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (n : ℕ) (hr : 0 < r n) (hδ : 0 < δ) (N : ℕ)
    {S : Set Velocity} (hS : MeasurableSet S)
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f)
    {z : Published.KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    step a ((originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0).restrict hS) f z =
      ∑ j : MeshLabel (windowMesh η δ M),
        step a (dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
          (d₀*meshScale s₀ η r n j^10) q j.2)
          (fun y => boundedMeshWeight s₀ η δ M a T r N n S j y*f y) z := by
  rw [step_restrict_eq_indicator]
  rw [originScale_step_eq_mesh_sum (K := K) (α := α) (γ := γ) (d₀ := d₀) (q := q)
    (M := M) (f := {y : Published.KineticPhase | y.2 ∈ S}.indicator f) hs₀ hsmax hη hηmax n hr hδ N a
    (hf.indicator (hS.preimage measurable_snd)) z]
  apply Finset.sum_congr rfl
  intro j _
  apply le_antisymm
  · apply step_slab_mono _ _ hz
    intro y hy
    exact (boundedMeshWeight_mul S j f hy).ge
  · apply step_slab_mono _ _ hz
    intro y hy
    exact (boundedMeshWeight_mul S j f hy).le

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_OriginMeshLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Exact finite mesh representation of the restricted fixed-origin gain chain -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.PositiveIteration

theorem finiteGainChain_measurable {I : Type*} [Fintype I] (a : ℝ)
    (K : ℕ → I → Kernel Published.KineticPhase Velocity) [∀ i j, IsSFiniteKernel (K i j)]
    {weight : ℕ → I → Published.KineticPhase → ℝ≥0∞}
    (hw : ∀ i j, Measurable (weight i j)) {f : Published.KineticPhase → ℝ≥0∞}
    (hf : Measurable f) (i n : ℕ) : Measurable (finiteGainChain a K weight f i n) := by
  induction n generalizing i with
  | zero => exact hf
  | succ n ih =>
    exact Finset.measurable_sum _ (fun j _ => step_measurable a (K i j)
      ((hw i j).mul (ih (i+1))))

theorem step_slab_congr {a T : ℝ} (K : Kernel Published.KineticPhase Velocity)
    {f g : Published.KineticPhase → ℝ≥0∞}
    (h : ∀ y, y.1.1 ∈ Icc a T → f y = g y)
    {z : Published.KineticPhase} (hz : z.1.1 ∈ Icc a T) : step a K f z = step a K g z :=
  le_antisymm (step_slab_mono K (fun y hy => (h y hy).le) hz)
    (step_slab_mono K (fun y hy => (h y hy).ge) hz)

end BoltzmannNonuniqueness.PositiveIteration

namespace BoltzmannNonuniqueness.JetCopyDatum

instance meshFamily_sFinite (s₀ η K α γ d₀ q : ℝ) (r : ℕ → ℝ) {J : Finset ℤ}
    (n i : ℕ) (j : MeshLabel J) : IsSFiniteKernel (meshFamily s₀ η K α γ d₀ q r n i j) := by
  unfold meshFamily
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem meshFamily_apply {s₀ η K α γ d₀ q : ℝ} {r : ℕ → ℝ} {J : Finset ℤ}
    (n : ℕ) (hr : 0 < r n) (i : ℕ) (j : MeshLabel J) :
    meshFamily s₀ η K α γ d₀ q r n i j =
      dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
        (d₀*meshScale s₀ η r n j^10) q j.2 := by
  unfold meshFamily thermalKernelFamily
  congr 1
  field_simp [(hr).ne']

theorem originScale_chain_eq_mesh {s₀ η K α γ d₀ q δ M a T : ℝ}
    {r : ℕ → ℝ} (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (hηmax : η ≤ Real.log 2) (n : ℕ) (hr : 0 < r n) (hδ : 0 < δ) (N : ℕ)
    (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    {f : Published.KineticPhase → ℝ≥0∞} (hf : Measurable f) (i m : ℕ)
    {z : Published.KineticPhase} (hz : z.1.1 ∈ Icc a T) :
    restrictedChain a (originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0) S hS f i m z =
      finiteGainChain a (meshFamily s₀ η K α γ d₀ q r n)
        (meshWeights s₀ η δ M a T r N n S) f i m z := by
  have hwm (i : ℕ) (j : MeshLabel (windowMesh η δ M)) :
      Measurable (meshWeights s₀ η δ M a T r N n S i j) :=
    boundedMeshWeight_measurable s₀ η δ M a T r N n (hS (i+1)) j
  induction m generalizing i z with
  | zero => rfl
  | succ m ih =>
    let f' := finiteGainChain a (meshFamily s₀ η K α γ d₀ q r n)
      (meshWeights s₀ η δ M a T r N n S) f (i+1) m
    have hfm : Measurable f' := finiteGainChain_measurable a _ hwm hf (i+1) m
    calc
      _ = step a ((originScaleKernel (r n) s₀ η K α γ d₀ q δ M N 0).restrict (hS (i+1))) f' z := by
        apply step_slab_congr _ _ hz
        intro y hy
        exact ih (i+1) hy
      _ = ∑ j : MeshLabel (windowMesh η δ M),
          step a (dilatedFreeKernel (r n) η K α γ (meshScale s₀ η r n j)
            (d₀*meshScale s₀ η r n j^10) q j.2)
            (fun y => boundedMeshWeight s₀ η δ M a T r N n (S (i+1)) j y*f' y) z :=
        originScale_restricted_step_eq hs₀ hsmax hη hηmax n hr hδ N (hS (i+1)) hfm hz
      _ = _ := by
        change _ = ∑ j : MeshLabel (windowMesh η δ M), step a _ _ z
        apply Finset.sum_congr rfl
        intro j _
        rw [meshFamily_apply n hr]
        rfl

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Vanishing of the actual selected fifth gain at a fixed origin and compact scales -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.FiveGainMap
open BoltzmannNonuniqueness.PositiveIteration
open BoltzmannNonuniqueness.JetCoreSheet
open BoltzmannNonuniqueness.GeometricMesh
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem origin_scale_five_tendsto_q80_oai
    (hMityagin : Published.Mityagin2020FiveGainParameters)
    {K α γ qexp a T b Vmax s₀ η d₀ θ δ M : ℝ}
    (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hq : 0 ≤ qexp)
    (ha : 0 < a) (hb : 0 < b) (hV : 0 ≤ Vmax)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hd₀ : 0 < d₀) (hθ : 0 < θ) (hδ : 0 < δ)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hphase : Tendsto (fun n => phase (s₀/r n) η) atTop (𝓝 θ)) (N : ℕ → ℕ)
    (t₀ : ℝ) (x v : V) (hv : 0 < v 0^2+v 1^2)
    (states : ℕ → State) (hstates : Tendsto states atTop (𝓝 (t₀,x,v)))
    (htime : ∀ n, (states n).1 ∈ Icc a T)
    (S : ℕ → Set Velocity) (hS : ∀ i, MeasurableSet (S i))
    (hbound : ∀ i w, w ∈ S i → ‖w‖ ≤ Vmax ∧ b ≤ ‖transverse w‖)
    (hinit : ∀ n, WithLp.toLp 2 (states n).2.2 ∈ S 0)
    {g : ℕ → Published.KineticPhase → ℝ≥0∞} {B : ℝ≥0∞}
    (hB : B ≠ ∞) (hg : ∀ n, Measurable (g n)) (hgB : ∀ n z, g n z ≤ B)
    (hL : ∀ C : Set Published.KineticPhase, IsCompact C →
      Tendsto (fun n => ∫⁻ z in C, g n z) atTop (𝓝 0)) :
    Tendsto (fun n => restrictedChain a
      (originScaleKernel (r n) s₀ η K α γ d₀ qexp δ M (N n) 0)
      S hS (g n) 0 5 (toKinetic (states n))) atTop (𝓝 0) := by
  let weights : ℕ → Fin 5 → MeshLabel (windowMesh η δ M) → Published.KineticPhase → ℝ≥0∞ :=
    fun n i => boundedMeshWeight s₀ η δ M a T r (N n) n (S (i.val+1))
  have hlim := geometric_thermal_five_tendsto hMityagin hK hα hγ hq ha hb hV
    hs₀ hη hd₀ hθ r hr hrlim hphase (windowMesh η δ M) t₀ x v hv states hstates
    (fun n => hbound 0 _ (hinit n)) weights
    (fun n i j => boundedMeshWeight_measurable s₀ η δ M a T r (N n) n (hS (i.val+1)) j)
    (fun n i j z => boundedMeshWeight_le_one s₀ η δ M a T r (N n) n (S (i.val+1)) j z)
    (fun n i j z hz => boundedMeshWeight_support (hbound (i.val+1)) j z hz) hB hg hgB hL
  apply hlim.congr'
  apply Eventually.of_forall
  intro n
  have he := originScale_chain_eq_mesh (K := K) (α := α) (γ := γ) (d₀ := d₀)
    (q := qexp) (M := M) (a := a) (T := T) (z := toKinetic (states n)) hs₀ hsmax hη hηmax n (hr n) hδ (N n) S hS
    (hg n) 0 5 (htime n)
  have hw : ∀ k, 0 ≤ k → k < 0+5 →
      meshWeights s₀ η δ M a T r (N n) n S k = cycleFive (weights n) k := by
    intro k _ hk
    have hk' : k < 5 := by omega
    rw [show cycleFive (weights n) k = weights n ⟨k,hk'⟩ from cycleFive_apply (weights n) ⟨k,hk'⟩]
    rfl
  have he' := finiteGainChain_congr_weights a (meshFamily s₀ η K α γ d₀ qexp r n)
    _ _ (g n) 0 5 hw (toKinetic (states n))
  exact (he.trans he').symm

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.JetCopyDatum.origin_scale_five_tendsto_q80_oai := @OAI.BoltzmannNonuniqueness.JetCopyDatum.origin_scale_five_tendsto_q80_oai
