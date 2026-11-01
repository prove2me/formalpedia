-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.MildCollisionSolution.localAdmissible_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T19:58:59.996553+00:00
-- url     : https://prove2.me/submissions/8a023131-8fed-4f33-bdef-6eaad9389bc6

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
/-- Mathlib d13f23b's `LipschitzOnWith.comp_absolutelyContinuousOnInterval`: a Lipschitz function of an
absolutely continuous one is absolutely continuous (Boltzmann EntropyIntegralBalance and JetSupersolutions,
oaiq-080). -/
theorem _root_.LipschitzOnWith.comp_absolutelyContinuousOnInterval {g f : ℝ → ℝ} {s : Set ℝ} {K : NNReal}
    {a b : ℝ} (hg : LipschitzOnWith K g s) (hmaps : ∀ t ∈ Set.uIcc a b, f t ∈ s)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => g (f t)) a b := by
  have h0 := hf
  unfold AbsolutelyContinuousOnInterval at h0 ⊢
  have h1 := h0.const_mul (K : ℝ)
  rw [mul_zero] at h1
  refine squeeze_zero' ?_ ?_ h1
  · exact Filter.Eventually.of_forall (fun E => Finset.sum_nonneg (fun i _ => dist_nonneg))
  · refine Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall (fun E hE => ?_))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' := hE.left i hi
    have := hg (hmaps _ hi'.left) (hmaps _ hi'.right)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (edist_ne_top _ _)) this
    rwa [ENNReal.toReal_mul, ← dist_edist, ← dist_edist, ENNReal.coe_toReal] at h2
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Model
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.sphereArea_isFiniteMeasure _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collision model for periodic hard spheres

The normal parametrization and absolute angular kernel here are exactly those of
Sections 1–2 of the paper.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem scatter_momentum (v w ω : Velocity) :
    scatterLeft v w ω + scatterRight v w ω = v + w := by
  unfold scatterLeft scatterRight
  abel

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Admissibility
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.sphereArea_isFiniteMeasure _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The entropy-class solution and nonuniqueness statement

The solution class follows Definition 2.1 with explicit integrability conditions.
The renormalized equation uses derivatives of smooth periodic lifts, while
integrals use volume on the unit torus and Euclidean velocity space.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem torusProjection_representative (x : Position) :
    torusProjection (torusRepresentative x) = x := by
  funext i
  exact AddCircle.coe_equivIco

theorem maxwellian_pos (v : Velocity) : 0 < maxwellian v := by
  unfold maxwellian
  positivity

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionMeasure
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_Moments
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.sphereArea_isFiniteMeasure _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integrable moments of finite-entropy data

The weighted entropy assumption from the manuscript controls mass, kinetic
energy, absolute entropy, and vector momentum. These conclusions use the actual
integrability assumption rather than any default value of a Bochner integral.
-/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem entropyMoment_nonneg {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    0 ≤ entropyMoment f z := by
  unfold entropyMoment
  positivity

theorem density_le_entropyMoment {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    f z ≤ entropyMoment f z := by
  unfold entropyMoment
  nlinarith [mul_nonneg hf (sq_nonneg ‖z.2‖),
    mul_nonneg hf (abs_nonneg (Real.log (f z)))]

theorem energyDensity_le_entropyMoment {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    ‖z.2‖ ^ 2 * f z ≤ entropyMoment f z := by
  unfold entropyMoment
  nlinarith [mul_nonneg hf (abs_nonneg (Real.log (f z)))]

theorem absEntropyDensity_le_entropyMoment {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    f z * |Real.log (f z)| ≤ entropyMoment f z := by
  unfold entropyMoment
  nlinarith [mul_nonneg hf (sq_nonneg ‖z.2‖)]

theorem momentumDensity_norm_le_entropyMoment {f : Density} {z : Phase} (hf : 0 ≤ f z) :
    ‖f z • z.2‖ ≤ entropyMoment f z := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hf]
  unfold entropyMoment
  apply mul_le_mul_of_nonneg_left _ hf
  nlinarith [sq_nonneg (‖z.2‖ - 1), abs_nonneg (Real.log (f z))]

namespace FiniteEntropyDatum

variable {f : Density} (hf : FiniteEntropyDatum f)

include hf

/-- Finite weighted entropy gives finite mass. -/
theorem integrable : Integrable f := by
  apply hf.2.2.mono' hf.2.1
  filter_upwards [hf.1] with z hz
  simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using density_le_entropyMoment hz

/-- The energy functional integrates an integrable density. -/
theorem integrable_energy : Integrable (fun z => ‖z.2‖ ^ 2 * f z) := by
  have hm : AEStronglyMeasurable (fun z : Phase => ‖z.2‖ ^ 2) := by fun_prop
  apply hf.2.2.mono' (hm.mul hf.2.1)
  filter_upwards [hf.1] with z hz
  rw [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hz)]
  exact energyDensity_le_entropyMoment hz

/-- This is absolute entropy, including the convention at zero from the model. -/
theorem integrable_absEntropy : Integrable (fun z => f z * |Real.log (f z)|) := by
  have hlog : AEStronglyMeasurable (fun z => Real.log (f z)) :=
    hf.2.1.aemeasurable.log.aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun z => f z * |Real.log (f z)|) := by
    simpa only [Pi.mul_def, Real.norm_eq_abs] using hf.2.1.mul hlog.norm
  apply hf.2.2.mono' hm
  filter_upwards [hf.1] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hz (abs_nonneg _))]
  exact absEntropyDensity_le_entropyMoment hz

/-- The vector momentum integral is a genuine Bochner integral. -/
theorem integrable_momentum : Integrable (fun z => f z • z.2) := by
  have hm : AEStronglyMeasurable (fun z : Phase => z.2) := by fun_prop
  apply hf.2.2.mono' (hf.2.1.smul hm)
  filter_upwards [hf.1] with z hz
  exact momentumDensity_norm_le_entropyMoment hz

theorem integrable_entropy : Integrable (fun z => f z * Real.log (f z)) := by
  have hlog : AEStronglyMeasurable (fun z => Real.log (f z)) :=
    hf.2.1.aemeasurable.log.aestronglyMeasurable
  apply hf.integrable_absEntropy.mono' (hf.2.1.mul hlog)
  filter_upwards [hf.1] with z hz
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hz, le_refl]

end FiniteEntropyDatum

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_KineticDensityMeasurable
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measure-preserving grouping of physical time and phase coordinates -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem kineticGrouping_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving (MeasurableEquiv.prodAssoc :
      ((ℝ × Position) × Velocity) ≃ᵐ ℝ × Phase)
      ((μ.prod volume).prod volume) (μ.prod volume) := by
  simpa only [Measure.volume_eq_prod] using measurePreserving_prodAssoc μ
    (volume : Measure Position) (volume : Measure Velocity)

theorem phaseInterval_measure (T : ℝ) :
    (volume.restrict (Icc 0 T)).prod (volume : Measure Phase) =
      volume.restrict (boundedTimes T) := by
  rw [Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod]
  rfl

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianEstimates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.MassTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.TorusFlight.flight_neg _root_.OAI.BoltzmannNonuniqueness.TorusFlight.flight_zero _root_.OAI.BoltzmannNonuniqueness.TorusFlight.neg_flight _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The Maxwellian reference entropy

Finite weighted absolute entropy makes the relative-entropy integral genuine.
Its nonnegativity is proved, including the zero-density convention.
-/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem log_maxwellian (v : Velocity) :
    Real.log (maxwellian v) = -(3 / 2 : ℝ) * Real.log (2 * Real.pi) - ‖v‖ ^ 2 / 2 := by
  have hp : 0 < (2 : ℝ) * Real.pi := by positivity
  rw [maxwellian, Real.log_mul (Real.rpow_pos_of_pos hp _).ne' (Real.exp_ne_zero _),
    Real.log_rpow hp, Real.log_exp]
  ring

theorem integrable_maxwellian : Integrable maxwellian := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (by norm_num : 0 < ((1 / 2 : ℂ)).re) 0 (0 : Velocity)).norm
  have hg : Integrable (fun v : Velocity => Real.exp (-‖v‖ ^ 2 / 2)) := by
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    funext v
    simp only [zero_mul, add_zero, Complex.norm_exp]
    congr 1
    norm_num
    norm_cast
    ring
  exact hg.const_mul _

theorem integrable_maxwellian_phase : Integrable (fun z : Phase => maxwellian z.2) :=
  integrable_maxwellian.comp_snd volume

theorem relativeEntropyDensity_eq {f : Density} {z : Phase} (hz : 0 ≤ f z) :
    f z * Real.log (f z / maxwellian z.2) - f z + maxwellian z.2 =
      f z * Real.log (f z) + ((3 / 2 : ℝ) * Real.log (2 * Real.pi) - 1) * f z +
        (1 / 2 : ℝ) * (‖z.2‖ ^ 2 * f z) + maxwellian z.2 := by
  rcases hz.eq_or_lt with hz | hz
  · simp [← hz]
  · rw [Real.log_div hz.ne' (maxwellian_pos _).ne', log_maxwellian]
    ring

theorem FiniteEntropyDatum.integrable_relativeEntropy {f : Density} (hf : FiniteEntropyDatum f) :
    Integrable (fun z => f z * Real.log (f z / maxwellian z.2) - f z + maxwellian z.2) := by
  have h := ((hf.integrable_entropy.add
    (hf.integrable.const_mul ((3 / 2 : ℝ) * Real.log (2 * Real.pi) - 1))).add
    (hf.integrable_energy.const_mul (1 / 2 : ℝ))).add integrable_maxwellian_phase
  apply h.congr
  filter_upwards [hf.1] with z hz
  exact (relativeEntropyDensity_eq hz).symm

/-- The scalar relative entropy is nonnegative at every nonnegative density value. -/
theorem relativeEntropyDensity_nonneg {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) :
    0 ≤ a * Real.log (a / m) - a + m := by
  rcases ha.eq_or_lt with ha | ha
  · simp [← ha, hm.le]
  · have h := Real.log_le_sub_one_of_pos (div_pos hm ha)
    have hlog : Real.log (m / a) = -Real.log (a / m) := by
      rw [Real.log_div hm.ne' ha.ne', Real.log_div ha.ne' hm.ne']
      ring
    rw [hlog] at h
    have hh := mul_le_mul_of_nonneg_left h ha.le
    have he : a * (m / a - 1) = m - a := by field_simp
    rw [he] at hh
    nlinarith only [hh]

theorem relativeEntropy_nonneg {f : Density} (hf : FiniteEntropyDatum f) :
    0 ≤ relativeEntropy f := by
  apply integral_nonneg_of_ae
  filter_upwards [hf.1] with z hz
  exact relativeEntropyDensity_nonneg hz (maxwellian_pos _)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyIntegralBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The regularized entropy primitive used at zeros of finite approximations -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem scalarRelativeEntropy_eq {m : ℝ} (hm : 0 < m) (f : ℝ) :
    scalarRelativeEntropy m f = f*Real.log (f/m)-f+m := by
  by_cases hf : f = 0
  · simp [scalarRelativeEntropy,hf]
  · rw [Real.log_div hf hm.ne']
    unfold scalarRelativeEntropy
    ring

end BoltzmannNonuniqueness

end

end

section

/-! # A regularization-independent integrable bound for relative entropy -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem scalarRelativeEntropy_nonneg {m u : ℝ} (hm : 0 < m) (hu : 0 ≤ u) :
    0 ≤ scalarRelativeEntropy m u := by
  rw [scalarRelativeEntropy_eq hm]
  exact relativeEntropyDensity_nonneg hu hm

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_ScalarEntropyConvex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded dual tests for relative entropy -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem entropyDual_le {m u : ℝ} (hm : 0 < m) (hu : 0 ≤ u) (s : ℝ) :
    entropyDual m u s ≤ scalarRelativeEntropy m u := by
  by_cases hz : u = 0
  · subst u
    dsimp [entropyDual,scalarRelativeEntropy]
    nlinarith [Real.exp_pos s]
  · have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
    have hr : 0 < u/m := div_pos hup hm
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (s-Real.log (u/m))) hu
    rw [Real.exp_sub,Real.exp_log hr] at h
    have he : u*(Real.exp s/(u/m)) = m*Real.exp s := by field_simp
    rw [he] at h
    rw [scalarRelativeEntropy_eq hm]
    dsimp [entropyDual]
    nlinarith only [h]

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_HalfGaussianMoment
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

end BoltzmannNonuniqueness.VelocityMoment

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityPolynomialBounds
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

end BoltzmannNonuniqueness.VelocityMoment

end

end

section

/-! # The polynomial factors required for collision energy integrability -/

noncomputable section

namespace BoltzmannNonuniqueness.VelocityMoment

theorem norm_sq_le_weight (v : Velocity) : ‖v‖^2 ≤ 2*weight v := by
  have h := Real.add_one_le_exp (‖v‖^2/2)
  change ‖v‖^2 ≤ 2*Real.exp (‖v‖^2/2)
  linarith

theorem norm_cube_le_weight (v : Velocity) : ‖v‖^3 ≤ 5*weight v := by
  have h := Real.pow_div_factorial_le_exp (‖v‖^2/2) (by positivity) 2
  norm_num at h
  have hs := norm_sq_le_weight v
  have he : ‖v‖^4 ≤ 8*weight v := by
    change ‖v‖^4 ≤ 8*Real.exp (‖v‖^2/2)
    nlinarith
  nlinarith [sq_nonneg (‖v‖^2-‖v‖)]

theorem norm_sq_kernel_le_weight (v w : Velocity) (ω : Sphere) :
    ‖v‖^2*collisionKernel v w ω ≤ 7*weight v*weight w := by
  have hk := (collisionKernel_le_norm v w ω).trans (norm_sub_le v w)
  have hcross : ‖v‖^2*‖w‖ ≤ (2*weight v)*weight w :=
    mul_le_mul (norm_sq_le_weight v) (norm_le_weight w) (norm_nonneg _)
      (mul_nonneg (by norm_num) (weight_pos v).le)
  have hleft : 5*weight v ≤ 5*weight v*weight w :=
    le_mul_of_one_le_right (mul_nonneg (by norm_num) (weight_pos v).le) (weight_one_le w)
  calc
    _ ≤ ‖v‖^2*(‖v‖+‖w‖) := mul_le_mul_of_nonneg_left hk (sq_nonneg _)
    _ = ‖v‖^3+‖v‖^2*‖w‖ := by ring
    _ ≤ 5*weight v+(2*weight v)*weight w := add_le_add (norm_cube_le_weight v) hcross
    _ ≤ _ := by nlinarith

end BoltzmannNonuniqueness.VelocityMoment

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionWeakMarginals
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measure preservation and integrability for the full hard-sphere collision rate -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem scatterTriple_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (scatterTriple (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  let ν := μ.prod (volume : Measure (Velocity × Velocity))
  have hf (ω : Sphere) : MeasurePreserving
      (fun p : X × (Velocity × Velocity) => (p.1,scatterPair ω p.2)) ν ν := by
    have hω : ‖(ω : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
    have hh := (MeasurePreserving.id μ).prod (scatterPair_measurePreserving (ω : Velocity) hω)
    have he : (Prod.map id (scatterPair (ω : Velocity))) =
        (fun p : X × (Velocity × Velocity) => (p.1,scatterPair ω p.2)) := by
      funext p
      rfl
    rw [he] at hh
    simpa only [ν,Measure.volume_eq_prod] using hh
  have hm : Measurable (fun z : Sphere × (X × (Velocity × Velocity)) =>
      (z.2.1,scatterPair z.1 z.2.2)) := by
    unfold scatterPair scatterLeft scatterRight normalComponent
    fun_prop
  have hh := (MeasurePreserving.id sphereArea).skew_product (μc := ν) (μd := ν)
    (g := fun (ω : Sphere) (p : X × (Velocity × Velocity)) => (p.1,scatterPair ω p.2)) hm
    (ae_of_all _ (fun ω => (hf ω).map_eq))
  have h₁ : MeasurePreserving Prod.swap (ν.prod sphereArea) (sphereArea.prod ν) :=
    Measure.measurePreserving_swap
  have h₂ : MeasurePreserving Prod.swap (sphereArea.prod ν) (ν.prod sphereArea) :=
    Measure.measurePreserving_swap
  exact h₂.comp (hh.comp h₁)


omit [MeasurableSpace X] in
theorem postRate_formula (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    postRate f z = collisionKernel z.1.2.1 z.1.2.2 z.2*
      f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) := by
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  change collisionKernel (scatterLeft z.1.2.1 z.1.2.2 z.2) (scatterRight z.1.2.1 z.1.2.2 z.2) z.2*
    f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) = _
  rw [collisionKernel_scatter _ _ _ hw]

theorem preRate_measurable {f : X × Velocity → ℝ} (hf : Measurable f) : Measurable (preRate f) := by
  unfold preRate collisionKernel normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem preRate_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : (X × (Velocity × Velocity)) × Sphere) : 0 ≤ preRate f z :=
  mul_nonneg (mul_nonneg (collisionKernel_nonneg _ _ _) (hf _)) (hf _)

omit [MeasurableSpace X] in
theorem preRate_le_pairDensity {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : (X × (Velocity × Velocity)) × Sphere) : preRate f z ≤ pairDensity f z.1 := by
  have hk : collisionKernel z.1.2.1 z.1.2.2 z.2 ≤ 1+‖z.1.2.1‖+‖z.1.2.2‖ :=
    (collisionKernel_le_norm _ _ _).trans ((norm_sub_le _ _).trans (by linarith))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (hf _)) (hf _)

theorem preRate_integrable {μ : Measure X} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (preRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  apply (hpair.comp_fst sphereArea).mono' (preRate_measurable hfm).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (preRate_nonneg hf z)]
  exact preRate_le_pairDensity hf z

theorem postRate_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (postRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (scatterTriple_measurePreserving μ).integrable_comp_of_integrable (preRate_integrable hfm hf hpair)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable physical gain and loss and their equal total mass -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem collisionGrouping_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (collisionGrouping (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) := by
  have ha := (measurePreserving_prodAssoc μ (volume : Measure Velocity) (volume : Measure Velocity)).symm.prod
    (MeasurePreserving.id sphereArea)
  have hb := measurePreserving_prodAssoc (μ.prod (volume : Measure Velocity))
    (volume : Measure Velocity) sphereArea
  have he : (⇑(collisionGrouping (X := X))) =
      MeasurableEquiv.prodAssoc ∘ Prod.map (MeasurableEquiv.prodAssoc.symm)
        (id : Sphere → Sphere) := by
    funext z
    rfl
  rw [he]
  simpa only [Measure.volume_eq_prod] using hb.comp ha

theorem gainDensity_formula (f : X × Velocity → ℝ) (p : X × Velocity) :
    gainDensity f p = ∫ q : Velocity × Sphere,
      collisionKernel p.2 q.1 q.2*f (p.1,scatterLeft p.2 q.1 q.2)*f (p.1,scatterRight p.2 q.1 q.2)
        ∂((volume : Measure Velocity).prod sphereArea) := by
  unfold gainDensity
  congr 1
  funext q
  exact postRate_formula f _

theorem gainLoss_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (gainDensity f) (μ.prod (volume : Measure Velocity)) ∧
      Integrable (lossDensity f) (μ.prod (volume : Measure Velocity)) := by
  have hpost : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => postRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (postRate_integrable hfm hf hpair)
  have hpre : Integrable
      (fun z : (X × Velocity) × (Velocity × Sphere) => preRate f (collisionGrouping.symm z))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) :=
    (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
      (preRate_integrable hfm hf hpair)
  exact ⟨hpost.integral_prod_left,hpre.integral_prod_left⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Slice mass bounds for the physical gain and loss -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem gainDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (gainDensity f) :=
  ((preRate_measurable hf).comp (scatterTriple_measurable.comp
    collisionGrouping.symm.measurable)).stronglyMeasurable.integral_prod_right'.measurable

theorem lossDensity_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (lossDensity f) :=
  ((preRate_measurable hf).comp
    collisionGrouping.symm.measurable).stronglyMeasurable.integral_prod_right'.measurable

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RawPairCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compactness bounds for the unweighted collision pair product -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem pairProduct_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (pairProduct f) := by unfold pairProduct; fun_prop

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PairRepresentative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Pair products depend only on the almost-everywhere density representative -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem pairProduct_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    pairProduct f =ᵐ[μ.prod (volume : Measure (Velocity × Velocity))] pairProduct g := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (pairProduct_measurable hfm) (pairProduct_measurable hgm))).mpr
  filter_upwards [Measure.ae_ae_of_ae_prod he] with x hx
  have hl : ∀ᵐ (y : Velocity × Velocity) ∂((volume : Measure Velocity).prod (volume : Measure Velocity)), f (x,y.1) = g (x,y.1) :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Velocity))
      (ν := (volume : Measure Velocity))).ae hx
  have hr : ∀ᵐ (y : Velocity × Velocity) ∂((volume : Measure Velocity).prod (volume : Measure Velocity)), f (x,y.2) = g (x,y.2) :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure Velocity))
      (ν := (volume : Measure Velocity))).ae hx
  rw [Measure.volume_eq_prod]
  filter_upwards [hl,hr] with y hy hz
  simp only [pairProduct,hy,hz]

theorem pairDensity_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    pairDensity f =ᵐ[μ.prod (volume : Measure (Velocity × Velocity))] pairDensity g := by
  filter_upwards [pairProduct_congr hfm hgm he] with z hz
  change f (z.1,z.2.1)*f (z.1,z.2.2) = g (z.1,z.2.1)*g (z.1,z.2.2) at hz
  simp only [pairDensity,mul_assoc]
  rw [hz]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionDissipation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Full collision terms are independent of the density representative -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_7 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem preRate_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    preRate f =ᵐ[(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea] preRate g := by
  have hp := (Measure.quasiMeasurePreserving_fst
    (μ := μ.prod (volume : Measure (Velocity × Velocity))) (ν := sphereArea)).ae
      (pairProduct_congr hfm hgm he)
  filter_upwards [hp] with z hz
  change f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) =
    g (z.1.1,z.1.2.1)*g (z.1.1,z.1.2.2) at hz
  simp only [preRate,mul_assoc,hz]

theorem postRate_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    postRate f =ᵐ[(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea] postRate g :=
  (scatterTriple_measurePreserving μ).quasiMeasurePreserving.ae (preRate_congr hfm hgm he)

theorem gainLoss_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    gainDensity f =ᵐ[μ.prod volume] gainDensity g ∧
      lossDensity f =ᵐ[μ.prod volume] lossDensity g := by
  have hp := (collisionGrouping_measurePreserving μ).symm.quasiMeasurePreserving.ae
    (postRate_congr hfm hgm he)
  have hl := (collisionGrouping_measurePreserving μ).symm.quasiMeasurePreserving.ae
    (preRate_congr hfm hgm he)
  constructor
  · filter_upwards [Measure.ae_ae_of_ae_prod hp] with p hp
    exact integral_congr_ae hp
  · filter_upwards [Measure.ae_ae_of_ae_prod hl] with p hp
    exact integral_congr_ae hp

theorem collision_fibers {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    (hpair : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      Integrable (fun q : Velocity × Sphere =>
        collisionKernel p.2 q.1 q.2*f (p.1,scatterLeft p.2 q.1 q.2)*
          f (p.1,scatterRight p.2 q.1 q.2)) ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q : Velocity × Sphere =>
        collisionKernel p.2 q.1 q.2*f p*f (p.1,q.1))
        ((volume : Measure Velocity).prod sphereArea) := by
  have hp := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    (postRate_integrable hfm hf hpair)
  have hl := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    (preRate_integrable hfm hf hpair)
  filter_upwards [hp.prod_right_ae,hl.prod_right_ae] with p hp hl
  constructor
  · have he : (fun q : Velocity × Sphere => postRate f (collisionGrouping.symm (p,q))) =
        (fun q => collisionKernel p.2 q.1 q.2*f (p.1,scatterLeft p.2 q.1 q.2)*
          f (p.1,scatterRight p.2 q.1 q.2)) := by
      funext q
      exact postRate_formula f _
    change Integrable (fun q => postRate f (collisionGrouping.symm (p,q))) _ at hp
    rw [he] at hp
    exact hp
  · exact hl

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Particle interchange and elastic substitution for the cutoff collision rate -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem particleSwap_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (particleSwap (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := ((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap
      (μ := (volume : Measure Velocity)) (ν := (volume : Measure Velocity)))).prod
      (MeasurePreserving.id sphereArea)
  have he : (⇑(particleSwap (X := X))) = Prod.map (Prod.map id Prod.swap) id := by
    funext z
    rfl
  rw [he]
  simpa only [Measure.volume_eq_prod] using h

theorem preRate_particleSwap (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : preRate f (particleSwap z) = preRate f z := by
  have hk : collisionKernel z.1.2.2 z.1.2.1 z.2 = collisionKernel z.1.2.1 z.1.2.2 z.2 := by
    unfold collisionKernel normalComponent
    rw [show z.1.2.2-z.1.2.1 = -(z.1.2.1-z.1.2.2) by abel,inner_neg_left,abs_neg]
  change collisionKernel z.1.2.2 z.1.2.1 z.2*f (z.1.1,z.1.2.2)*f (z.1.1,z.1.2.1) = _
  rw [hk]
  unfold preRate
  ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The gain rate and particle interchange -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem scatterLeft_swap (v w ω : Velocity) : scatterLeft w v ω = scatterRight v w ω := by
  have hn : normalComponent w v ω = -normalComponent v w ω := by
    unfold normalComponent
    rw [show w-v = -(v-w) by abel,inner_neg_left]
  simp only [scatterLeft,scatterRight,hn,neg_smul,sub_neg_eq_add]

theorem scatterRight_swap (v w ω : Velocity) : scatterRight w v ω = scatterLeft v w ω := by
  exact (scatterLeft_swap w v ω).symm

namespace CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem scatterTriple_particleSwap (z : (X × (Velocity × Velocity)) × Sphere) :
    scatterTriple (particleSwap z) = particleSwap (scatterTriple z) := by
  change ((z.1.1,(scatterLeft z.1.2.2 z.1.2.1 z.2,scatterRight z.1.2.2 z.1.2.1 z.2)),z.2) =
    ((z.1.1,(scatterRight z.1.2.1 z.1.2.2 z.2,scatterLeft z.1.2.1 z.1.2.2 z.2)),z.2)
  exact congrArg (fun p : Velocity × Velocity => ((z.1.1,p),z.2))
    (Prod.ext (scatterLeft_swap z.1.2.1 z.1.2.2 z.2)
      (scatterRight_swap z.1.2.1 z.1.2.2 z.2))

theorem postRate_particleSwap (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) : postRate f (particleSwap z) = postRate f z := by
  change preRate f (scatterTriple (particleSwap z)) = preRate f (scatterTriple z)
  rw [scatterTriple_particleSwap,preRate_particleSwap]

end CollisionCompactness
end BoltzmannNonuniqueness

end

end

section

/-! # The weak collision identity for the full hard-sphere operator -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem postRate_scatter_full (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    postRate f (scatterTriple z) = preRate f z := by
  change preRate f (scatterTriple (scatterTriple z)) = _
  rw [scatterTriple_involutive]

theorem integral_preRate_particleSwap_full (μ : Measure X) [SFinite μ]
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*preRate f z)
  simp only [preRate_particleSwap] at h
  exact h.symm

theorem integral_postRate_scatter_full (μ : Measure X) [SFinite μ]
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*postRate f z)
  simp only [postRate_scatter_full] at h
  exact h.symm

theorem integral_postRate_particleSwap_full (μ : Measure X) [SFinite μ]
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*postRate f z)
  simp only [postRate_particleSwap] at h
  exact h.symm

theorem integral_postRate_scatter_right_full (μ : Measure X) [SFinite μ]
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.2)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.2)*postRate f z)
  simp only [postRate_scatter_full] at h
  exact h.symm

theorem full_weak_identity {μ : Measure X} [SFinite μ] (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*postRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ z, ψ (z.1.1,z.1.2.1)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) -
    (∫ z, ψ (z.1.1,z.1.2.1)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    (1/2:ℝ) * ∫ z, collisionJump ψ z*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  have hr : Integrable (fun z => ψ (z.1.1,z.1.2.2)*preRate f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpre
    simp only [Function.comp_def,preRate_particleSwap] at h
    exact h
  have hrpost : Integrable (fun z => ψ (z.1.1,z.1.2.2)*postRate f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,postRate_particleSwap] at h
    exact h
  have hl' : Integrable (fun z =>
      ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*preRate f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,postRate_scatter_full] at h
    exact h
  have hr' : Integrable (fun z =>
      ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*preRate f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hrpost
    simp only [Function.comp_def,postRate_scatter_full] at h
    exact h
  have he : (fun z => collisionJump ψ z*preRate f z) =
      (fun z => ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*preRate f z)+
      (fun z => ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*preRate f z)-
      (fun z => ψ (z.1.1,z.1.2.1)*preRate f z)-
      (fun z => ψ (z.1.1,z.1.2.2)*preRate f z) := by
    funext z
    dsimp [collisionJump]
    ring
  rw [he,integral_sub' ((hl'.add hr').sub hpre) hr,
    integral_sub' (hl'.add hr') hpre,integral_add' hl' hr']
  rw [← integral_postRate_scatter_full,← integral_postRate_scatter_right_full,
    ← integral_postRate_particleSwap_full,← integral_preRate_particleSwap_full]
  ring

theorem full_collision_invariant {μ : Measure X} [SFinite μ]
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*postRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hψ : ∀ z, collisionJump ψ z = 0) :
    (∫ z, ψ (z.1.1,z.1.2.1)*postRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.1)*preRate f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := full_weak_identity f ψ hpre hpost
  simp only [hψ,zero_mul,integral_zero,mul_zero,sub_eq_zero] at h
  exact h

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Passing collision tests between rates and the physical gain/loss marginals -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_8 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

variable {X : Type*} [MeasurableSpace X]

theorem collision_test_marginal {μ : Measure X} [SFinite μ]
    (r : (X × (Velocity × Velocity)) × Sphere → ℝ) (ψ : X × Velocity → ℝ)
    (hi : Integrable (fun z => ψ (z.1.1,z.1.2.1)*r z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (fun p => ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
      ∂(volume : Measure Velocity).prod sphereArea)) (μ.prod volume) ∧
    (∫ p, ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
      ∂(volume : Measure Velocity).prod sphereArea) ∂μ.prod volume) =
      ∫ z, ψ (z.1.1,z.1.2.1)*r z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have hg := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable hi
  have he : (fun p : X × Velocity => ∫ q : Velocity × Sphere,
      ψ p*r (collisionGrouping.symm (p,q)) ∂(volume : Measure Velocity).prod sphereArea) =
      (fun p => ψ p*(∫ q : Velocity × Sphere, r (collisionGrouping.symm (p,q))
        ∂(volume : Measure Velocity).prod sphereArea)) := by
    funext p
    exact integral_const_mul _ _
  have hgroup : Integrable (fun y : (X × Velocity) × (Velocity × Sphere) =>
      ψ y.1*r (collisionGrouping.symm y))
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea)) := hg
  constructor
  · have h := hgroup.integral_prod_left
    rw [he] at h
    exact h
  · calc
      _ = ∫ p, ∫ q : Velocity × Sphere, ψ p*r (collisionGrouping.symm (p,q))
          ∂(volume : Measure Velocity).prod sphereArea ∂μ.prod volume := by rw [he]
      _ = ∫ y : (X × Velocity) × (Velocity × Sphere), ψ y.1*r (collisionGrouping.symm y)
          ∂(μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea) :=
        (integral_prod _ hgroup).symm
      _ = _ := (collisionGrouping_measurePreserving μ).symm.integral_comp
        collisionGrouping.symm.measurableEmbedding (fun z => ψ (z.1.1,z.1.2.1)*r z)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The mass, momentum, and energy collision invariants -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem collisionJump_mass (a : X → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p => a p.1) z = 0 := by
  unfold collisionJump
  ring

omit [MeasurableSpace X] in
theorem collisionJump_momentum (i : Fin 3) (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p : X × Velocity => p.2 i) z = 0 := by
  have h := congrArg (fun v : Velocity => v i) (scatter_momentum z.1.2.1 z.1.2.2 z.2)
  change (scatterLeft z.1.2.1 z.1.2.2 z.2) i+
    (scatterRight z.1.2.1 z.1.2.2 z.2) i = z.1.2.1 i+z.1.2.2 i at h
  change (scatterLeft z.1.2.1 z.1.2.2 z.2) i+
    (scatterRight z.1.2.1 z.1.2.2 z.2) i-z.1.2.1 i-z.1.2.2 i = 0
  linarith

omit [MeasurableSpace X] in
theorem collisionJump_energy (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p : X × Velocity => ‖p.2‖^2) z = 0 := by
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  have h := scatter_energy z.1.2.1 z.1.2.2 z.2 hw
  unfold collisionJump
  linarith

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusTransport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Free transport and its measure-preserving characteristic coordinates on the torus -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

theorem flight_measurePreserving (t : ℝ) :
    MeasurePreserving (flight t) (volume : Measure Phase) volume := by
  have hm : Measurable (Function.uncurry (fun (v : Velocity) (x : Position) =>
      x+torusProjection (t • v))) := by
    unfold Function.uncurry torusProjection
    fun_prop
  have hskew := (MeasurePreserving.id (volume : Measure Velocity)).skew_product hm
    (ae_of_all _ (fun v => (measurePreserving_add_right (volume : Measure Position)
      (torusProjection (t • v))).map_eq))
  have he : flight t = Prod.swap ∘ (fun z : Velocity × Position =>
      (z.1,z.2+torusProjection (t • z.1))) ∘ Prod.swap := rfl
  rw [he,Measure.volume_eq_prod]
  exact (Measure.measurePreserving_swap (μ := (volume : Measure Velocity)) (ν := volume)).comp
    (hskew.comp Measure.measurePreserving_swap)

theorem along_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving (fun z : ℝ × Phase => (z.1,flight z.1 z.2))
      (μ.prod volume) (μ.prod volume) :=
  (MeasurePreserving.id μ).skew_product (g := fun t p => flight t p) measurable_flight
    (ae_of_all _ (fun t => (flight_measurePreserving t).map_eq))

theorem back_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving (fun z : ℝ × Phase => (z.1,flight (-z.1) z.2))
      (μ.prod volume) (μ.prod volume) :=
  (MeasurePreserving.id μ).skew_product (g := fun t p => flight (-t) p)
    (measurable_flight.comp ((measurable_fst.neg).prodMk measurable_snd))
    (ae_of_all _ (fun t => (flight_measurePreserving (-t)).map_eq))

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Strong L¹ continuity of free transport on the physical torus -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.TorusFlight

local instance instRegularPhaseVolume : (volume : Measure Phase).Regular :=
  Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _

theorem continuous_continuousFlight : Continuous continuousFlight :=
  ContinuousMap.continuous_of_continuous_uncurry continuousFlight continuous_flight

theorem tendsto_flight_L1 {f : Phase → ℝ} (hf : Integrable f) (t : ℝ) :
    Tendsto (fun s => eLpNorm (fun p => f (flight s p)-f (flight t p)) 1 volume)
      (𝓝 t) (𝓝 0) := by
  let hf₁ := memLp_one_iff_integrable.mpr hf
  let u : Lp ℝ 1 (volume : Measure Phase) := hf₁.toLp f
  have hu : u =ᵐ[volume] f := hf₁.coeFn_toLp
  have hc : Continuous (fun s => Lp.compMeasurePreserving (continuousFlight s)
      (flight_measurePreserving s) u) :=
    continuous_const.compMeasurePreservingLp continuous_continuousFlight flight_measurePreserving (by norm_num)
  have hrep s : Lp.compMeasurePreserving (continuousFlight s) (flight_measurePreserving s) u =ᵐ[volume]
      (fun p => f (flight s p)) := by
    filter_upwards [Lp.coeFn_compMeasurePreserving u (flight_measurePreserving s),
      (flight_measurePreserving s).quasiMeasurePreserving.ae hu] with p hp hpu
    exact hp.trans hpu
  have he s : edist (Lp.compMeasurePreserving (continuousFlight s) (flight_measurePreserving s) u)
      (Lp.compMeasurePreserving (continuousFlight t) (flight_measurePreserving t) u) =
      eLpNorm (fun p => f (flight s p)-f (flight t p)) 1 volume := by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((hrep s).sub (hrep t))
  have ht := tendsto_iff_edist_tendsto_0.mp (hc.tendsto t)
  simpa only [he] using ht

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Integrals in characteristic coordinates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.TorusFlight

theorem integral_flight (f : Phase → ℝ) (t : ℝ) :
    (∫ p, f (flight t p)) = ∫ p, f p :=
  (flight_measurePreserving t).integral_comp (flightEquiv t).measurableEmbedding f

end BoltzmannNonuniqueness.TorusFlight

namespace BoltzmannNonuniqueness.Published

theorem integral_timePrimitive {μ : Measure ℝ} [SFinite μ]
    {R : ℝ × Phase → ℝ} (hRi : Integrable R (μ.prod volume))
    (t : ℝ) :
    (∫ p, timePrimitive μ R (t,p)) = ∫ s, if s ≤ t then ∫ p, R (s,p) else 0 ∂μ := by
  have hi : Integrable (fun z : ℝ × Phase => if z.1 ≤ t then R z else 0) (μ.prod volume) :=
    hRi.indicator (measurableSet_le measurable_fst measurable_const)
  have hs := integral_integral_swap (f := fun s p => if s ≤ t then R (s,p) else 0) hi
  change (∫ p, ∫ s, (if s ≤ t then R (s,p) else 0) ∂μ) = _
  rw [← hs]
  apply integral_congr_ae
  filter_upwards [] with s
  split_ifs <;> simp_all

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Integrating the periodic free-characteristic change of variables -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness

namespace TorusFlight

theorem integral_along {μ : Measure ℝ} [SFinite μ] {f : ℝ × Phase → ℝ}
    (hi : Integrable f (μ.prod volume)) :
    (∫ z, along f z ∂μ.prod volume) = ∫ z, f z ∂μ.prod volume := by
  have hai : Integrable (along f) (μ.prod volume) :=
    (along_measurePreserving μ).integrable_comp_of_integrable hi
  rw [integral_prod _ hai,integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => integral_flight (fun p => f (t,p)) t)

end TorusFlight

end BoltzmannNonuniqueness

end

end

section

/-! # The derivatives of periodic tests along physical free transport -/

noncomputable section

namespace BoltzmannNonuniqueness

theorem centered_characteristic_projection (p : Phase) (t s : ℝ) :
    torusProjection (torusRepresentative (TorusFlight.flight t p).1+(s-t) • p.2) =
      (TorusFlight.flight s p).1 := by
  funext i
  have hr := congrFun (torusProjection_representative (TorusFlight.flight t p).1) i
  change ((torusRepresentative (TorusFlight.flight t p).1) i : AddCircle (1:ℝ)) =
    p.1 i+(t*p.2 i : ℝ) at hr
  change (((torusRepresentative (TorusFlight.flight t p).1) i+(s-t)*p.2 i : ℝ) : AddCircle (1:ℝ)) =
    p.1 i+(s*p.2 i : ℝ)
  rw [AddCircle.coe_add,hr,add_assoc,← AddCircle.coe_add]
  congr 2
  ring

theorem KineticTest.hasDerivAt_along (φ : KineticTest) (p : Phase) (t : ℝ) :
    HasDerivAt (fun s => φ.toFun s (TorusFlight.flight s p).1 p.2)
      (φ.transportDerivative t (TorusFlight.flight t p)) t := by
  let x := torusRepresentative (TorusFlight.flight t p).1
  let L : ℝ → LiftedSpaceTimePhase := fun s => (s,(x+(s-t) • p.2,p.2))
  have hx : HasDerivAt (fun s => x+(s-t) • p.2) p.2 t := by
    simpa using (((hasDerivAt_id t).sub_const t).smul_const p.2).const_add x
  have hL : HasDerivAt L (1,p.2,0) t :=
    (hasDerivAt_id t).prodMk (hx.prodMk (hasDerivAt_const t p.2))
  have h := ((φ.regular.differentiable (by simp)) (L t)).hasFDerivAt.comp_hasDerivAt t hL
  have he : (fun s => φ.toFun (L s).1 (torusProjection (L s).2.1) (L s).2.2) =
      (fun s => φ.toFun s (TorusFlight.flight s p).1 p.2) := by
    funext s
    exact congrArg (fun y => φ.toFun s y p.2) (centered_characteristic_projection p t s)
  dsimp only [Function.comp_def] at h
  rw [he] at h
  simpa only [L,x,sub_self,zero_smul,add_zero,KineticTest.transportDerivative,TorusFlight.flight] using h

theorem MassTest.hasDerivAt_along (φ : MassTest) (p : Phase) (t : ℝ) :
    HasDerivAt (fun s => φ.toFun s (TorusFlight.flight s p).1)
      (φ.transportDerivative t (TorusFlight.flight t p)) t := by
  let x := torusRepresentative (TorusFlight.flight t p).1
  let L : ℝ → ℝ × Velocity := fun s => (s,x+(s-t) • p.2)
  have hx : HasDerivAt (fun s => x+(s-t) • p.2) p.2 t := by
    simpa using (((hasDerivAt_id t).sub_const t).smul_const p.2).const_add x
  have hL : HasDerivAt L (1,p.2) t := (hasDerivAt_id t).prodMk hx
  have h := ((φ.regular.differentiable (by simp)) (L t)).hasFDerivAt.comp_hasDerivAt t hL
  have he : (fun s => φ.toFun (L s).1 (torusProjection (L s).2)) =
      (fun s => φ.toFun s (TorusFlight.flight s p).1) := by
    funext s
    exact congrArg (φ.toFun s) (centered_characteristic_projection p t s)
  dsimp only [Function.comp_def] at h
  rw [he] at h
  simpa only [L,x,sub_self,zero_smul,add_zero,MassTest.transportDerivative,TorusFlight.flight] using h

end BoltzmannNonuniqueness

end

end

section

/-! # Measurable representatives for periodic kinetic and mass tests -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

private theorem measurable_kineticTestPoint : Measurable (fun p : ℝ × Phase =>
    (p.1,(torusRepresentative p.2.1,p.2.2))) :=
  measurable_fst.prodMk ((measurable_torusRepresentative.comp measurable_snd.fst).prodMk measurable_snd.snd)

@[fun_prop] theorem KineticTest.measurable_toFun (φ : KineticTest) :
    Measurable (fun p : ℝ × Phase => φ.toFun p.1 p.2.1 p.2.2) := by
  have h := φ.regular.continuous.measurable.comp measurable_kineticTestPoint
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact congrArg (fun x => φ.toFun p.1 x p.2.2) (torusProjection_representative p.2.1).symm

@[fun_prop] theorem KineticTest.measurable_transportDerivative (φ : KineticTest) :
    Measurable (fun p : ℝ × Phase => φ.transportDerivative p.1 p.2) := by
  have hm := (φ.regular.continuous_fderiv (by simp)).measurable.comp measurable_kineticTestPoint
  exact (isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous.measurable.comp
    (hm.prodMk (measurable_const.prodMk (measurable_snd.snd.prodMk measurable_const)))

@[fun_prop] theorem MassTest.measurable_toFun (φ : MassTest) :
    Measurable (fun p : ℝ × Phase => φ.toFun p.1 p.2.1) := by
  have hm : Measurable (fun p : ℝ × Phase => (p.1,torusRepresentative p.2.1)) :=
    measurable_fst.prodMk (measurable_torusRepresentative.comp measurable_snd.fst)
  have h := φ.regular.continuous.measurable.comp hm
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact congrArg (φ.toFun p.1) (torusProjection_representative p.2.1).symm

end BoltzmannNonuniqueness

end

end

section

/-! # Uniform bounds for periodic tests on a finite time interval -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness

private theorem fundamentalCube_compact : IsCompact fundamentalCube :=
  (isCompact_univ_pi (fun _ : Fin 3 => isCompact_Icc)).image
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))

private theorem representative_mem_cube (x : Position) : torusRepresentative x ∈ fundamentalCube := by
  refine ⟨_,?_,rfl⟩
  intro i _
  have h := ((AddCircle.equivIco (1:ℝ) 0) (x i)).property
  exact ⟨h.1,by simpa using h.2.le⟩

private theorem kinetic_lift_support (φ : KineticTest) {R : ℝ}
    (hzero : ∀ t x v, R < |t| ∨ R < ‖v‖ → φ.toFun t x v = 0) :
    tsupport (fun z : LiftedSpaceTimePhase => φ.toFun z.1 (torusProjection z.2.1) z.2.2) ⊆
      {z | ‖z.2.2‖ ≤ R} := by
  apply closure_minimal
  · intro z hz
    by_contra hn
    exact hz (hzero z.1 (torusProjection z.2.1) z.2.2 (Or.inr (lt_of_not_ge hn)))
  · exact isClosed_le (continuous_snd.snd.norm) continuous_const

private theorem kinetic_bounds_on_box (φ : KineticTest) (T R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ p : Phase, ‖p.2‖ ≤ R →
      |φ.toFun t p.1 p.2| ≤ C ∧
      ‖fderiv ℝ (fun z : LiftedSpaceTimePhase => φ.toFun z.1 (torusProjection z.2.1) z.2.2)
        (t,torusRepresentative p.1,p.2)‖ ≤ C := by
  let K : Set LiftedSpaceTimePhase := Icc 0 T ×ˢ (fundamentalCube ×ˢ Metric.closedBall 0 R)
  have hK : IsCompact K := isCompact_Icc.prod
    (fundamentalCube_compact.prod (isCompact_closedBall (0:Velocity) R))
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn φ.regular.continuous.continuousOn
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (φ.regular.continuous_fderiv (by simp)).continuousOn
  refine ⟨|B|+|D|,by positivity,?_⟩
  intro t ht p hv
  have hp : (t,torusRepresentative p.1,p.2) ∈ K :=
    ⟨ht,representative_mem_cube p.1,by simpa using hv⟩
  have hb : |φ.toFun t p.1 p.2| ≤ B := by
    simpa only [torusProjection_representative,Real.norm_eq_abs] using hB _ hp
  have hd := hD _ hp
  constructor
  · linarith [le_abs_self B,abs_nonneg D]
  · exact hd.trans (by linarith [le_abs_self D,abs_nonneg B])

private theorem velocity_fderiv_zero {L : LiftedSpaceTimePhase → ℝ} {R : ℝ}
    (hs : tsupport L ⊆ {z | ‖z.2.2‖ ≤ R}) (z : LiftedSpaceTimePhase) (hz : R < ‖z.2.2‖) :
    fderiv ℝ L z = 0 := by
  have hout : z ∉ tsupport L := fun h => (not_le_of_gt hz) (hs h)
  exact fderiv_of_notMem_tsupport ℝ hout

private theorem kinetic_derivative_zero (φ : KineticTest) {R : ℝ}
    (hzero : ∀ t x v, R < |t| ∨ R < ‖v‖ → φ.toFun t x v = 0)
    (t : ℝ) (p : Phase) (hv : R < ‖p.2‖) : φ.transportDerivative t p = 0 := by
  let L : LiftedSpaceTimePhase → ℝ := fun z => φ.toFun z.1 (torusProjection z.2.1) z.2.2
  have hs : tsupport L ⊆ {z | ‖z.2.2‖ ≤ R} := kinetic_lift_support φ hzero
  exact congrArg (fun A : LiftedSpaceTimePhase →L[ℝ] ℝ => A ((1:ℝ),p.2,0))
    (velocity_fderiv_zero hs (t,torusRepresentative p.1,p.2) hv)

theorem KineticTest.bounded_on_time (φ : KineticTest) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ p : Phase,
      |φ.toFun t p.1 p.2| ≤ C ∧ |φ.transportDerivative t p| ≤ C := by
  obtain ⟨R,hR,hzero⟩ := φ.compact_time_velocity
  obtain ⟨B,hB,hbounds⟩ := kinetic_bounds_on_box φ T R
  refine ⟨B*(1+R),by positivity,?_⟩
  intro t ht p
  by_cases hv : ‖p.2‖ ≤ R
  · obtain ⟨hb,hd⟩ := hbounds t ht p hv
    have htangent : ‖((1:ℝ),p.2,(0:Velocity))‖ ≤ 1+R := by
      simp only [Prod.norm_def,Real.norm_eq_abs,abs_one,norm_zero,max_eq_left (norm_nonneg p.2)]
      exact max_le (by linarith) (by linarith)
    constructor
    · nlinarith
    · change ‖fderiv ℝ (fun z : LiftedSpaceTimePhase => φ.toFun z.1 (torusProjection z.2.1) z.2.2)
        (t,torusRepresentative p.1,p.2) ((1:ℝ),p.2,0)‖ ≤ _
      exact ((fderiv ℝ _ _).le_opNorm _).trans
        (mul_le_mul hd htangent (norm_nonneg _) hB)
  · rw [hzero t p.1 p.2 (Or.inr (lt_of_not_ge hv)),kinetic_derivative_zero φ hzero t p (lt_of_not_ge hv)]
    simp only [abs_zero]
    constructor <;> positivity

theorem MassTest.bounded_on_time (φ : MassTest) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ∀ p : Phase,
      |φ.toFun t p.1| ≤ C ∧ |φ.transportDerivative t p| ≤ C*(1+‖p.2‖) := by
  let K : Set (ℝ × Velocity) := Icc 0 T ×ˢ fundamentalCube
  have hK : IsCompact K := isCompact_Icc.prod fundamentalCube_compact
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn φ.regular.continuous.continuousOn
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (φ.regular.continuous_fderiv (by simp)).continuousOn
  refine ⟨|B|+|D|,by positivity,?_⟩
  intro t ht p
  have hp : (t,torusRepresentative p.1) ∈ K := ⟨ht,representative_mem_cube p.1⟩
  have hb : |φ.toFun t p.1| ≤ |B| := by
    simpa only [torusProjection_representative,Real.norm_eq_abs] using
      (hB _ hp).trans (le_abs_self B)
  have hd : ‖fderiv ℝ (fun z : ℝ × Velocity => φ.toFun z.1 (torusProjection z.2))
      (t,torusRepresentative p.1)‖ ≤ |D| := (hD _ hp).trans (le_abs_self D)
  have htangent : ‖((1:ℝ),p.2)‖ ≤ 1+‖p.2‖ := by
    simp only [Prod.norm_def,Real.norm_eq_abs,abs_one]
    exact max_le (by linarith [norm_nonneg p.2]) (by linarith)
  constructor
  · linarith [abs_nonneg D]
  · change ‖fderiv ℝ (fun z : ℝ × Velocity => φ.toFun z.1 (torusProjection z.2))
      (t,torusRepresentative p.1) ((1:ℝ),p.2)‖ ≤ _
    exact ((fderiv ℝ _ _).le_opNorm _).trans (mul_le_mul
      (hd.trans (by linarith [abs_nonneg B])) htangent (norm_nonneg _) (by positivity))

end BoltzmannNonuniqueness

end

end

section

/-! # Smoothness of periodic tests on each free characteristic -/

noncomputable section

namespace BoltzmannNonuniqueness

theorem KineticTest.contDiff_along (φ : KineticTest) (p : Phase) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s => φ.toFun s (TorusFlight.flight s p).1 p.2) := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ =>
      (s,(torusRepresentative p.1+s • p.2,p.2))) := by fun_prop
  have h := φ.regular.comp hL
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  have he := centered_characteristic_projection p 0 s
  simp only [TorusFlight.flight_zero,sub_zero] at he
  exact congrArg (fun x => φ.toFun s x p.2) he.symm

theorem MassTest.contDiff_along (φ : MassTest) (p : Phase) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s => φ.toFun s (TorusFlight.flight s p).1) := by
  have hL : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ =>
      (s,torusRepresentative p.1+s • p.2)) := by fun_prop
  have h := φ.regular.comp hL
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  have he := centered_characteristic_projection p 0 s
  simp only [TorusFlight.flight_zero,sub_zero] at he
  exact congrArg (φ.toFun s) he.symm

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalMomentIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform finite-entropy moments give spacetime transport integrability -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem entropyMoment_spacetime_integrable {T : ℝ} {F : Evolution}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p)
    (hfinite : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (F t))
    (hbound : ∃ C : ℝ, ∀ t ∈ Icc 0 T, (∫ p, entropyMoment (F t) p) ≤ C) :
    Integrable (fun z : ℝ × Phase => entropyMoment (F z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  let E : ℝ × Phase → ℝ := fun z => entropyMoment (F z.1) z.2
  have hEm : Measurable E := by
    unfold E entropyMoment
    exact hFm.mul ((measurable_const.add (measurable_snd.snd.norm.pow_const 2)).add hFm.log.abs)
  have hEn (t : ℝ) (p : Phase) : 0 ≤ E (t,p) := entropyMoment_nonneg (hFn t p)
  obtain ⟨C,hC⟩ := hbound
  apply (integrable_prod_iff hEm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hfinite t ht).2.2
  · apply Integrable.of_bound (hEm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have he : (∫ p, ‖E (t,p)‖) = ∫ p, E (t,p) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => Real.norm_of_nonneg (hEn t p))
    rw [he,Real.norm_of_nonneg (integral_nonneg (hEn t))]
    exact hC t ht

theorem mass_transport_integrable {T : ℝ} {F : Evolution}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p)
    (hEi : Integrable (fun z : ℝ × Phase => entropyMoment (F z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume)) (φ : MassTest) :
    Integrable (fun z : ℝ × Phase => F z.1 z.2*φ.transportDerivative z.1 z.2)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  obtain ⟨C,hC,hb⟩ := φ.bounded_on_time T
  apply (hEi.const_mul (2*C)).mono' (hFm.mul φ.measurable_transportDerivative).aestronglyMeasurable
  have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht] with z hz
  change ‖F z.1 z.2*φ.transportDerivative z.1 z.2‖ ≤ 2*C*entropyMoment (F z.1) z.2
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hFn z.1 z.2)]
  have hφ := (hb z.1 hz z.2).2
  have hf := hFn z.1 z.2
  have hE := entropyMoment_nonneg hf
  have hv : (1+‖z.2.2‖)*F z.1 z.2 ≤ 2*entropyMoment (F z.1) z.2 := by
    unfold entropyMoment
    have hlog := abs_nonneg (Real.log (F z.1 z.2))
    nlinarith [sq_nonneg (‖z.2.2‖-1),mul_nonneg hf hlog,
      mul_nonneg hf (sq_nonneg (‖z.2.2‖-1))]
  exact (mul_le_mul_of_nonneg_left hφ hf).trans (by nlinarith)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RenormalizationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The manuscript's renormalizations have uniform Lipschitz bounds -/

noncomputable section

open Set
open scoped NNReal

namespace BoltzmannNonuniqueness.Renormalization

theorem exists_lipschitz (β : Renormalization) :
    ∃ C : ℝ≥0, LipschitzOnWith C β.toFun (Ici 0) := by
  obtain ⟨C,hC,hb⟩ := β.derivative_bound
  refine ⟨⟨C,hC⟩,(convex_Ici (0:ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (β.regular.differentiableOn (by norm_num) x hx).hasDerivWithinAt) ?_⟩
  intro x hx
  have h : |derivWithin β.toFun (Ici 0) x| ≤ C :=
    (hb x hx).trans (div_le_self hC (by linarith only [show 0 ≤ x from hx]))
  exact_mod_cast h

theorem weighted_lipschitz {β : Renormalization} {C : ℝ≥0}
    (hβ : LipschitzOnWith C β.toFun (Ici 0)) {m u v : ℝ}
    (hm : 0 < m) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |m*β.toFun (u/m)-m*β.toFun (v/m)| ≤ (C:ℝ)*|u-v| := by
  have h := hβ.dist_le_mul (u/m) (div_nonneg hu hm.le) (v/m) (div_nonneg hv hm.le)
  simp only [Real.dist_eq] at h
  calc
    _ = m*|β.toFun (u/m)-β.toFun (v/m)| := by
      rw [← mul_sub,abs_mul,abs_of_pos hm]
    _ ≤ m*((C:ℝ)*|u/m-v/m|) := mul_le_mul_of_nonneg_left h hm.le
    _ = _ := by
      rw [← sub_div,abs_div,abs_of_pos hm]
      field_simp

theorem weighted_abs_bound {β : Renormalization} {C : ℝ≥0}
    (hβ : LipschitzOnWith C β.toFun (Ici 0)) {m u : ℝ} (hm : 0 < m) (hu : 0 ≤ u) :
    |m*β.toFun (u/m)| ≤ (C:ℝ)*u := by
  simpa only [zero_div,β.at_zero,mul_zero,sub_zero,abs_of_nonneg hu] using
    weighted_lipschitz hβ hm hu (le_refl (0:ℝ))

end BoltzmannNonuniqueness.Renormalization

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_RenormalizedIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurability and integrability of the renormalized collision source -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Renormalization

variable {X : Type*} [MeasurableSpace X]

theorem measurable_derivative_comp (β : Renormalization) {f : X → ℝ}
    (hfm : Measurable f) (hfn : ∀ x, 0 ≤ f x) :
    Measurable (fun x => derivWithin β.toFun (Ici 0) (f x)) := by
  have hc := β.regular.continuousOn_derivWithin (uniqueDiffOn_Ici 0) (le_refl 1)
  exact (continuousOn_iff_continuous_domRestrict.mp hc).measurable.comp
    (hfm.subtype_mk (h := hfn))

theorem derivative_mul_integrable (β : Renormalization) {μ : Measure X}
    {f r : X → ℝ} (hfm : Measurable f) (hfn : ∀ x, 0 ≤ f x) (hri : Integrable r μ) :
    Integrable (fun x => derivWithin β.toFun (Ici 0) (f x)*r x) μ := by
  obtain ⟨C,hC,hb⟩ := β.derivative_bound
  apply hri.bdd_mul (c := C) (β.measurable_derivative_comp hfm hfn).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs]
  exact (hb (f x) (hfn x)).trans (div_le_self hC (by linarith only [hfn x]))

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # Integrability of the weak renormalized equation on finite intervals -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

namespace Renormalization

variable {X : Type*} [MeasurableSpace X]

theorem weighted_measurable (β : Renormalization) {f m : X → ℝ}
    (hfm : Measurable f) (hmm : Measurable m) (hfn : ∀ x, 0 ≤ f x) (hm : ∀ x, 0 < m x) :
    Measurable (fun x => m x*β.toFun (f x/m x)) := by
  have hq := hfm.div hmm
  have hn : ∀ x, f x/m x ∈ Ici 0 := fun x => div_nonneg (hfn x) (hm x).le
  have hb := (continuousOn_iff_continuous_domRestrict.mp β.regular.continuousOn).measurable.comp
    (hq.subtype_mk (h := hn))
  exact hmm.mul hb

theorem weighted_integrable (β : Renormalization) {μ : Measure X} {f m : X → ℝ}
    (hfm : Measurable f) (hmm : Measurable m) (hfn : ∀ x, 0 ≤ f x) (hm : ∀ x, 0 < m x)
    (hfi : Integrable f μ) : Integrable (fun x => m x*β.toFun (f x/m x)) μ := by
  obtain ⟨C,hC⟩ := β.exists_lipschitz
  apply (hfi.const_mul (C:ℝ)).mono' (β.weighted_measurable hfm hmm hfn hm).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using weighted_abs_bound hC (hm x) (hfn x))

end Renormalization

theorem renormalizedIntegrand_integrable {T : ℝ} {F : Evolution}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2))
    (hFn : ∀ t p, 0 ≤ F t p)
    (hFi : Integrable (fun z : ℝ × Phase => F z.1 z.2)
      ((volume.restrict (Icc 0 T)).prod volume))
    (hQi : Integrable (fun z : ℝ × Phase => collision (F z.1) z.2.1 z.2.2)
      ((volume.restrict (Icc 0 T)).prod volume)) (β : Renormalization) (φ : KineticTest) :
    IntegrableOn (renormalizedIntegrand F β φ) (boundedTimes T) := by
  let μ : Measure (ℝ × Phase) := (volume.restrict (Icc 0 T)).prod volume
  have hmm : Measurable (fun z : ℝ × Phase => maxwellian z.2.2) := by
    unfold maxwellian
    fun_prop
  have hq := hFm.div hmm
  have hn : ∀ z : ℝ × Phase, 0 ≤ F z.1 z.2/maxwellian z.2.2 :=
    fun z => div_nonneg (hFn z.1 z.2) (maxwellian_pos z.2.2).le
  have hwi := β.weighted_integrable hFm hmm (fun z => hFn z.1 z.2)
    (fun z => maxwellian_pos z.2.2) hFi
  have hri := β.derivative_mul_integrable hq hn hQi
  obtain ⟨C,_hC,hb⟩ := φ.bounded_on_time T
  have ht : ∀ᵐ z : ℝ × Phase ∂μ, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hwb : ∀ᵐ z : ℝ × Phase ∂μ, ‖φ.transportDerivative z.1 z.2‖ ≤ C := by
    filter_upwards [ht] with z hz
    simpa only [Real.norm_eq_abs] using (hb z.1 hz z.2).2
  have hrb : ∀ᵐ z : ℝ × Phase ∂μ, ‖φ.toFun z.1 z.2.1 z.2.2‖ ≤ C := by
    filter_upwards [ht] with z hz
    simpa only [Real.norm_eq_abs] using (hb z.1 hz z.2).1
  have hi := (hwi.mul_bdd φ.measurable_transportDerivative.aestronglyMeasurable hwb).add
    (hri.mul_bdd φ.measurable_toFun.aestronglyMeasurable hrb)
  change Integrable (renormalizedIntegrand F β φ) _
  rw [← phaseInterval_measure]
  exact hi

end BoltzmannNonuniqueness

end

end

section

/-! # The renormalized characteristic equation tested along a smooth path -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.Renormalization

theorem tested_chain_rule (β : Renormalization) {a b : ℝ} (hab : a ≤ b)
    {F r ψ ψ' : ℝ → ℝ} (hF : AbsolutelyContinuousOnInterval F a b)
    (hFn : ∀ t ∈ Icc a b, 0 ≤ F t)
    (hr : ∀ᵐ t, t ∈ Icc a b → HasDerivAt F (r t) t)
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hψ' : ∀ᵐ t, t ∈ Icc a b → HasDerivAt ψ (ψ' t) t) :
    (∫ t in a..b, derivWithin β.toFun (Ici 0) (F t)*r t*ψ t+β.toFun (F t)*ψ' t) =
      β.toFun (F b)*ψ b-β.toFun (F a)*ψ a := by
  obtain ⟨C,hC⟩ := β.exists_lipschitz
  have hB : AbsolutelyContinuousOnInterval (fun t => β.toFun (F t)) a b :=
    hC.comp_absolutelyContinuousOnInterval
      (fun t ht => hFn t (by simpa only [uIcc_of_le hab] using ht)) hF
  calc
    _ = ∫ t in a..b, deriv (fun s => β.toFun (F s)) t*ψ t+
        β.toFun (F t)*deriv ψ t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hr,hψ',Measure.ae_ne (volume : Measure ℝ) b] with t ht hpt htb htI
      have ht' : t ∈ Ioc a b := by simpa only [uIoc_of_le hab] using htI
      have htcc : t ∈ Icc a b := ⟨ht'.1.le,ht'.2⟩
      have hd := (β.regular.differentiableOn (by norm_num) (F t) (hFn t htcc)).hasDerivWithinAt
      have hc := hd.scomp t (ht htcc).hasDerivWithinAt hFn
      have hda := hc.hasDerivAt (Icc_mem_nhds ht'.1 (lt_of_le_of_ne ht'.2 htb))
      rw [(hpt htcc).deriv]
      have he : deriv (fun s => β.toFun (F s)) t =
          derivWithin β.toFun (Ici 0) (F t)*r t := by
        simpa only [Function.comp_def,smul_eq_mul,mul_comm] using hda.deriv
      rw [he]
    _ = _ := hB.integral_deriv_mul_eq_sub hψ

theorem weighted_tested_chain_rule (β : Renormalization) {a b m : ℝ}
    (hab : a ≤ b) (hm : 0 < m) {F r ψ ψ' : ℝ → ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hFn : ∀ t ∈ Icc a b, 0 ≤ F t)
    (hr : ∀ᵐ t, t ∈ Icc a b → HasDerivAt F (r t) t)
    (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hψ' : ∀ᵐ t, t ∈ Icc a b → HasDerivAt ψ (ψ' t) t) :
    (∫ t in a..b, derivWithin β.toFun (Ici 0) (F t/m)*r t*ψ t+
      m*β.toFun (F t/m)*ψ' t) =
      m*β.toFun (F b/m)*ψ b-m*β.toFun (F a/m)*ψ a := by
  have hF' : AbsolutelyContinuousOnInterval (fun t => F t/m) a b := by
    simpa only [div_eq_mul_inv,mul_comm] using
      AbsolutelyContinuousOnInterval.const_mul m⁻¹ hF
  have hr' : ∀ᵐ t, t ∈ Icc a b → HasDerivAt (fun t => F t/m) (r t/m) t := by
    filter_upwards [hr] with t ht hmem
    exact (ht hmem).div_const m
  have he := congrArg (fun x : ℝ => m*x) (β.tested_chain_rule hab hF'
    (fun t ht => div_nonneg (hFn t ht) hm.le) hr' hψ hψ')
  rw [← intervalIntegral.integral_const_mul] at he
  have hi : (fun t => m*(derivWithin β.toFun (Ici 0) (F t/m)*(r t/m)*ψ t+
      β.toFun (F t/m)*ψ' t)) =
      (fun t => derivWithin β.toFun (Ici 0) (F t/m)*r t*ψ t+
        m*β.toFun (F t/m)*ψ' t) := by
    funext t
    field_simp
  rw [hi] at he
  exact he.trans (by ring)

end BoltzmannNonuniqueness.Renormalization

end

end

section

/-! # Integrability of the tested renormalized time traces -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.KineticTest

theorem weighted_slice_integrable (φ : KineticTest) (β : Renormalization)
    {T t : ℝ} (ht : t ∈ Icc 0 T) {f : Density}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p) (hfi : Integrable f) :
    Integrable (fun p => maxwellian p.2*β.toFun (f p/maxwellian p.2)*φ.toFun t p.1 p.2) := by
  have hmm : Measurable (fun p : Phase => maxwellian p.2) := by
    unfold maxwellian
    fun_prop
  have hi := β.weighted_integrable hfm hmm hfn (fun p => maxwellian_pos p.2) hfi
  have hφ : Measurable (fun p : Phase => φ.toFun t p.1 p.2) :=
    φ.measurable_toFun.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C,_hC,hb⟩ := φ.bounded_on_time T
  apply hi.mul_bdd hφ.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    simpa only [Real.norm_eq_abs] using (hb t ht p).1)

end BoltzmannNonuniqueness.KineticTest

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyDissipationAverage
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Finite Gaussian relative entropy controls the required datum class -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem entropyGaussian_integrable : Integrable entropyGaussian := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (by norm_num : 0 < ((1/4:ℂ)).re) 0 (0:Velocity)).norm
  have hg : Integrable (fun v : Velocity => Real.exp (-‖v‖^2/4)) := by
    convert! h using 1
    all_goals try with_reducible_and_instances rfl
    funext v
    simp only [zero_mul,add_zero,Complex.norm_exp]
    congr 1
    norm_num
    norm_cast
    ring
  convert hg.const_mul ((2*Real.pi)^(-(3/2:ℝ))*Real.exp (1/4)) using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  dsimp [entropyGaussian,maxwellian]
  simp only [mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem entropy_controls_mass_energy {u : ℝ} (hu : 0 ≤ u) (v : Velocity) :
    (1+‖v‖^2)*u ≤ 4*(scalarRelativeEntropy (maxwellian v) u+entropyGaussian v) := by
  have h := entropyDual_le (maxwellian_pos v) hu ((1+‖v‖^2)/4)
  dsimp [entropyDual,entropyGaussian] at *
  nlinarith [maxwellian_pos v]

end BoltzmannNonuniqueness

end

end

section

/-! # A uniform absolute-entropy moment from the relative-entropy bound -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem entropyMomentCoefficient_nonneg : 0 ≤ entropyMomentCoefficient := by
  unfold entropyMomentCoefficient
  positivity

theorem entropyMoment_control {f : Density} {z : Phase} (hu : 0 ≤ f z) :
    entropyMoment f z ≤
      (1+4*entropyMomentCoefficient)*scalarRelativeEntropy (maxwellian z.2) (f z)+
        4*entropyMomentCoefficient*entropyGaussian z.2+maxwellian z.2 := by
  let u := f z
  let c := 1-(3/2:ℝ)*Real.log (2*Real.pi)
  have hu' : 0 ≤ u := hu
  have hE : 0 ≤ ‖z.2‖^2*u := mul_nonneg (sq_nonneg _) hu'
  have hm := (maxwellian_pos z.2).le
  have hc : c*u ≤ |c| *u := mul_le_mul_of_nonneg_right (le_abs_self c) hu'
  have hc' : -(|c| *u) ≤ c*u := by
    simpa only [neg_mul] using mul_le_mul_of_nonneg_right (neg_abs_le c) hu'
  have hcu : 0 ≤ |c| *u := mul_nonneg (abs_nonneg c) hu'
  have hH := scalarRelativeEntropy_nonneg (maxwellian_pos z.2) hu'
  have he : scalarRelativeEntropy (maxwellian z.2) u =
      u*Real.log u-c*u+(1/2:ℝ)*(‖z.2‖^2*u)+maxwellian z.2 := by
    dsimp [scalarRelativeEntropy,c]
    rw [log_maxwellian]
    ring
  have ha : |u*Real.log u| ≤ u*Real.log u+2*(|c| *u+(1/2:ℝ)*(‖z.2‖^2*u)+maxwellian z.2) := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hpre : entropyMoment f z ≤ scalarRelativeEntropy (maxwellian z.2) u+
      entropyMomentCoefficient*((1+‖z.2‖^2)*u)+maxwellian z.2 := by
    have habs : u*|Real.log u| = |u*Real.log u| := by rw [abs_mul,abs_of_nonneg hu']
    change u*(1+‖z.2‖^2+|Real.log u|) ≤ _
    rw [mul_add,habs]
    change _ ≤ scalarRelativeEntropy (maxwellian z.2) u+(2+3*|c|)*((1+‖z.2‖^2)*u)+maxwellian z.2
    have hEc : 0 ≤ |c| *(‖z.2‖^2*u) := mul_nonneg (abs_nonneg c) hE
    nlinarith
  have hb := mul_le_mul_of_nonneg_left (entropy_controls_mass_energy hu' z.2)
    entropyMomentCoefficient_nonneg
  exact hpre.trans (by nlinarith)

theorem entropyMoment_integral_control {f : Density} (hf : FiniteEntropyDatum f) :
    (∫ z, entropyMoment f z) ≤
      (1+4*entropyMomentCoefficient)*relativeEntropy f+
        4*entropyMomentCoefficient*(∫ z : Phase, entropyGaussian z.2)+
          (∫ z : Phase, maxwellian z.2) := by
  have hH := hf.integrable_relativeEntropy.congr (Filter.Eventually.of_forall (fun z =>
    (scalarRelativeEntropy_eq (maxwellian_pos z.2) _).symm))
  have hG : Integrable (fun z : Phase => entropyGaussian z.2) :=
    entropyGaussian_integrable.comp_snd volume
  have hi := ((hH.const_mul (1+4*entropyMomentCoefficient)).add
    (hG.const_mul (4*entropyMomentCoefficient))).add integrable_maxwellian_phase
  have hb := integral_mono_ae hf.2.2 hi (hf.1.mono (fun _ hu => entropyMoment_control hu))
  simp only [Pi.add_apply] at hb
  have hsum := integral_add ((hH.const_mul (1+4*entropyMomentCoefficient)).add
    (hG.const_mul (4*entropyMomentCoefficient))) integrable_maxwellian_phase
  have hsum' := integral_add (hH.const_mul (1+4*entropyMomentCoefficient))
    (hG.const_mul (4*entropyMomentCoefficient))
  simp only [Pi.add_apply] at hsum hsum'
  rw [hsum,hsum',integral_const_mul,integral_const_mul] at hb
  have he : (∫ z, scalarRelativeEntropy (maxwellian z.2) (f z)) = relativeEntropy f :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => scalarRelativeEntropy_eq (maxwellian_pos z.2) _))
  rwa [he] at hb

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_TimeSourceCumulative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The time primitive on the common closed time interval -/

noncomputable section

open MeasureTheory Set Filter

namespace BoltzmannNonuniqueness.Published

variable {P : Type*} [MeasurableSpace P]

omit [MeasurableSpace P] in
theorem timePrimitive_eq_interval {T t : ℝ} (ht : t ∈ Icc 0 T)
    (f : ℝ × P → ℝ) (p : P) :
    timePrimitive (volume.restrict (Icc 0 T)) f (t,p) = ∫ s in 0..t, f (s,p) := by
  change (∫ s, (Iic t).indicator (fun s => f (s,p)) s ∂volume.restrict (Icc 0 T)) = _
  rw [integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  have he : Iic t ∩ Icc 0 T = Icc 0 t := by
    ext s
    simp only [mem_inter_iff,mem_Iic,mem_Icc]
    constructor
    · rintro ⟨hs,h0,_⟩; exact ⟨h0,hs⟩
    · rintro ⟨h0,hs⟩; exact ⟨hs,h0,hs.trans ht.2⟩
  rw [he,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le ht.1]

theorem timePrimitive_measurable (μ : Measure ℝ) [SFinite μ] {f : ℝ × P → ℝ}
    (hf : Measurable f) : Measurable (timePrimitive μ f) := by
  have hm : Measurable (fun z : (ℝ × P) × ℝ => if z.2 ≤ z.1.1 then f (z.2,z.1.2) else 0) :=
    (hf.comp (measurable_snd.prodMk measurable_fst.snd)).ite
      (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Strong L¹ continuity of the integrable time primitive -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {P : Type*} [MeasurableSpace P]

theorem timePrimitive_L1_continuous {ν : Measure P} [SFinite ν] {T : ℝ}
    (hT : 0 ≤ T) {f : ℝ × P → ℝ} (hfm : Measurable f)
    (hfi : Integrable f ((volume.restrict (Icc 0 T)).prod ν))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => eLpNorm (fun p =>
      timePrimitive (volume.restrict (Icc 0 T)) f (s,p)-
        timePrimitive (volume.restrict (Icc 0 T)) f (t,p)) 1 ν)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let G : ℝ → P → ℝ := fun s p => timePrimitive μ f (s,p)
  let M : P → ℝ := fun p => ∫ s, ‖f (s,p)‖ ∂μ
  have hM : Integrable M ν := hfi.integral_norm_prod_right
  have hGm s : Measurable (G s) :=
    (timePrimitive_measurable μ hfm).comp (measurable_const.prodMk measurable_id)
  have hGb (s : ℝ) : ∀ᵐ p ∂ν, ‖G s p‖ ≤ M p := by
    filter_upwards [hfi.prod_left_ae] with p hp
    apply norm_integral_le_of_norm_le hp.norm
    filter_upwards [] with r
    change ‖if r ≤ s then f (r,p) else 0‖ ≤ ‖f (r,p)‖
    split <;> simp
  have hGi (s : ℝ) : Integrable (G s) ν :=
    hM.mono' (hGm s).aestronglyMeasurable (hGb s)
  have hbound (s : ℝ) : ∀ᵐ p ∂ν, ‖‖G s p-G t p‖‖ ≤ 2*M p := by
    filter_upwards [hGb s,hGb t] with p hs ht
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (by linarith)
  have hpoint : ∀ᵐ p ∂ν,
      Tendsto (fun s => ‖G s p-G t p‖) (𝓝[Icc 0 T] t) (𝓝 (0 : ℝ)) := by
    filter_upwards [hfi.prod_left_ae] with p hp
    have hpI : IntervalIntegrable (fun r => f (r,p)) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hp
    have hc := intervalIntegral.continuousOn_primitive_interval' hpI
      (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T)
    rw [uIcc_of_le hT] at hc
    have hcG : ContinuousOn (fun s => G s p) (Icc 0 T) := hc.congr (fun s hs =>
      timePrimitive_eq_interval hs f p)
    simpa using ((hcG t ht).sub (continuousWithinAt_const (b := G t p))).norm.tendsto
  have hlim : Tendsto (fun s => ∫ p, ‖G s p-G t p‖ ∂ν) (𝓝[Icc 0 T] t) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (fun p => 2*M p)
      (Eventually.of_forall (fun s => ((hGm s).sub (hGm t)).norm.aestronglyMeasurable))
      (Eventually.of_forall hbound) (hM.const_mul 2) hpoint
    simpa using h
  have he s : eLpNorm (fun p => G s p-G t p) 1 ν =
      ENNReal.ofReal (∫ p, ‖G s p-G t p‖ ∂ν) := by
    exact (eLpNorm_one_eq_lintegral_enorm).trans
      (ofReal_integral_norm_eq_lintegral_enorm ((hGi s).sub (hGi t))).symm
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  simpa only [Function.comp_def,ENNReal.ofReal_zero,← he] using h

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildCurveContinuity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A strongly continuous Eulerian representative of an integrable mild curve -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.TorusFlight

theorem timePrimitive_slice_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    {R : ℝ × Phase → ℝ} (hRm : Measurable R) (hRi : Integrable R (μ.prod volume)) (t : ℝ) :
    Integrable (fun p => Published.timePrimitive μ R (t,p)) := by
  apply hRi.integral_norm_prod_right.mono'
    (((Published.timePrimitive_measurable μ hRm).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [hRi.prod_left_ae] with p hp
  apply norm_integral_le_of_norm_le hp.norm
  filter_upwards [] with s
  change ‖if s ≤ t then R (s,p) else 0‖ ≤ ‖R (s,p)‖
  split <;> simp

theorem characteristicProfile_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a : Density} (hai : Integrable a) {R : ℝ × Phase → ℝ}
    (hRm : Measurable R) (hRi : Integrable R (μ.prod volume)) (t : ℝ) :
    Integrable (characteristicProfile μ a R t) :=
  hai.add (timePrimitive_slice_integrable hRm hRi t)

theorem eulerianProfile_L1_continuous {T : ℝ} (hT : 0 ≤ T)
    {a : Density} (hai : Integrable a) {R : ℝ × Phase → ℝ}
    (hRm : Measurable R) (hRi : Integrable R ((volume.restrict (Icc 0 T)).prod volume))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => eLpNorm (fun p =>
      eulerianProfile (volume.restrict (Icc 0 T)) a R s p-
        eulerianProfile (volume.restrict (Icc 0 T)) a R t p) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let C := characteristicProfile μ a R
  have hCt := characteristicProfile_integrable hai hRm hRi t
  have hprim := Published.timePrimitive_L1_continuous hT hRm hRi ht
  have hneg : Tendsto (fun s : ℝ => -s) (𝓝[Icc 0 T] t) (𝓝 (-t)) :=
    continuous_neg.continuousAt.tendsto.mono_left inf_le_left
  have hfixed := (tendsto_flight_L1 hCt (-t)).comp hneg
  have hi (s : ℝ) : eLpNorm (fun p => C s (flight (-s) p)-C t (flight (-s) p)) 1 volume =
      eLpNorm (fun p => Published.timePrimitive μ R (s,p)-Published.timePrimitive μ R (t,p)) 1 volume := by
    have he : (fun p => C s p-C t p) =
        (fun p => Published.timePrimitive μ R (s,p)-Published.timePrimitive μ R (t,p)) := by
      funext p
      dsimp [C,characteristicProfile]
      ring
    have hms : Measurable (fun p : Phase => Published.timePrimitive μ R (s,p)) :=
      (Published.timePrimitive_measurable μ hRm).comp (measurable_const.prodMk measurable_id)
    have hmt : Measurable (fun p : Phase => Published.timePrimitive μ R (t,p)) :=
      (Published.timePrimitive_measurable μ hRm).comp (measurable_const.prodMk measurable_id)
    have hm : Measurable (fun p => C s p-C t p) := by
      rw [he]
      exact hms.sub hmt
    exact (eLpNorm_comp_measurePreserving hm.aestronglyMeasurable
      (flight_measurePreserving (-s)) (p := 1)).trans
        (congrArg (fun h => eLpNorm h 1 (volume : Measure Phase)) he)
  have hupper := hprim.add hfixed
  simp only [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) (fun s => ?_)
  have he : (fun p => eulerianProfile μ a R s p-eulerianProfile μ a R t p) =
      (fun p => C s (flight (-s) p)-C t (flight (-s) p))+
        (fun p => C t (flight (-s) p)-C t (flight (-t) p)) := by
    funext p
    dsimp [eulerianProfile,C]
    ring
  rw [he]
  exact (eLpNorm_add_le
    (hf := by
      exact ((characteristicProfile_integrable hai hRm hRi s).1.sub hCt.1).comp_measurePreserving
        (flight_measurePreserving (-s)))
    (hg := by
      exact (hCt.1.comp_measurePreserving (flight_measurePreserving (-s))).sub
        (hCt.1.comp_measurePreserving (flight_measurePreserving (-t)))) (by norm_num : (1 : ℝ≥0∞) ≤ 1)).trans_eq (by rw [hi]; rfl)

end BoltzmannNonuniqueness.TorusFlight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedMildBalance
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Velocity-weighted balances of an integrable characteristic source -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TorusFlight

theorem velocity_weighted_profile_balance {μ : Measure ℝ} [IsFiniteMeasure μ]
    (a : Density) (R : ℝ × Phase → ℝ) (ψ : Velocity → ℝ)
    (hRm : Measurable (fun z : ℝ × Phase => ψ z.2.2*R z))
    (hRi : Integrable (fun z : ℝ × Phase => ψ z.2.2*R z) (μ.prod volume))
    (hai : Integrable (fun p : Phase => ψ p.2*a p)) (t : ℝ) :
    (∫ p : Phase, ψ p.2*eulerianProfile μ a R t p) =
      (∫ p : Phase, ψ p.2*a p)+
        ∫ s, if s ≤ t then ∫ p : Phase, ψ p.2*R (s,p) else 0 ∂μ := by
  let W : ℝ × Phase → ℝ := fun z => ψ z.2.2*R z
  have hp : ∀ p : Phase, ψ p.2*Published.timePrimitive μ R (t,p) =
      Published.timePrimitive μ W (t,p) := by
    intro p
    change ψ p.2*(∫ s, if s ≤ t then R (s,p) else 0 ∂μ) =
      ∫ s, if s ≤ t then ψ p.2*R (s,p) else 0 ∂μ
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with s
    split_ifs <;> simp
  calc
    _ = ∫ p : Phase, ψ p.2*characteristicProfile μ a R t p := by
      have h := integral_flight (fun p : Phase => ψ p.2*characteristicProfile μ a R t p) (-t)
      exact h
    _ = ∫ p : Phase, ψ p.2*a p+Published.timePrimitive μ W (t,p) := by
      congr 1
      funext p
      dsimp [characteristicProfile]
      rw [mul_add,hp]
    _ = (∫ p : Phase, ψ p.2*a p)+(∫ p, Published.timePrimitive μ W (t,p)) :=
      integral_add hai (timePrimitive_slice_integrable hRm hRi t)
    _ = _ := by rw [Published.integral_timePrimitive hRi]

end BoltzmannNonuniqueness.TorusFlight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildRenormalization
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A strongly continuous representative of the constructed local mild solution -/

noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal

namespace BoltzmannNonuniqueness

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem source_measurable (S : MildCollisionSolution T f₀ g) : Measurable (source g) :=
  (CollisionCompactness.gainDensity_measurable S.measurable).sub
    (CollisionCompactness.lossDensity_measurable S.measurable)

theorem characteristicSource_measurable (S : MildCollisionSolution T f₀ g) :
    Measurable (characteristicSource g) :=
  (S.source_measurable.comp MeasurableEquiv.prodAssoc.symm.measurable).comp
    (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).measurable

theorem characteristicSource_integrable (S : MildCollisionSolution T f₀ g) :
    Integrable (characteristicSource g) ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  have hterms := CollisionCompactness.gainLoss_integrable S.measurable S.nonnegative S.pair_integrable
  have hi := (measurePreserving_prodAssoc (volume.restrict (Icc 0 T))
    (volume : Measure Position) (volume : Measure Velocity)).symm.integrable_comp_of_integrable
      (hterms.1.sub hterms.2)
  have hr : Integrable (TorusFlight.regroup (source g))
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
    rw [Measure.volume_eq_prod]
    exact hi
  exact (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable hr

theorem evolution_eq_ae (S : MildCollisionSolution T f₀ g) :
    TorusFlight.regroup g =ᵐ[(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
      (fun z => evolution T f₀ g z.1 z.2) := by
  have h := (TorusFlight.back_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae
    S.characteristic
  filter_upwards [h] with z hz
  change TorusFlight.regroup g (z.1,TorusFlight.flight z.1 (TorusFlight.flight (-z.1) z.2)) = _ at hz
  rw [TorusFlight.neg_flight] at hz
  exact hz

theorem evolution_strong_continuity (S : MildCollisionSolution T f₀ g)
    (hT : 0 ≤ T) (hf₀ : Integrable f₀) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Filter.Tendsto (fun s => eLpNorm (fun p => evolution T f₀ g s p-evolution T f₀ g t p) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) :=
  TorusFlight.eulerianProfile_L1_continuous hT hf₀ S.characteristicSource_measurable
    S.characteristicSource_integrable ht

theorem evolution_initial (hT : 0 ≤ T) (p : Phase) : evolution T f₀ g 0 p = f₀ p := by
  change f₀ (TorusFlight.flight (-0) p)+Published.timePrimitive (volume.restrict (Icc 0 T))
    (characteristicSource g) (0,TorusFlight.flight (-0) p) = f₀ p
  simp only [neg_zero,TorusFlight.flight_zero]
  rw [Published.timePrimitive_eq_interval ⟨le_rfl,hT⟩,intervalIntegral.integral_same,add_zero]

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

section

/-! # Renormalization along almost every actual mild characteristic -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem continuous_path_nonnegative_of_ae {T : ℝ} {u : ℝ → ℝ}
    (hT : 0 < T) (hu : ContinuousOn u (Icc 0 T))
    (hn : ∀ᵐ t ∂volume.restrict (Icc 0 T), 0 ≤ u t) :
    ∀ t ∈ Icc 0 T, 0 ≤ u t := by
  have he : u =ᵐ[volume.restrict (Icc 0 T)] (fun t => max (u t) 0) := by
    filter_upwards [hn] with t ht
    exact (max_eq_left ht).symm
  have heq := Measure.eqOn_Icc_of_ae_eq volume hT.ne he hu (hu.sup continuousOn_const)
  intro t ht
  rw [heq ht]
  exact le_max_right _ _

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem nonnegative_integral_paths (S : MildCollisionSolution T f₀ g) (hT : 0 < T) :
    ∀ᵐ p : Phase, ∀ t ∈ Icc 0 T, 0 ≤ entropyPath f₀ (characteristicSource g) t p := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hp : ∀ᵐ z ∂μ.prod (volume : Measure Phase),
      0 ≤ f₀ z.2+Published.timePrimitive μ (characteristicSource g) z := by
    filter_upwards [S.characteristic] with z hz
    change TorusFlight.along (TorusFlight.regroup g) z =
      f₀ z.2+Published.timePrimitive μ (characteristicSource g) z at hz
    rw [← hz]
    exact S.nonnegative _
  have hp' := (Measure.measurePreserving_swap (μ := (volume : Measure Phase)) (ν := μ)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hp',S.characteristicSource_integrable.prod_left_ae] with p hpos hri
  have hi : IntervalIntegrable (fun t => characteristicSource g (t,p)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hri
  have hc : ContinuousOn (fun t => entropyPath f₀ (characteristicSource g) t p) (Icc 0 T) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hi
      (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
    rw [uIcc_of_le hT.le] at h
    exact continuousOn_const.add h
  apply continuous_path_nonnegative_of_ae hT hc
  filter_upwards [hpos,ae_restrict_mem measurableSet_Icc] with t ht hmem
  change 0 ≤ f₀ p+Published.timePrimitive (volume.restrict (Icc 0 T)) (characteristicSource g) (t,p) at ht
  rwa [Published.timePrimitive_eq_interval hmem] at ht

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

section

/-! # The actual mild solution satisfies the tested renormalized path identity -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem renormalized_tested_paths (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (β : Renormalization) (φ : KineticTest) :
    ∀ᵐ p : Phase,
      (∫ t in (0:ℝ)..T,
        derivWithin β.toFun (Ici 0) (entropyPath f₀ (characteristicSource g) t p/maxwellian p.2)*
          characteristicSource g (t,p)*φ.toFun t (TorusFlight.flight t p).1 p.2+
        maxwellian p.2*β.toFun (entropyPath f₀ (characteristicSource g) t p/maxwellian p.2)*
          φ.transportDerivative t (TorusFlight.flight t p)) =
        maxwellian p.2*β.toFun (entropyPath f₀ (characteristicSource g) T p/maxwellian p.2)*
          φ.toFun T (TorusFlight.flight T p).1 p.2-
        maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2 := by
  filter_upwards [S.nonnegative_integral_paths hT,S.characteristicSource_integrable.prod_left_ae]
    with p hn hri
  have hi : IntervalIntegrable (fun t => characteristicSource g (t,p)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hri
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f₀ p) 0 T := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  have hpath : AbsolutelyContinuousOnInterval (fun t => entropyPath f₀ (characteristicSource g) t p) 0 T :=
    hconst.add hp
  have hd : ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (fun t => entropyPath f₀ (characteristicSource g) t p) (characteristicSource g (t,p)) t := by
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    exact (ht (by simpa only [uIcc_of_le hT.le] using hmem) 0 left_mem_uIcc).const_add (f₀ p)
  have hφ : AbsolutelyContinuousOnInterval
      (fun t => φ.toFun t (TorusFlight.flight t p).1 p.2) 0 T :=
    ((φ.contDiff_along p).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn.absolutelyContinuousOnInterval
  have hφ' : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt
      (fun t => φ.toFun t (TorusFlight.flight t p).1 p.2)
      (φ.transportDerivative t (TorusFlight.flight t p)) t :=
    ae_of_all _ (fun t _ => φ.hasDerivAt_along p t)
  simpa only [entropyPath,intervalIntegral.integral_same,add_zero,TorusFlight.flight_zero] using
    β.weighted_tested_chain_rule hT.le (maxwellian_pos p.2) hpath hn hd hφ hφ'

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # The unrenormalized local mass test identity on each mild characteristic -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem tested_absolutelyContinuous_path {T : ℝ} {F r ψ ψ' : ℝ → ℝ}
    (hT : 0 ≤ T) (hF : AbsolutelyContinuousOnInterval F 0 T)
    (hr : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt F (r t) t)
    (hψ : AbsolutelyContinuousOnInterval ψ 0 T)
    (hψ' : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt ψ (ψ' t) t) :
    (∫ t in (0:ℝ)..T, r t*ψ t+F t*ψ' t) = F T*ψ T-F 0*ψ 0 := by
  calc
    _ = ∫ t in (0:ℝ)..T, deriv F t*ψ t+F t*deriv ψ t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hr,hψ'] with t ht hpt hmem
      have htcc : t ∈ Icc 0 T := by
        exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le hT] using hmem)
      rw [(ht htcc).deriv,(hpt htcc).deriv]
    _ = _ := hF.integral_deriv_mul_eq_sub hψ

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem mass_tested_paths (S : MildCollisionSolution T f₀ g) (hT : 0 < T) (φ : MassTest) :
    ∀ᵐ p : Phase,
      (∫ t in (0:ℝ)..T, characteristicSource g (t,p)*φ.toFun t (TorusFlight.flight t p).1+
        entropyPath f₀ (characteristicSource g) t p*φ.transportDerivative t (TorusFlight.flight t p)) =
        entropyPath f₀ (characteristicSource g) T p*φ.toFun T (TorusFlight.flight T p).1-
          f₀ p*φ.toFun 0 p.1 := by
  filter_upwards [S.characteristicSource_integrable.prod_left_ae] with p hri
  have hi : IntervalIntegrable (fun t => characteristicSource g (t,p)) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hri
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 T)
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f₀ p) 0 T := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  have hpath : AbsolutelyContinuousOnInterval (fun t => entropyPath f₀ (characteristicSource g) t p) 0 T :=
    hconst.add hp
  have hd : ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (fun t => entropyPath f₀ (characteristicSource g) t p) (characteristicSource g (t,p)) t := by
    filter_upwards [hi.ae_hasDerivAt_integral] with t ht hmem
    exact (ht (by simpa only [uIcc_of_le hT.le] using hmem) 0 left_mem_uIcc).const_add (f₀ p)
  have hφ : AbsolutelyContinuousOnInterval (fun t => φ.toFun t (TorusFlight.flight t p).1) 0 T :=
    ((φ.contDiff_along p).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffOn.absolutelyContinuousOnInterval
  have hφ' : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt (fun t => φ.toFun t (TorusFlight.flight t p).1)
      (φ.transportDerivative t (TorusFlight.flight t p)) t :=
    ae_of_all _ (fun t _ => φ.hasDerivAt_along p t)
  simpa only [entropyPath,intervalIntegral.integral_same,add_zero,TorusFlight.flight_zero] using
    tested_absolutelyContinuous_path hT.le hpath hd hφ hφ'

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveMildRepresentative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A nonnegative strongly continuous representative with the exact initial trace -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem evolution_measurable (S : MildCollisionSolution T f₀ g) (hf₀ : Measurable f₀) :
    Measurable (fun z : ℝ × Phase => evolution T f₀ g z.1 z.2) := by
  have hm := (hf₀.comp measurable_snd).add
    (Published.timePrimitive_measurable (volume.restrict (Icc 0 T)) S.characteristicSource_measurable)
  exact hm.comp (TorusFlight.back_measurePreserving (volume.restrict (Icc 0 T))).measurable

theorem positiveEvolution_measurable (S : MildCollisionSolution T f₀ g) (hf₀ : Measurable f₀) :
    Measurable (fun z : ℝ × Phase => positiveEvolution T f₀ g z.1 z.2) :=
  (S.evolution_measurable hf₀).max measurable_const

theorem positiveEvolution_nonnegative (t : ℝ) (p : Phase) : 0 ≤ positiveEvolution T f₀ g t p :=
  le_max_right _ _

theorem positiveEvolution_eq_ae (S : MildCollisionSolution T f₀ g) :
    TorusFlight.regroup g =ᵐ[(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
      (fun z => positiveEvolution T f₀ g z.1 z.2) := by
  filter_upwards [S.evolution_eq_ae] with z hz
  change TorusFlight.regroup g z = max (evolution T f₀ g z.1 z.2) 0
  rw [← hz]
  exact (max_eq_left (S.nonnegative ((z.1,z.2.1),z.2.2))).symm

theorem positiveEvolution_initial (hT : 0 ≤ T) (hf₀ : ∀ p, 0 ≤ f₀ p) (p : Phase) :
    positiveEvolution T f₀ g 0 p = f₀ p := by
  rw [positiveEvolution,evolution_initial hT,max_eq_left (hf₀ p)]

theorem positiveEvolution_strong_continuity (S : MildCollisionSolution T f₀ g)
    (hT : 0 ≤ T) (hf₀m : Measurable f₀) (hf₀ : Integrable f₀)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => eLpNorm (fun p => positiveEvolution T f₀ g s p-positiveEvolution T f₀ g t p)
      1 volume) (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hm s : Measurable (fun p => positiveEvolution T f₀ g s p) :=
    (S.positiveEvolution_measurable hf₀m).comp (measurable_const.prodMk measurable_id)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (S.evolution_strong_continuity hT hf₀ ht) (fun _ => zero_le)
  intro s
  apply eLpNorm_mono
  intro p
  exact abs_max_sub_max_le_abs _ _ _

theorem positiveEvolution_integrable (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) (hf₀ : Integrable f₀) (t : ℝ) :
    Integrable (positiveEvolution T f₀ g t) := by
  have hi := (TorusFlight.flight_measurePreserving (-t)).integrable_comp_of_integrable
    (TorusFlight.characteristicProfile_integrable hf₀ S.characteristicSource_measurable
      S.characteristicSource_integrable t)
  apply hi.norm.mono'
    (((S.positiveEvolution_measurable hf₀m).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [] with p
  change ‖max (evolution T f₀ g t p) 0‖ ≤ ‖evolution T f₀ g t p‖
  simp only [Real.norm_eq_abs]
  simpa only [sub_zero,max_self] using abs_max_sub_max_le_abs (evolution T f₀ g t p) 0 0

end BoltzmannNonuniqueness.MildCollisionSolution

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_StrongMildRepresentative
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Collision integrability for the strong nonnegative mild representative -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem kineticDensity_gain (F : Evolution) (z : ℝ × Phase) :
    TorusFlight.regroup (CollisionCompactness.gainDensity (kineticDensity F)) z =
      gain (F z.1) z.2.1 z.2.2 := by
  rw [TorusFlight.regroup,CollisionCompactness.gainDensity_formula]
  rfl

theorem kineticDensity_loss (F : Evolution) (z : ℝ × Phase) :
    TorusFlight.regroup (CollisionCompactness.lossDensity (kineticDensity F)) z =
      loss (F z.1) z.2.1 z.2.2 := rfl

theorem kineticDensity_collision (F : Evolution) (z : ℝ × Phase) :
    TorusFlight.regroup (MildCollisionSolution.source (kineticDensity F)) z =
      collision (F z.1) z.2.1 z.2.2 := by
  change TorusFlight.regroup (CollisionCompactness.gainDensity (kineticDensity F)) z -
    TorusFlight.regroup (CollisionCompactness.lossDensity (kineticDensity F)) z = _
  rw [kineticDensity_gain,kineticDensity_loss]
  rfl

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem positiveDensity_measurable (S : MildCollisionSolution T f₀ g)
    (hf₀ : Measurable f₀) : Measurable (kineticDensity (positiveEvolution T f₀ g)) :=
  (S.positiveEvolution_measurable hf₀).comp MeasurableEquiv.prodAssoc.measurable

theorem positiveDensity_eq_ae (S : MildCollisionSolution T f₀ g) :
    g =ᵐ[(AnnularEnvelope.timePositionVolume T).prod volume]
      kineticDensity (positiveEvolution T f₀ g) :=
  (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae
    S.positiveEvolution_eq_ae

theorem positiveDensity_pair_integrable (S : MildCollisionSolution T f₀ g)
    (hf₀ : Measurable f₀) :
    Integrable (CollisionCompactness.pairDensity (kineticDensity (positiveEvolution T f₀ g)))
      ((AnnularEnvelope.timePositionVolume T).prod volume) :=
  S.pair_integrable.congr (CollisionCompactness.pairDensity_congr
    S.measurable (S.positiveDensity_measurable hf₀) S.positiveDensity_eq_ae)

theorem positiveEvolution_strongEarly (S : MildCollisionSolution T f₀ g)
    (hT : 0 < T) (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) :
    StrongEarly T (positiveEvolution T f₀ g) := by
  let F := positiveEvolution T f₀ g
  have hm := S.positiveDensity_measurable hf₀m
  have hn : ∀ z, 0 ≤ kineticDensity F z := fun z => positiveEvolution_nonnegative _ _
  have hi := CollisionCompactness.gainLoss_integrable hm hn (S.positiveDensity_pair_integrable hf₀m)
  have hgain := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable hi.1
  have hloss := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable hi.2
  refine ⟨hT,fun _ ht => S.positiveEvolution_strong_continuity hT.le hf₀m hf₀i ht,?_,?_⟩
  · change Integrable _ _
    rw [← phaseInterval_measure]
    have he : (CollisionCompactness.gainDensity (kineticDensity (positiveEvolution T f₀ g)) ∘
        MeasurableEquiv.prodAssoc.symm) =
        (fun z : ℝ × Phase => gain (positiveEvolution T f₀ g z.1) z.2.1 z.2.2) := by
      funext z
      exact kineticDensity_gain _ z
    rw [he] at hgain
    exact hgain
  · change Integrable _ _
    rw [← phaseInterval_measure]
    exact hloss

theorem positiveEvolution_collision_fibers (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) :
    ∀ᵐ p ∂volume.restrict (boundedTimes T),
      Integrable (fun q : Velocity × Sphere =>
        collisionKernel p.2.2 q.1 q.2 *
          positiveEvolution T f₀ g p.1 (p.2.1,scatterLeft p.2.2 q.1 q.2) *
          positiveEvolution T f₀ g p.1 (p.2.1,scatterRight p.2.2 q.1 q.2))
        ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q : Velocity × Sphere =>
        collisionKernel p.2.2 q.1 q.2 * positiveEvolution T f₀ g p.1 p.2 *
          positiveEvolution T f₀ g p.1 (p.2.1,q.1))
        ((volume : Measure Velocity).prod sphereArea) := by
  have h := CollisionCompactness.collision_fibers (S.positiveDensity_measurable hf₀m)
    (fun z => positiveEvolution_nonnegative z.1.1 (z.1.2,z.2))
    (S.positiveDensity_pair_integrable hf₀m)
  rw [← phaseInterval_measure]
  exact (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.quasiMeasurePreserving.ae h

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_L1CurveEquality
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spacetime equality determines a strongly continuous L¹ curve at every time -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem strong_ae_eq_all_times {T : ℝ} (hT : 0 < T) {F G : Evolution}
    (hFi : ∀ t, Integrable (F t)) (hGi : ∀ t, Integrable (G t))
    (hFc : ∀ t ∈ Icc 0 T,
      Tendsto (fun s => eLpNorm (fun p => F s p-F t p) 1 volume) (𝓝[Icc 0 T] t) (𝓝 0))
    (hGc : ∀ t ∈ Icc 0 T,
      Tendsto (fun s => eLpNorm (fun p => G s p-G t p) 1 volume) (𝓝[Icc 0 T] t) (𝓝 0))
    (he : (fun z : ℝ × Phase => F z.1 z.2) =ᵐ[(volume.restrict (Icc 0 T)).prod volume]
      (fun z => G z.1 z.2)) : ∀ t ∈ Icc 0 T, F t =ᵐ[volume] G t := by
  let F₁ (t : ℝ) : Lp ℝ 1 (volume : Measure Phase) := (memLp_one_iff_integrable.mpr (hFi t)).toLp (F t)
  let G₁ (t : ℝ) : Lp ℝ 1 (volume : Measure Phase) := (memLp_one_iff_integrable.mpr (hGi t)).toLp (G t)
  have hFrep t : F₁ t =ᵐ[volume] F t := (memLp_one_iff_integrable.mpr (hFi t)).coeFn_toLp
  have hGrep t : G₁ t =ᵐ[volume] G t := (memLp_one_iff_integrable.mpr (hGi t)).coeFn_toLp
  have hFcont : ContinuousOn F₁ (Icc 0 T) := by
    intro t ht
    apply tendsto_iff_edist_tendsto_0.mpr
    have hedist s : edist (F₁ s) (F₁ t) = eLpNorm (fun p => F s p-F t p) 1 volume := by
      rw [Lp.edist_def]
      exact eLpNorm_congr_ae ((hFrep s).sub (hFrep t))
    simpa only [hedist] using hFc t ht
  have hGcont : ContinuousOn G₁ (Icc 0 T) := by
    intro t ht
    apply tendsto_iff_edist_tendsto_0.mpr
    have hedist s : edist (G₁ s) (G₁ t) = eLpNorm (fun p => G s p-G t p) 1 volume := by
      rw [Lp.edist_def]
      exact eLpNorm_congr_ae ((hGrep s).sub (hGrep t))
    simpa only [hedist] using hGc t ht
  have he₁ : F₁ =ᵐ[volume.restrict (Icc 0 T)] G₁ := by
    filter_upwards [Measure.ae_ae_of_ae_prod he] with t ht
    change F t =ᵐ[volume] G t at ht
    exact Lp.ext ((hFrep t).trans (ht.trans (hGrep t).symm))
  have heq := Measure.eqOn_Icc_of_ae_eq (volume : Measure ℝ) (ne_of_lt hT)
    he₁ hFcont hGcont
  intro t ht
  have hrep : F₁ t =ᵐ[volume] G₁ t := by rw [heq ht]
  exact (hFrep t).symm.trans (hrep.trans (hGrep t))

namespace MildCollisionSolution

theorem evolution_eq_positive_each_time {T : ℝ} {f₀ : Density}
    {g : (ℝ × Position) × Velocity → ℝ}
    (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) :
    ∀ t ∈ Icc 0 T, evolution T f₀ g t =ᵐ[volume] positiveEvolution T f₀ g t := by
  have hi t : Integrable (evolution T f₀ g t) :=
    (TorusFlight.flight_measurePreserving (-t)).integrable_comp_of_integrable
      (TorusFlight.characteristicProfile_integrable hf₀i S.characteristicSource_measurable
        S.characteristicSource_integrable t)
  exact strong_ae_eq_all_times hT hi (S.positiveEvolution_integrable hf₀m hf₀i)
    (fun t ht => S.evolution_strong_continuity hT.le hf₀i ht)
    (fun t ht => S.positiveEvolution_strong_continuity hT.le hf₀m hf₀i ht)
    (S.evolution_eq_ae.symm.trans S.positiveEvolution_eq_ae)

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildRenormalizedBalance
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The canonical integral paths agree with every-time physical traces -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem evolution_along_eq_path {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    evolution T f₀ g t (TorusFlight.flight t p) = entropyPath f₀ (characteristicSource g) t p := by
  unfold evolution TorusFlight.eulerianProfile
  rw [TorusFlight.flight_neg]
  change f₀ p+Published.timePrimitive (volume.restrict (Icc 0 T)) (characteristicSource g) (t,p) = _
  rw [Published.timePrimitive_eq_interval ht]
  rfl

theorem positiveEvolution_along_eq_path (S : MildCollisionSolution T f₀ g)
    (hT : 0 < T) (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun p => positiveEvolution T f₀ g t (TorusFlight.flight t p)) =ᵐ[volume]
      (fun p => entropyPath f₀ (characteristicSource g) t p) := by
  have h := (TorusFlight.flight_measurePreserving t).quasiMeasurePreserving.ae
    (S.evolution_eq_positive_each_time hT hf₀m hf₀i t ht)
  filter_upwards [h] with p hp
  exact hp.symm.trans (evolution_along_eq_path ht p)

theorem positiveEvolution_along_eq_path_spacetime (S : MildCollisionSolution T f₀ g) :
    (fun z : ℝ × Phase => positiveEvolution T f₀ g z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
      (fun z => entropyPath f₀ (characteristicSource g) z.1 z.2) := by
  have h := (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae
    (S.evolution_eq_ae.symm.trans S.positiveEvolution_eq_ae)
  have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [h,ht] with z hz htz
  exact hz.symm.trans (evolution_along_eq_path htz z.2)

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # The nonnegative strong representative satisfies the actual nonlinear mild equation -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

namespace Published

theorem timePrimitive_congr {P : Type*} [MeasurableSpace P]
    {μ : Measure ℝ} {ν : Measure P} [SFinite μ] [SFinite ν]
    {f g : ℝ × P → ℝ} (he : f =ᵐ[μ.prod ν] g) :
    timePrimitive μ f =ᵐ[μ.prod ν] timePrimitive μ g := by
  have hs := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae he)
  have ht := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hs
  filter_upwards [ht] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with s hs
  change f (s,z.2) = g (s,z.2) at hs
  rw [hs]

end Published

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem positiveDensity_source_eq_ae (S : MildCollisionSolution T f₀ g)
    (hf₀ : Measurable f₀) :
    source g =ᵐ[(AnnularEnvelope.timePositionVolume T).prod volume]
      source (kineticDensity (positiveEvolution T f₀ g)) := by
  have h := CollisionCompactness.gainLoss_congr
    S.measurable (S.positiveDensity_measurable hf₀) S.positiveDensity_eq_ae
  exact h.1.sub h.2

theorem positiveEvolution_characteristic (S : MildCollisionSolution T f₀ g)
    (hf₀ : Measurable f₀) :
    (fun z : ℝ × Phase => positiveEvolution T f₀ g z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
    (fun z => f₀ z.2 + Published.timePrimitive (volume.restrict (Icc 0 T))
      (fun w => collision (positiveEvolution T f₀ g w.1)
        (TorusFlight.flight w.1 w.2).1 (TorusFlight.flight w.1 w.2).2) z) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let F := positiveEvolution T f₀ g
  have hf : TorusFlight.regroup (kineticDensity F) =ᵐ[μ.prod volume] TorusFlight.regroup g :=
    S.positiveEvolution_eq_ae.symm
  have hs := (kineticGrouping_measurePreserving μ).symm.quasiMeasurePreserving.ae
    (S.positiveDensity_source_eq_ae hf₀)
  have ha : characteristicSource g =ᵐ[μ.prod volume] characteristicSource (kineticDensity F) :=
    (TorusFlight.along_measurePreserving μ).quasiMeasurePreserving.ae hs
  have hp := Published.timePrimitive_congr ha
  have hal : TorusFlight.along (TorusFlight.regroup (kineticDensity F)) =ᵐ[μ.prod volume]
      TorusFlight.along (TorusFlight.regroup g) :=
    (TorusFlight.along_measurePreserving μ).quasiMeasurePreserving.ae hf
  have he := hal.trans S.characteristic
  have heq : (fun w : ℝ × Phase => collision (F w.1)
      (TorusFlight.flight w.1 w.2).1 (TorusFlight.flight w.1 w.2).2) =
      characteristicSource (kineticDensity F) := by
    funext w
    exact (kineticDensity_collision F (w.1,TorusFlight.flight w.1 w.2)).symm
  filter_upwards [he,hp] with z hz hpz
  change F z.1 (TorusFlight.flight z.1 z.2) = f₀ z.2+Published.timePrimitive μ
    (characteristicSource g) z at hz
  rw [hpz] at hz
  change F z.1 (TorusFlight.flight z.1 z.2) = _
  rw [heq]
  exact hz

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

section

/-! # The physical renormalized collision term in characteristic coordinates -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem positiveEvolution_along_collision_eq_source (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) :
    characteristicSource g =ᵐ[(volume.restrict (Icc 0 T)).prod volume]
      (fun z => collision (positiveEvolution T f₀ g z.1)
        (TorusFlight.flight z.1 z.2).1 (TorusFlight.flight z.1 z.2).2) := by
  have hs := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.quasiMeasurePreserving.ae
    (S.positiveDensity_source_eq_ae hf₀m)
  have ha := (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae hs
  filter_upwards [ha] with z hz
  exact hz.trans (kineticDensity_collision _ (z.1,TorusFlight.flight z.1 z.2))

theorem renormalizedIntegrand_along_eq (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) (β : Renormalization) (φ : KineticTest) :
    TorusFlight.along (renormalizedIntegrand (positiveEvolution T f₀ g) β φ) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
      (fun z => derivWithin β.toFun (Ici 0)
          (entropyPath f₀ (characteristicSource g) z.1 z.2/maxwellian z.2.2)*
          characteristicSource g z*φ.toFun z.1 (TorusFlight.flight z.1 z.2).1 z.2.2+
        maxwellian z.2.2*β.toFun (entropyPath f₀ (characteristicSource g) z.1 z.2/maxwellian z.2.2)*
          φ.transportDerivative z.1 (TorusFlight.flight z.1 z.2)) := by
  filter_upwards [S.positiveEvolution_along_eq_path_spacetime,
    S.positiveEvolution_along_collision_eq_source hf₀m] with z hf hr
  dsimp only [TorusFlight.along,renormalizedIntegrand,relativeDensity]
  rw [hf,← hr]
  simp only [TorusFlight.flight]
  ring

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # The actual strong representative has integrable renormalized weak terms -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem positiveEvolution_spacetime_integrable (S : MildCollisionSolution T f₀ g) :
    Integrable (fun z : ℝ × Phase => positiveEvolution T f₀ g z.1 z.2)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  have hi := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable
    S.integrable
  exact hi.congr S.positiveEvolution_eq_ae

theorem positiveEvolution_collision_integrable (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) :
    Integrable (fun z : ℝ × Phase => collision (positiveEvolution T f₀ g z.1) z.2.1 z.2.2)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  have hi := CollisionCompactness.gainLoss_integrable (S.positiveDensity_measurable hf₀m)
    (fun z => positiveEvolution_nonnegative z.1.1 (z.1.2,z.2))
    (S.positiveDensity_pair_integrable hf₀m)
  have h := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable
    (hi.1.sub hi.2)
  exact h.congr (Filter.Eventually.of_forall (kineticDensity_collision _))

theorem renormalized_integrable (S : MildCollisionSolution T f₀ g) (hf₀m : Measurable f₀)
    (β : Renormalization) (φ : KineticTest) :
    IntegrableOn (renormalizedIntegrand (positiveEvolution T f₀ g) β φ) (boundedTimes T) :=
  renormalizedIntegrand_integrable (S.positiveEvolution_measurable hf₀m)
    positiveEvolution_nonnegative S.positiveEvolution_spacetime_integrable
    (S.positiveEvolution_collision_integrable hf₀m) β φ

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # The weak renormalized equation for the actual local mild solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness



namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem renormalized_balance (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) (hf₀n : ∀ p, 0 ≤ f₀ p)
    (β : Renormalization) (φ : KineticTest) :
    (∫ z in boundedTimes T, renormalizedIntegrand (positiveEvolution T f₀ g) β φ z) =
      (∫ p : Phase, maxwellian p.2*β.toFun (positiveEvolution T f₀ g T p/maxwellian p.2)*
        φ.toFun T p.1 p.2)-
      (∫ p : Phase, maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let F := positiveEvolution T f₀ g
  let I := renormalizedIntegrand F β φ
  let B : Phase → ℝ := fun p => maxwellian p.2*β.toFun (F T p/maxwellian p.2)*φ.toFun T p.1 p.2
  let B₀ : Phase → ℝ := fun p => maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2
  have hIi : Integrable I (μ.prod volume) := by
    have h := S.renormalized_integrable hf₀m β φ
    change Integrable I _ at h
    rwa [← phaseInterval_measure] at h
  have hAi := (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hIi
  have hBm : Measurable (F T) := (S.positiveEvolution_measurable hf₀m).comp
    (measurable_const.prodMk measurable_id)
  have hBi : Integrable B := φ.weighted_slice_integrable β ⟨hT.le,le_rfl⟩ hBm
    (positiveEvolution_nonnegative T) (S.positiveEvolution_integrable hf₀m hf₀i T)
  have hB₀i : Integrable B₀ := φ.weighted_slice_integrable β ⟨le_rfl,hT.le⟩ hf₀m hf₀n hf₀i
  have hp : ∀ᵐ p : Phase,
      (∫ t, TorusFlight.along I (t,p) ∂μ) = B (TorusFlight.flight T p)-B₀ p := by
    have he := Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := (volume : Measure Phase)) (ν := μ)).quasiMeasurePreserving.ae
        (S.renormalizedIntegrand_along_eq hf₀m β φ))
    filter_upwards [S.renormalized_tested_paths hT β φ,he,
      S.positiveEvolution_along_eq_path hT hf₀m hf₀i ⟨hT.le,le_rfl⟩] with p hp he hend
    rw [intervalIntegral.integral_of_le hT.le,← integral_Icc_eq_integral_Ioc] at hp
    calc
      _ = _ := integral_congr_ae he
      _ = _ := hp
      _ = _ := by
        dsimp only [B,B₀,F]
        rw [hend]
        rfl
  calc
    _ = ∫ z, I z ∂μ.prod volume := by rw [phaseInterval_measure]
    _ = ∫ z, TorusFlight.along I z ∂μ.prod volume := (TorusFlight.integral_along hIi).symm
    _ = ∫ p : Phase, ∫ t, TorusFlight.along I (t,p) ∂μ := integral_prod_symm _ hAi
    _ = ∫ p : Phase, B (TorusFlight.flight T p)-B₀ p := integral_congr_ae hp
    _ = (∫ p : Phase, B (TorusFlight.flight T p))-(∫ p : Phase, B₀ p) :=
      integral_sub ((TorusFlight.flight_measurePreserving T).integrable_comp_of_integrable hBi) hB₀i
    _ = _ := by rw [TorusFlight.integral_flight]

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_LocalAdmissibility
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual cold datum has a nonnegative strong local mild solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem MildCollisionSolution.localMildSolution
    {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}
    (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) (hf₀n : ∀ p, 0 ≤ f₀ p) :
    LocalMildSolution T f₀ (MildCollisionSolution.positiveEvolution T f₀ g) where
  strong := S.positiveEvolution_strongEarly hT hf₀m hf₀i
  measurable := S.positiveEvolution_measurable hf₀m
  nonnegative := MildCollisionSolution.positiveEvolution_nonnegative
  initial := funext (MildCollisionSolution.positiveEvolution_initial hT.le hf₀n)
  integrable_each_time := S.positiveEvolution_integrable hf₀m hf₀i
  pair_integrable := S.positiveDensity_pair_integrable hf₀m
  characteristic := S.positiveEvolution_characteristic hf₀m

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_EnergyCollisionMarginals
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Both collision rates are integrable with the energy weight -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem preRate_energy_integrable {μ : Measure X} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hi : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (fun z => ‖z.1.2.1‖^2*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hd := (hi.const_mul 7).comp_fst sphereArea
  apply hd.mono' (by
    exact ((measurable_fst.snd.fst.norm.pow_const 2).mul (preRate_measurable hfm)).aestronglyMeasurable)
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (preRate_nonneg hfn z))]
  calc
    _ = (‖z.1.2.1‖^2*collisionKernel z.1.2.1 z.1.2.2 z.2)*f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) := by
      unfold preRate
      ring
    _ ≤ (7*VelocityMoment.weight z.1.2.1*VelocityMoment.weight z.1.2.2)*
        f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (VelocityMoment.norm_sq_kernel_le_weight _ _ _) (hfn _)) (hfn _)
    _ = _ := by unfold exponentialPair; ring

theorem preRate_other_energy_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hi : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (fun z => ‖z.1.2.2‖^2*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable
    (preRate_energy_integrable hfm hfn hi)
  simp only [Function.comp_def,preRate_particleSwap] at h
  exact h

theorem postRate_energy_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hi : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (fun z => ‖z.1.2.1‖^2*postRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hs := (preRate_energy_integrable hfm hfn hi).add (preRate_other_energy_integrable hfm hfn hi)
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2*preRate f z) := by
    apply Measurable.mul _ (preRate_measurable hfm)
    unfold scatterLeft normalComponent
    fun_prop
  have hl : Integrable (fun z => ‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    apply hs.mono' hm.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (preRate_nonneg hfn z))]
    have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
    have he := scatter_energy z.1.2.1 z.1.2.2 z.2 hw
    have hle : ‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2 ≤ ‖z.1.2.1‖^2+‖z.1.2.2‖^2 := by
      nlinarith [sq_nonneg ‖scatterRight z.1.2.1 z.1.2.2 z.2‖]
    exact (mul_le_mul_of_nonneg_right hle (preRate_nonneg hfn z)).trans_eq (by
      exact add_mul _ _ _)
  have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hl
  have he : (fun z : (X × (Velocity × Velocity)) × Sphere =>
      ‖scatterLeft (scatterTriple z).1.2.1 (scatterTriple z).1.2.2 (scatterTriple z).2‖^2*
        preRate f (scatterTriple z)) = (fun z => ‖z.1.2.1‖^2*postRate f z) := by
    funext z
    have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
    change ‖scatterLeft (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2‖^2*preRate f (scatterTriple z) = _
    rw [scatterLeft_involutive _ _ _ hw]
    rfl
  change Integrable (fun z => ‖scatterLeft (scatterTriple z).1.2.1
    (scatterTriple z).1.2.2 (scatterTriple z).2‖^2*preRate f (scatterTriple z)) _ at h
  rw [he] at h
  exact h

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Energy-weighted gain and loss integrability for the local solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

namespace CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem gainLoss_energy_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hi : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (fun p => ‖p.2‖^2*gainDensity f p) (μ.prod volume) ∧
      Integrable (fun p => ‖p.2‖^2*lossDensity f p) (μ.prod volume) := by
  exact ⟨(collision_test_marginal (postRate f) (fun p => ‖p.2‖^2)
      (postRate_energy_integrable hfm hfn hi)).1,
    (collision_test_marginal (preRate f) (fun p => ‖p.2‖^2)
      (preRate_energy_integrable hfm hfn hi)).1⟩

end CollisionCompactness

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionConservation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Mass, scalar momentum, and energy balances for the full collision operator -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem full_test_collision_invariant {μ : Measure X} [SFinite μ]
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*postRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hψ : ∀ z, collisionJump ψ z = 0) :
    (∫ p, ψ p*gainDensity f p ∂μ.prod volume) =
      ∫ p, ψ p*lossDensity f p ∂μ.prod volume := by
  exact (collision_test_marginal (postRate f) ψ hpost).2.trans
    ((full_collision_invariant f ψ hpre hpost hψ).trans
      (collision_test_marginal (preRate f) ψ hpre).2.symm)

theorem energy_collision_balance {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hi : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    (∫ p, ‖p.2‖^2*gainDensity f p ∂μ.prod volume) =
      ∫ p, ‖p.2‖^2*lossDensity f p ∂μ.prod volume :=
  full_test_collision_invariant f (fun p => ‖p.2‖^2)
    (preRate_energy_integrable hfm hfn hi) (postRate_energy_integrable hfm hfn hi)
    collisionJump_energy

omit [MeasurableSpace X] in
theorem coordinate_abs_le_energy (v : Velocity) (i : Fin 3) : |v i| ≤ 1+‖v‖^2 := by
  have h := PiLp.norm_apply_le v i
  simp only [Real.norm_eq_abs] at h
  nlinarith [sq_nonneg (‖v‖-1)]

theorem momentum_rate_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hp : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (he : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (i : Fin 3) :
    Integrable (fun z => (z.1.2.1 i)*preRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    Integrable (fun z => (z.1.2.1 i)*postRate f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hpre := (preRate_integrable hfm hfn hp).add (preRate_energy_integrable hfm hfn he)
  have hpost := (postRate_integrable hfm hfn hp).add (postRate_energy_integrable hfm hfn he)
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => z.1.2.1 i) := by
    fun_prop
  constructor
  · apply hpre.mono' (hm.mul (preRate_measurable hfm)).aestronglyMeasurable
    filter_upwards [] with z
    simp only [Pi.mul_apply,Pi.add_apply]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (preRate_nonneg hfn z)]
    exact (mul_le_mul_of_nonneg_right (coordinate_abs_le_energy _ i)
      (preRate_nonneg hfn z)).trans_eq (by ring)
  · apply hpost.mono' (hm.mul ((preRate_measurable hfm).comp scatterTriple_measurable)).aestronglyMeasurable
    filter_upwards [] with z
    simp only [Pi.mul_apply,Pi.add_apply]
    change |(z.1.2.1 i)*postRate f z| ≤ postRate f z+‖z.1.2.1‖^2*postRate f z
    have hz : 0 ≤ postRate f z := preRate_nonneg hfn (scatterTriple z)
    rw [abs_mul,abs_of_nonneg hz]
    exact (mul_le_mul_of_nonneg_right (coordinate_abs_le_energy _ i)
      hz).trans_eq (by ring)

theorem momentum_collision_balance {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hp : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (he : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (i : Fin 3) :
    (∫ p : X × Velocity, (p.2 i)*gainDensity f p ∂μ.prod volume) =
      ∫ p : X × Velocity, (p.2 i)*lossDensity f p ∂μ.prod volume :=
  full_test_collision_invariant f (fun p => p.2 i)
    (momentum_rate_integrable hfm hfn hp he i).1
    (momentum_rate_integrable hfm hfn hp he i).2 (collisionJump_momentum i)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Collision mass cancellation against bounded functions of the base variables -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem base_test_collision_zero {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hp : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity))))
    {ψ : X → ℝ} (hψm : Measurable ψ) {C : ℝ} (hψb : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ C) :
    (∫ p, ψ p.1*(gainDensity f p-lossDensity f p) ∂μ.prod volume) = 0 := by
  have hb : ∀ᵐ z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea,
      ‖ψ z.1.1‖ ≤ C :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae hψb)
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere => ψ z.1.1) :=
    hψm.comp measurable_fst.fst
  have hpre := (preRate_integrable hfm hfn hp).bdd_mul hm.aestronglyMeasurable hb
  have hpost := (postRate_integrable hfm hfn hp).bdd_mul hm.aestronglyMeasurable hb
  have hbalance := full_test_collision_invariant f (fun p => ψ p.1) hpre hpost
    (collisionJump_mass ψ)
  have hb' : ∀ᵐ p : X × Velocity ∂μ.prod volume, ‖ψ p.1‖ ≤ C :=
    Measure.quasiMeasurePreserving_fst.ae hψb
  have hi := gainLoss_integrable hfm hfn hp
  have hgi := hi.1.bdd_mul (hψm.comp measurable_fst).aestronglyMeasurable hb'
  have hli := hi.2.bdd_mul (hψm.comp measurable_fst).aestronglyMeasurable hb'
  calc
    _ = ∫ p, ψ p.1*gainDensity f p-ψ p.1*lossDensity f p ∂μ.prod volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => mul_sub _ _ _)
    _ = (∫ p, ψ p.1*gainDensity f p ∂μ.prod volume)-
        ∫ p, ψ p.1*lossDensity f p ∂μ.prod volume := integral_sub hgi hli
    _ = 0 := by rw [hbalance,sub_self]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MomentumCollisionIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integrability of each momentum component of gain and loss -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem gainLoss_coordinate_integrable {μ : Measure X} [SFinite μ] {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hp : Integrable (pairDensity f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (he : Integrable (exponentialPair f) (μ.prod (volume : Measure (Velocity × Velocity))))
    (i : Fin 3) :
    Integrable (fun p => p.2 i*gainDensity f p) (μ.prod volume) ∧
      Integrable (fun p => p.2 i*lossDensity f p) (μ.prod volume) := by
  have h := momentum_rate_integrable hfm hfn hp he i
  exact ⟨(collision_test_marginal (postRate f) (fun p => p.2 i) h.2).1,
    (collision_test_marginal (preRate f) (fun p => p.2 i) h.1).1⟩

end BoltzmannNonuniqueness.CollisionCompactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildConservation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrable local mass tests and cancellation of their collision source -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem MassTest.slice_integrable (φ : MassTest) {T t : ℝ} (ht : t ∈ Icc 0 T)
    {f : Density} (hfi : Integrable f) : Integrable (fun p => f p*φ.toFun t p.1) := by
  have hφ : Measurable (fun p : Phase => φ.toFun t p.1) :=
    φ.measurable_toFun.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C,_hC,hb⟩ := φ.bounded_on_time T
  apply hfi.mul_bdd hφ.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    simpa only [Real.norm_eq_abs] using (hb t ht p).1)

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem mass_source_integrable (S : MildCollisionSolution T f₀ g) (hf₀m : Measurable f₀)
    (φ : MassTest) :
    Integrable (fun z : ℝ × Phase => collision (positiveEvolution T f₀ g z.1) z.2.1 z.2.2*
      φ.toFun z.1 z.2.1) ((volume.restrict (Icc 0 T)).prod volume) := by
  obtain ⟨C,_hC,hb⟩ := φ.bounded_on_time T
  apply (S.positiveEvolution_collision_integrable hf₀m).mul_bdd φ.measurable_toFun.aestronglyMeasurable
  have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht] with z hz
  simpa only [Real.norm_eq_abs] using (hb z.1 hz z.2).1

theorem mass_source_zero (S : MildCollisionSolution T f₀ g) (hf₀m : Measurable f₀)
    (φ : MassTest) :
    (∫ z : ℝ × Phase, collision (positiveEvolution T f₀ g z.1) z.2.1 z.2.2*
      φ.toFun z.1 z.2.1 ∂(volume.restrict (Icc 0 T)).prod volume) = 0 := by
  let F := positiveEvolution T f₀ g
  let ψ : ℝ × Position → ℝ := fun u => φ.toFun u.1 u.2
  have hψm : Measurable ψ := φ.measurable_toFun.comp
    (show Measurable (fun u : ℝ × Position => (u.1,(u.2,(0:Velocity)))) from by fun_prop)
  obtain ⟨C,_hC,hb⟩ := φ.bounded_on_time T
  have hψb : ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T, ‖ψ u‖ ≤ C := by
    have ht : ∀ᵐ u : ℝ × Position ∂AnnularEnvelope.timePositionVolume T, u.1 ∈ Icc 0 T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [ht] with u hu
    simpa only [ψ,Real.norm_eq_abs] using (hb u.1 hu (u.2,0)).1
  have hz := CollisionCompactness.base_test_collision_zero (S.positiveDensity_measurable hf₀m)
    (fun p => positiveEvolution_nonnegative p.1.1 (p.1.2,p.2))
    (S.positiveDensity_pair_integrable hf₀m) hψm hψb
  let W : ℝ × Phase → ℝ := fun z => collision (F z.1) z.2.1 z.2.2*φ.toFun z.1 z.2.1
  have hc := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding W
  change (∫ z, W z ∂(volume.restrict (Icc 0 T)).prod volume) = 0
  rw [← hc]
  calc
    _ = ∫ p, ψ p.1*(CollisionCompactness.gainDensity (kineticDensity F) p-
        CollisionCompactness.lossDensity (kineticDensity F) p)
        ∂(AnnularEnvelope.timePositionVolume T).prod volume := by
      apply integral_congr_ae
      filter_upwards [] with p
      have he := kineticDensity_collision F (p.1.1,(p.1.2,p.2))
      change collision (F p.1.1) p.1.2 p.2*ψ p.1 = _
      rw [← he]
      exact mul_comm _ _
    _ = 0 := hz

theorem mass_integrand_integrable (S : MildCollisionSolution T f₀ g) (hf₀m : Measurable f₀)
    (hEi : Integrable (fun z : ℝ × Phase => entropyMoment (positiveEvolution T f₀ g z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume)) (φ : MassTest) :
    Integrable (massTestIntegrand (positiveEvolution T f₀ g) φ)
      ((volume.restrict (Icc 0 T)).prod volume) :=
  (mass_transport_integrable (S.positiveEvolution_measurable hf₀m) positiveEvolution_nonnegative hEi φ).add
    (S.mass_source_integrable hf₀m φ)

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

section

/-! # The actual local mild solution conserves local mass -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem massTestIntegrand_along_eq (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) (φ : MassTest) :
    TorusFlight.along (massTestIntegrand (positiveEvolution T f₀ g) φ) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
      (fun z => characteristicSource g z*φ.toFun z.1 (TorusFlight.flight z.1 z.2).1+
        entropyPath f₀ (characteristicSource g) z.1 z.2*
          φ.transportDerivative z.1 (TorusFlight.flight z.1 z.2)) := by
  filter_upwards [S.positiveEvolution_along_eq_path_spacetime,
    S.positiveEvolution_along_collision_eq_source hf₀m] with z hf hr
  dsimp only [TorusFlight.along,massTestIntegrand]
  rw [hf,← hr]
  exact add_comm _ _

theorem mass_balance_with_source (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀)
    (hEi : Integrable (fun z : ℝ × Phase => entropyMoment (positiveEvolution T f₀ g z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume)) (φ : MassTest) :
    (∫ z, massTestIntegrand (positiveEvolution T f₀ g) φ z ∂(volume.restrict (Icc 0 T)).prod volume) =
      (∫ p : Phase, positiveEvolution T f₀ g T p*φ.toFun T p.1)-
      (∫ p : Phase, f₀ p*φ.toFun 0 p.1) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let F := positiveEvolution T f₀ g
  let I := massTestIntegrand F φ
  let B : Phase → ℝ := fun p => F T p*φ.toFun T p.1
  let B₀ : Phase → ℝ := fun p => f₀ p*φ.toFun 0 p.1
  have hIi : Integrable I (μ.prod volume) := S.mass_integrand_integrable hf₀m hEi φ
  have hAi := (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hIi
  have hBi : Integrable B := φ.slice_integrable ⟨hT.le,le_rfl⟩ (S.positiveEvolution_integrable hf₀m hf₀i T)
  have hB₀i : Integrable B₀ := φ.slice_integrable ⟨le_rfl,hT.le⟩ hf₀i
  have hp : ∀ᵐ p : Phase,
      (∫ t, TorusFlight.along I (t,p) ∂μ) = B (TorusFlight.flight T p)-B₀ p := by
    have he := Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := (volume : Measure Phase)) (ν := μ)).quasiMeasurePreserving.ae
        (S.massTestIntegrand_along_eq hf₀m φ))
    filter_upwards [S.mass_tested_paths hT φ,he,
      S.positiveEvolution_along_eq_path hT hf₀m hf₀i ⟨hT.le,le_rfl⟩] with p hp he hend
    rw [intervalIntegral.integral_of_le hT.le,← integral_Icc_eq_integral_Ioc] at hp
    calc
      _ = _ := integral_congr_ae he
      _ = _ := hp
      _ = _ := by
        dsimp only [B,B₀,F]
        rw [hend]
  calc
    _ = ∫ z, TorusFlight.along I z ∂μ.prod volume := (TorusFlight.integral_along hIi).symm
    _ = ∫ p : Phase, ∫ t, TorusFlight.along I (t,p) ∂μ := integral_prod_symm _ hAi
    _ = ∫ p : Phase, B (TorusFlight.flight T p)-B₀ p := integral_congr_ae hp
    _ = (∫ p : Phase, B (TorusFlight.flight T p))-(∫ p : Phase, B₀ p) :=
      integral_sub ((TorusFlight.flight_measurePreserving T).integrable_comp_of_integrable hBi) hB₀i
    _ = _ := by rw [TorusFlight.integral_flight]

theorem local_mass_balance (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀)
    (hEi : Integrable (fun z : ℝ × Phase => entropyMoment (positiveEvolution T f₀ g z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume)) (φ : MassTest) :
    (∫ z in boundedTimes T, positiveEvolution T f₀ g z.1 z.2*φ.transportDerivative z.1 z.2) =
      (∫ p : Phase, positiveEvolution T f₀ g T p*φ.toFun T p.1)-
      (∫ p : Phase, f₀ p*φ.toFun 0 p.1) := by
  have h := S.mass_balance_with_source hT hf₀m hf₀i hEi φ
  change (∫ z, positiveEvolution T f₀ g z.1 z.2*φ.transportDerivative z.1 z.2+
    collision (positiveEvolution T f₀ g z.1) z.2.1 z.2.2*φ.toFun z.1 z.2.1
    ∂(volume.restrict (Icc 0 T)).prod volume) = _ at h
  rw [integral_add (mass_transport_integrable (S.positiveEvolution_measurable hf₀m)
      positiveEvolution_nonnegative hEi φ) (S.mass_source_integrable hf₀m φ),
    S.mass_source_zero hf₀m φ,add_zero] at h
  rwa [phaseInterval_measure] at h

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # Every-time energy conservation of the constructed local mild solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem energy_source_zero (S : MildCollisionSolution T f₀ g)
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫ p : Phase, ‖p.2‖^2*source g ((t,p.1),p.2)) = 0 := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hpi := (measurePreserving_prodAssoc μ (volume : Measure Position)
    (volume : Measure (Velocity × Velocity))).symm.integrable_comp_of_integrable hE
  filter_upwards [hpi.prod_right_ae] with t ht
  let f : Position × Velocity → ℝ := fun p => g ((t,p.1),p.2)
  have hm : Measurable f := S.measurable.comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hn : ∀ p, 0 ≤ f p := fun p => S.nonnegative _
  have hp : Integrable (CollisionCompactness.exponentialPair f)
      ((volume : Measure Position).prod (volume : Measure (Velocity × Velocity))) := ht
  have hc := CollisionCompactness.energy_collision_balance hm hn hp
  have hi := CollisionCompactness.gainLoss_energy_integrable hm hn hp
  change (∫ p : Phase, ‖p.2‖^2*(CollisionCompactness.gainDensity f p-
    CollisionCompactness.lossDensity f p)) = 0
  simp_rw [mul_sub]
  rw [Measure.volume_eq_prod,integral_sub hi.1 hi.2,hc,sub_self]

theorem energy_characteristic_integrable (S : MildCollisionSolution T f₀ g)
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) :
    Integrable (fun z : ℝ × Phase => ‖z.2.2‖^2*characteristicSource g z)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  have hi := CollisionCompactness.gainLoss_energy_integrable S.measurable S.nonnegative hE
  have hs : Integrable (fun p => ‖p.2‖^2*source g p)
      ((AnnularEnvelope.timePositionVolume T).prod volume) := by
    convert hi.1.sub hi.2 using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact mul_sub _ _ _
  have hr := (measurePreserving_prodAssoc (volume.restrict (Icc 0 T))
    (volume : Measure Position) (volume : Measure Velocity)).symm.integrable_comp_of_integrable hs
  have hrr : Integrable (fun z : ℝ × Phase => ‖z.2.2‖^2*TorusFlight.regroup (source g) z)
      ((volume.restrict (Icc 0 T)).prod volume) := by
    rw [Measure.volume_eq_prod]
    exact hr
  exact (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable hrr

theorem energy_characteristic_zero (S : MildCollisionSolution T f₀ g)
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫ p : Phase, ‖p.2‖^2*characteristicSource g (t,p)) = 0 := by
  filter_upwards [S.energy_source_zero hE] with t ht
  exact (TorusFlight.integral_flight
    (fun p : Phase => ‖p.2‖^2*source g ((t,p.1),p.2)) t).trans ht

theorem energy_conservation (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀)
    (hf₀E : Integrable (fun p : Phase => ‖p.2‖^2*f₀ p))
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    energy (positiveEvolution T f₀ g t) = energy f₀ := by
  have hm : Measurable (fun z : ℝ × Phase => ‖z.2.2‖^2*characteristicSource g z) :=
    (measurable_snd.snd.norm.pow_const 2).mul S.characteristicSource_measurable
  have h := TorusFlight.velocity_weighted_profile_balance f₀ (characteristicSource g)
    (fun v => ‖v‖^2) hm (S.energy_characteristic_integrable hE) hf₀E t
  have hz : (∫ s, if s ≤ t then ∫ p : Phase, ‖p.2‖^2*characteristicSource g (s,p) else 0
      ∂volume.restrict (Icc 0 T)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [S.energy_characteristic_zero hE] with s hs
    split_ifs <;> simp_all
  rw [hz,add_zero] at h
  change (∫ p : Phase, ‖p.2‖^2*positiveEvolution T f₀ g t p) = _
  calc
    _ = ∫ p : Phase, ‖p.2‖^2*evolution T f₀ g t p := by
      apply integral_congr_ae
      filter_upwards [S.evolution_eq_positive_each_time hT hf₀m hf₀i t ht] with p hp
      rw [hp]
    _ = _ := h

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # Every-time momentum conservation for the actual local mild solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem coordinate_source_zero (S : MildCollisionSolution T f₀ g)
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) (i : Fin 3) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫ p : Phase, p.2 i*source g ((t,p.1),p.2)) = 0 := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hp := (measurePreserving_prodAssoc μ (volume : Measure Position)
    (volume : Measure (Velocity × Velocity))).symm.integrable_comp_of_integrable S.pair_integrable
  have he := (measurePreserving_prodAssoc μ (volume : Measure Position)
    (volume : Measure (Velocity × Velocity))).symm.integrable_comp_of_integrable hE
  filter_upwards [hp.prod_right_ae,he.prod_right_ae] with t hpt het
  let f : Position × Velocity → ℝ := fun p => g ((t,p.1),p.2)
  have hm : Measurable f := S.measurable.comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hn : ∀ p, 0 ≤ f p := fun p => S.nonnegative _
  have hpair : Integrable (CollisionCompactness.pairDensity f)
      ((volume : Measure Position).prod (volume : Measure (Velocity × Velocity))) := hpt
  have henergy : Integrable (CollisionCompactness.exponentialPair f)
      ((volume : Measure Position).prod (volume : Measure (Velocity × Velocity))) := het
  have hc := CollisionCompactness.momentum_collision_balance hm hn hpair henergy i
  have hi := CollisionCompactness.gainLoss_coordinate_integrable hm hn hpair henergy i
  change (∫ p : Phase, p.2 i*(CollisionCompactness.gainDensity f p-CollisionCompactness.lossDensity f p)) = 0
  simp_rw [mul_sub]
  rw [Measure.volume_eq_prod,integral_sub hi.1 hi.2,hc,sub_self]

theorem coordinate_characteristic_integrable (S : MildCollisionSolution T f₀ g)
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) (i : Fin 3) :
    Integrable (fun z : ℝ × Phase => z.2.2 i*characteristicSource g z)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  have hi := CollisionCompactness.gainLoss_coordinate_integrable S.measurable S.nonnegative S.pair_integrable hE i
  have hs : Integrable (fun p => p.2 i*source g p) ((AnnularEnvelope.timePositionVolume T).prod volume) := by
    convert hi.1.sub hi.2 using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    exact mul_sub _ _ _
  have hr := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable hs
  exact (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable hr

theorem coordinate_conservation (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) {i : Fin 3}
    (hf₀c : Integrable (fun p : Phase => p.2 i*f₀ p))
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p : Phase, p.2 i*positiveEvolution T f₀ g t p) = ∫ p : Phase, p.2 i*f₀ p := by
  have hm : Measurable (fun z : ℝ × Phase => z.2.2 i*characteristicSource g z) := by
    exact (by fun_prop : Measurable (fun z : ℝ × Phase => z.2.2 i)).mul S.characteristicSource_measurable
  have h := TorusFlight.velocity_weighted_profile_balance f₀ (characteristicSource g)
    (fun v => v i) hm (S.coordinate_characteristic_integrable hE i) hf₀c t
  have hz : (∫ s, if s ≤ t then ∫ p : Phase, p.2 i*characteristicSource g (s,p) else 0
      ∂volume.restrict (Icc 0 T)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [S.coordinate_source_zero hE i] with s hs
    have hchar : (∫ p : Phase, p.2 i*characteristicSource g (s,p)) = 0 :=
      (TorusFlight.integral_flight (fun p : Phase => p.2 i*source g ((s,p.1),p.2)) s).trans hs
    split_ifs <;> simp_all
  rw [hz,add_zero] at h
  calc
    _ = ∫ p : Phase, p.2 i*evolution T f₀ g t p := by
      apply integral_congr_ae
      filter_upwards [S.evolution_eq_positive_each_time hT hf₀m hf₀i t ht] with p hp
      rw [hp]
    _ = _ := h

theorem momentum_conservation (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀ : FiniteEntropyDatum f₀)
    (hfinite : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (positiveEvolution T f₀ g t))
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume))
    {t : ℝ} (ht : t ∈ Icc 0 T) : momentum (positiveEvolution T f₀ g t) = momentum f₀ := by
  apply PiLp.ext
  intro i
  let L := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i
  have h₀ := L.integrable_comp hf₀.integrable_momentum
  have h₁ := L.integral_comp_comm hf₀.integrable_momentum
  have h₂ := L.integral_comp_comm (hfinite t ht).integrable_momentum
  have hc : Integrable (fun p : Phase => p.2 i*f₀ p) := by
    simpa only [L,PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul,mul_comm] using h₀
  have h := S.coordinate_conservation hT hf₀m hf₀.integrable hc hE ht
  change (momentum (positiveEvolution T f₀ g t)) i = (momentum f₀) i
  simp only [L,PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul] at h₁ h₂
  calc
    _ = ∫ p : Phase, positiveEvolution T f₀ g t p*p.2 i := h₂.symm
    _ = ∫ p : Phase, p.2 i*positiveEvolution T f₀ g t p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => mul_comm _ _)
    _ = ∫ p : Phase, p.2 i*f₀ p := h
    _ = ∫ p : Phase, f₀ p*p.2 i := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => mul_comm _ _)
    _ = _ := h₁

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyLocalConstruction
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A strong local solution with the full entropy and moment bounds -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem uniform_entropyMoment_of_entropy_inequality {T : ℝ} {f₀ : Density} {F : Evolution}
    (hf₀ : FiniteEntropyDatum f₀) (hf : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (F t))
    (hH : ∀ t ∈ Icc 0 T, ENNReal.ofReal (relativeEntropy (F t))+
      (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (F s)) ≤ ENNReal.ofReal (relativeEntropy f₀)) :
    ∃ C : ℝ, ∀ t ∈ Icc 0 T, (∫ z, entropyMoment (F t) z) ≤ C := by
  refine ⟨(1+4*entropyMomentCoefficient)*relativeEntropy f₀+
    4*entropyMomentCoefficient*(∫ z : Phase, entropyGaussian z.2)+
      (∫ z : Phase, maxwellian z.2),?_⟩
  intro t ht
  have hle : ENNReal.ofReal (relativeEntropy (F t)) ≤ ENNReal.ofReal (relativeEntropy f₀) :=
    (le_add_of_nonneg_right zero_le).trans (hH t ht)
  have hreal : relativeEntropy (F t) ≤ relativeEntropy f₀ := by
    have h := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal (relativeEntropy f₀) ≠ ⊤) hle
    simpa only [ENNReal.toReal_ofReal (relativeEntropy_nonneg (hf t ht)),
      ENNReal.toReal_ofReal (relativeEntropy_nonneg hf₀)] using h
  refine (entropyMoment_integral_control (hf t ht)).trans ?_
  have ha : 0 ≤ 1+4*entropyMomentCoefficient := by
    nlinarith [entropyMomentCoefficient_nonneg]
  linarith [mul_le_mul_of_nonneg_left hreal ha]

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MildLocalAdmissibility
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All local admissibility properties for the same actual mild solution -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.MildCollisionSolution

theorem localAdmissible_q80_oai {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}
    (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀n : ∀ p, 0 ≤ f₀ p) (hf₀ : FiniteEntropyDatum f₀)
    (hfinite : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (positiveEvolution T f₀ g t))
    (hH : ∀ t ∈ Icc 0 T,
      ENNReal.ofReal (relativeEntropy (positiveEvolution T f₀ g t))+
      (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (positiveEvolution T f₀ g s)) ≤
        ENNReal.ofReal (relativeEntropy f₀))
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) :
    AdmissibleLocal T f₀ (positiveEvolution T f₀ g) := by
  have hM := uniform_entropyMoment_of_entropy_inequality hf₀ hfinite hH
  have hEi := entropyMoment_spacetime_integrable (S.positiveEvolution_measurable hf₀m)
    positiveEvolution_nonnegative hfinite hM
  refine ⟨S.localMildSolution hT hf₀m hf₀.integrable hf₀n,hf₀,hfinite,hM,
    S.positiveEvolution_collision_fibers hf₀m,S.renormalized_integrable hf₀m,?_,?_,?_,?_,?_,hH⟩
  · intro β φ
    rw [S.renormalized_balance hT hf₀m hf₀.integrable hf₀n β φ]
    ring
  · intro φ
    change Integrable _ _
    rw [← phaseInterval_measure]
    exact mass_transport_integrable (S.positiveEvolution_measurable hf₀m) positiveEvolution_nonnegative hEi φ
  · intro φ
    rw [S.local_mass_balance hT hf₀m hf₀.integrable hEi φ]
    ring
  · exact fun _ ht => S.momentum_conservation hT hf₀m hf₀ hfinite hE ht
  · exact fun _ ht => S.energy_conservation hT hf₀m hf₀.integrable hf₀.integrable_energy hE ht

end BoltzmannNonuniqueness.MildCollisionSolution

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.MildCollisionSolution.localAdmissible_q80_oai := @OAI.BoltzmannNonuniqueness.MildCollisionSolution.localAdmissible_q80_oai
