-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_profile_eq_density_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:14:19.491626+00:00
-- url     : https://prove2.me/submissions/e48ac60f-ab5c-4a5b-a6cc-e8c8d0f1559e

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_GlobalCollisionLimit_characteristic_error_L1_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_GlobalCollisionLimit_gain_path_integrable_full_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_GlobalCollisionLimit_linear_comparison_error_L1_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_GlobalCollisionLimit_linear_profile_le_full_q80

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Admissibility
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.sphereArea_isFiniteMeasure _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

theorem maxwellian_pos (v : Velocity) : 0 < maxwellian v := by
  unfold maxwellian
  positivity

end BoltzmannNonuniqueness

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

/-- The loss-frequency angular normalization in the manuscript. -/
theorem integral_collisionKernel_sphereArea (v w : Velocity) :
    (∫ ω : Sphere, collisionKernel v w ω ∂sphereArea) = 2 * Real.pi * ‖v - w‖ :=
  integral_abs_inner_sphereArea (v - w)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LossIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.AnnularEnvelope.instIsFiniteMeasureProdRealPositionTimePositionVolume _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.sphereProbability_isProbability _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Loss frequency and its first-moment bound

The angular normalization gives the loss-frequency formula from Section 2,
equation `eq:frequency`. Fubini is used only with an explicit integrability
hypothesis for the original collision integrand. Separate first-moment
conditions ensure that the frequency integral itself is finite.
-/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

theorem frequency_integrand_norm_le (f : Density) (x : Position) (v w : Velocity) :
    ‖‖v - w‖ * f (x, w)‖ ≤
      ‖v‖ * |f (x, w)| + ‖w‖ * |f (x, w)| := by
  rw [Real.norm_eq_abs, abs_mul, abs_norm]
  calc
    ‖v - w‖ * |f (x, w)| ≤ (‖v‖ + ‖w‖) * |f (x, w)| :=
      mul_le_mul_of_nonneg_right (norm_sub_le v w) (abs_nonneg _)
    _ = _ := by ring

theorem integrable_abs_firstMoment (f : Density) (x : Position)
    (hm : Integrable (fun w : Velocity => ‖w‖ * f (x, w))) :
    Integrable (fun w : Velocity => ‖w‖ * |f (x, w)|) := by
  simpa only [Real.norm_eq_abs, abs_mul, abs_norm] using hm.norm

/-- Finite mass and first absolute velocity moment make the frequency integrable. -/
theorem integrable_frequency_integrand (f : Density) (x : Position) (v : Velocity)
    (hf : Integrable (fun w : Velocity => f (x, w)))
    (hm : Integrable (fun w : Velocity => ‖w‖ * f (x, w))) :
    Integrable (fun w : Velocity => ‖v - w‖ * f (x, w)) := by
  have hfa : Integrable (fun w : Velocity => |f (x, w)|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hb := (hfa.const_mul ‖v‖).add (integrable_abs_firstMoment f x hm)
  apply hb.mono' ((by fun_prop : AEStronglyMeasurable (fun w : Velocity => ‖v - w‖)).mul
    hf.aestronglyMeasurable)
  filter_upwards [] with w
  exact frequency_integrand_norm_le f x v w

end BoltzmannNonuniqueness

end

end

section

/-! # Integrability of the original hard-sphere loss integral -/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem integrable_loss_of_moments (f : Density) (x : Position) (v : Velocity)
    (hf : Integrable (fun w : Velocity => f (x, w)))
    (hm : Integrable (fun w : Velocity => ‖w‖ * f (x, w))) :
    Integrable (fun p : Velocity × Sphere =>
      collisionKernel v p.1 p.2 * f (x, v) * f (x, p.1))
      ((volume : Measure Velocity).prod sphereArea) := by
  have hi := ((integrable_frequency_integrand f x v hf hm).norm.const_mul |f (x, v)|).comp_fst sphereArea
  have hk : AEStronglyMeasurable (fun p : Velocity × Sphere => collisionKernel v p.1 p.2)
      ((volume : Measure Velocity).prod sphereArea) := by unfold collisionKernel normalComponent; fun_prop
  apply hi.mono' ((hk.mul aestronglyMeasurable_const).mul hf.aestronglyMeasurable.comp_fst)
  filter_upwards [] with p
  dsimp only [Pi.mul_apply]
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (collisionKernel_nonneg v p.1 p.2), abs_norm]
  calc
    collisionKernel v p.1 p.2 * |f (x, v)| * |f (x, p.1)| ≤
        ‖v - p.1‖ * |f (x, v)| * |f (x, p.1)| := by
      gcongr
      exact collisionKernel_le_norm v p.1 p.2
    _ = _ := by ring

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.UnifIntegrableCompat
attribute [-instance] _root_.OAI.closedSubmoduleNormedAddCommGroup _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv _root_.OAI.isProbabilityMeasure_map_snd _root_.OAI.isProbabilityMeasure_map_subtype_val _root_.OAI.vonNeumannToStarSubalgebraIsClosed
/-!
# Uniform integrability compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. The two disagree on uniform integrability:

* `d13f23b`'s `UnifIntegrable f p μ` is `Tendsto (fun ε ↦ ⨆ i s (_ : μ s ≤ ε), eLpNorm (f i) p
  (μ.restrict s)) (𝓝 0) (𝓝 0)` (extended-real `ε`, `δ`, any set `s`); `0df444a`'s is the real
  `ε`-`δ` form over measurable sets with `eLpNorm (s.indicator (f i)) p μ`.
* `d13f23b`'s `UniformIntegrable f p μ` has two components, `UnifIntegrable f p μ` and a uniform
  bound; `0df444a`'s has three, measurability first. In `d13f23b` the bound alone gives
  measurability, since there `eLpNorm` is `∞` on a function that is not a.e. strongly measurable.
* `d13f23b`'s `UnifTight` takes `ε : ℝ≥0∞`; `0df444a`'s takes `ε : ℝ≥0`.

So that ported proofs keep `d13f23b`'s shapes (`obtain ⟨hu, C, hC⟩ := hf`, `intro ε hε` with
`ε : ℝ≥0∞`, `hu.ae_mono`, `hu.comp`), this file declares `OAI.UnifIntegrable`,
`OAI.UniformIntegrable` and `OAI.UnifTight`, which shadow Mathlib's inside `namespace OAI`, with
`d13f23b`'s API under `d13f23b`'s names, proved from `0df444a`'s. `OAI.UnifIntegrable` carries the
measurability of every member (Mathlib's `UnifIntegrable` together with it), so that
`OAI.UniformIntegrable` keeps `d13f23b`'s two components and is equivalent to Mathlib's
`UniformIntegrable` (`OAI.uniformIntegrable_iff_mathlib`).

`d13f23b`'s `unifIntegrable_iff` and `unifIntegrable_iff'` cannot be stated as equivalences here
(the right sides do not give measurability): the port rewrites their `mp` direction to
`OAI.UnifIntegrable.enn_spec` / `enn_spec'` and their `mpr` direction to
`OAI.UnifIntegrable.of_enn` / `of_enn'`, which take the measurability as a second argument.
-/

noncomputable section UnifIntegrableCompat

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace OAI

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]
  {p : ℝ≥0∞} {f g : ι → α → β}

theorem uniformIntegrable_iff_mathlib :
    UniformIntegrable f p μ ↔ MeasureTheory.UniformIntegrable f p μ :=
  ⟨fun ⟨⟨u, hm⟩, b⟩ => ⟨hm, u, b⟩, fun ⟨hm, u, b⟩ => ⟨⟨u, hm⟩, b⟩⟩

/-! ### `UnifIntegrable` -/

namespace UnifIntegrable

/-- The `mp` direction of `d13f23b`'s `unifIntegrable_iff`. -/
theorem enn_spec (hf : UnifIntegrable f p μ) :
    ∀ ε > 0, ∃ δ > 0, ∀ i s, μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε := by
  intro ε hε
  rcases eq_top_or_lt_top ε with rfl | hεt
  · exact ⟨1, one_pos, fun _ _ _ => le_top⟩
  obtain ⟨δ, hδ, h⟩ := hf.1 (ENNReal.toReal_pos hε.ne' hεt.ne)
  refine ⟨ENNReal.ofReal δ, ENNReal.ofReal_pos.2 hδ, fun i s hs => ?_⟩
  have ht := measurableSet_toMeasurable μ s
  calc eLpNorm (f i) p (μ.restrict s)
      ≤ eLpNorm (f i) p (μ.restrict (toMeasurable μ s)) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono (subset_toMeasurable μ s) le_rfl)
    _ = eLpNorm ((toMeasurable μ s).indicator (f i)) p μ :=
        (eLpNorm_indicator_eq_eLpNorm_restrict ht).symm
    _ ≤ ENNReal.ofReal ε.toReal := h i _ ht (by rwa [measure_toMeasurable])
    _ = ε := ENNReal.ofReal_toReal hεt.ne

/-- The `mp` direction of `d13f23b`'s `unifIntegrable_iff'`. -/
theorem enn_spec' (hf : UnifIntegrable f p μ) :
    ∀ ε > 0, ∃ δ > 0, ∀ i s, MeasurableSet s → μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε :=
  fun ε hε => (hf.enn_spec ε hε).imp fun _ ⟨hδ, h⟩ => ⟨hδ, fun i s _ => h i s⟩

/-- The `mpr` direction of `d13f23b`'s `unifIntegrable_iff'`, with the measurability. -/
theorem of_enn' (h : ∀ ε > 0, ∃ δ > 0, ∀ i s, MeasurableSet s → μ s ≤ δ →
      eLpNorm (f i) p (μ.restrict s) ≤ ε) (hm : ∀ i, AEStronglyMeasurable (f i) μ) :
    UnifIntegrable f p μ := by
  refine ⟨fun ε hε => ?_, hm⟩
  obtain ⟨δ, hδ, hb⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  have hne : min δ 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  refine ⟨(min δ 1).toReal, ENNReal.toReal_pos (lt_min hδ one_pos).ne' hne, fun i s hsm hs => ?_⟩
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hsm]
  refine hb i s hsm (hs.trans ?_)
  rw [ENNReal.ofReal_toReal hne]
  exact min_le_left _ _

/-- The `mpr` direction of `d13f23b`'s `unifIntegrable_iff`, with the measurability. -/
theorem of_enn (h : ∀ ε > 0, ∃ δ > 0, ∀ i s, μ s ≤ δ → eLpNorm (f i) p (μ.restrict s) ≤ ε)
    (hm : ∀ i, AEStronglyMeasurable (f i) μ) : UnifIntegrable f p μ :=
  of_enn' (fun ε hε => (h ε hε).imp fun _ ⟨hδ, hb⟩ => ⟨hδ, fun i s _ => hb i s⟩) hm

/-- Uniform integrability is preserved by restriction of the measure to a set. -/
protected theorem restrict (hf : UnifIntegrable f p μ) (s : Set α) :
    UnifIntegrable f p (μ.restrict s) :=
  ⟨hf.1.restrict s, fun i => (hf.2 i).restrict⟩

protected theorem comp {ι' : Type*} (g : ι' → ι) (hf : UnifIntegrable f p μ) :
    UnifIntegrable (f ∘ g) p μ :=
  ⟨fun _ hε => (hf.1 hε).imp fun _ ⟨hδ, h⟩ => ⟨hδ, fun i s => h (g i) s⟩, fun i => hf.2 (g i)⟩

end UnifIntegrable

/-! ### `UniformIntegrable` -/

namespace UniformIntegrable

protected theorem memLp (hf : UniformIntegrable f p μ) (i : ι) : MemLp (f i) p μ :=
  (uniformIntegrable_iff_mathlib.1 hf).memLp i

theorem toMathlib (hf : UniformIntegrable f p μ) : MeasureTheory.UniformIntegrable f p μ :=
  uniformIntegrable_iff_mathlib.1 hf

theorem spec (hp : p ≠ 0) (hp' : p ≠ ∞) (hfu : UniformIntegrable f p μ) {ε : ℝ≥0∞}
    (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ i, eLpNorm ({ x | C ≤ ‖f i x‖₊ }.indicator (f i)) p μ ≤ ε := by
  rcases eq_top_or_lt_top ε with rfl | hεt
  · exact ⟨0, fun _ => le_top⟩
  obtain ⟨C, hC⟩ := hfu.toMathlib.spec hp hp' (ENNReal.toReal_pos hε.ne' hεt.ne)
  exact ⟨C, fun i => (hC i).trans (ENNReal.ofReal_toReal hεt.ne).le⟩

end UniformIntegrable

theorem uniformIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UniformIntegrable (fun _ : ι => g) p μ :=
  uniformIntegrable_iff_mathlib.2 (MeasureTheory.uniformIntegrable_const hp hp_ne_top hg)


/-! ### `UnifTight` -/

end OAI

end UnifIntegrableCompat
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityWeight
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.coordinateKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.coreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

section

/-! # Removing a countable family of velocity windows from a null-set statement -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem ae_prod_of_velocity_windows {P : X × Velocity → Prop}
    (h : ∀ n : ℕ, ∀ᵐ z ∂μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 (n:ℝ))), P z) :
    ∀ᵐ z ∂μ.prod (volume : Measure Velocity), P z := by
  have he : (⋃ n : ℕ, (univ : Set X) ×ˢ Metric.closedBall (0:Velocity) (n:ℝ)) = univ := by
    rw [← prod_iUnion,Metric.iUnion_closedBall_nat,univ_prod_univ]
  have hh := (ae_restrict_iUnion_iff (μ := μ.prod (volume : Measure Velocity))
    (fun n : ℕ => (univ : Set X) ×ˢ Metric.closedBall (0:Velocity) (n:ℝ)) P).mpr (fun n => by
      rw [← Measure.prod_restrict,Measure.restrict_univ]
      exact h n)
  simpa only [he,Measure.restrict_univ] using hh

end BoltzmannNonuniqueness

end

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

theorem scalarRelativeEntropy_continuous (m : ℝ) : Continuous (scalarRelativeEntropy m) :=
  (Real.continuous_mul_log.sub (continuous_id.mul_const (1+Real.log m))).add_const m

theorem scalarRelativeEntropy_hasDerivAt {m f : ℝ} (hm : 0 < m) (hf : 0 < f) :
    HasDerivAt (scalarRelativeEntropy m) (Real.log (f/m)) f := by
  have h := ((Real.hasDerivAt_mul_log hf.ne').sub
    ((hasDerivAt_id f).mul_const (1+Real.log m))).add_const m
  rw [Real.log_div hf.ne' hm.ne']
  refine h.congr_deriv (Eq.symm ?_)
  · ring

theorem regularizedEntropy_continuous_delta (m e f : ℝ) :
    Continuous (fun δ => regularizedEntropy m e δ f) :=
  (((scalarRelativeEntropy_continuous m).comp
    (continuous_const.add (continuous_id.mul_const e))).sub
    ((scalarRelativeEntropy_continuous m).comp (continuous_id.mul_const e))).add_const m

theorem regularizedEntropy_tendsto (m e f : ℝ) :
    Tendsto (fun δ => regularizedEntropy m e δ f) (𝓝 0) (𝓝 (scalarRelativeEntropy m f)) := by
  have h := (regularizedEntropy_continuous_delta m e f).tendsto 0
  have he : regularizedEntropy m e 0 f = scalarRelativeEntropy m f := by
    simp [regularizedEntropy,scalarRelativeEntropy]
  rw [he] at h
  exact h

theorem regularizedEntropy_hasDerivAt {m e δ f : ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (hf : 0 ≤ f) :
    HasDerivAt (regularizedEntropy m e δ) (Real.log ((f+δ*e)/m)) f := by
  have hp : 0 < f+δ*e := add_pos_of_nonneg_of_pos hf (mul_pos hδ he)
  have h := (((scalarRelativeEntropy_hasDerivAt hm hp).comp f
    ((hasDerivAt_id f).add_const (δ*e))).sub_const (scalarRelativeEntropy m (δ*e))).add_const m
  refine h.congr_deriv (Eq.symm ?_)
  · ring

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

section

/-! # The regularized entropy chain rule on an absolutely continuous free path -/

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace BoltzmannNonuniqueness

theorem regularizedEntropy_lipschitz {m e δ R : ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (_hR : 0 ≤ R) :
    ∃ C : ℝ≥0, LipschitzOnWith C (regularizedEntropy m e δ) (Icc 0 R) := by
  let L := Real.log (δ*e/m)
  let U := Real.log ((R+δ*e)/m)
  let C : ℝ≥0 := ⟨|L|+|U|,add_nonneg (abs_nonneg _) (abs_nonneg _)⟩
  refine ⟨C,(convex_Icc (0:ℝ) R).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x hx => (regularizedEntropy_hasDerivAt hm he hδ hx.1).hasDerivWithinAt) ?_⟩
  intro x hx
  have hl : L ≤ Real.log ((x+δ*e)/m) := Real.log_le_log (div_pos (mul_pos hδ he) hm)
    (div_le_div_of_nonneg_right (by linarith [hx.1]) hm.le)
  have hu : Real.log ((x+δ*e)/m) ≤ U := Real.log_le_log
    (div_pos (add_pos_of_nonneg_of_pos hx.1 (mul_pos hδ he)) hm)
    (div_le_div_of_nonneg_right (by linarith [hx.2]) hm.le)
  have hb : |Real.log ((x+δ*e)/m)| ≤ |L|+|U| := abs_le.mpr ⟨by
    linarith [neg_abs_le L,abs_nonneg U],by linarith [le_abs_self U,abs_nonneg L]⟩
  exact_mod_cast hb

theorem lipschitzOnWith_comp_absolutelyContinuousOnInterval {g f : ℝ → ℝ} {s : Set ℝ} {K : ℝ≥0}
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

theorem regularizedEntropy_chain_rule {a b m e δ R : ℝ} {F r : ℝ → ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hFn : ∀ t ∈ uIcc a b, 0 ≤ F t) (hFb : ∀ t ∈ uIcc a b, F t ≤ R)
    (hr : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt F (r t) t) :
    (∫ t in a..b, Real.log ((F t+δ*e)/m)*r t) =
      regularizedEntropy m e δ (F b)-regularizedEntropy m e δ (F a) := by
  obtain ⟨C,hC⟩ := regularizedEntropy_lipschitz hm he hδ hR
  have hc : AbsolutelyContinuousOnInterval (fun t => regularizedEntropy m e δ (F t)) a b :=
    lipschitzOnWith_comp_absolutelyContinuousOnInterval hC (fun t ht => ⟨hFn t ht,hFb t ht⟩) hF
  rw [← hc.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hr] with t ht hmem
  have hmemb : t ∈ uIcc a b := uIoc_subset_uIcc hmem
  exact ((regularizedEntropy_hasDerivAt hm he hδ (hFn t hmemb)).comp t (ht hmemb)).deriv.symm

end BoltzmannNonuniqueness

end

end

section

/-! # The entropy balance for an integral characteristic path -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem regularizedEntropy_integral_path {a b m e δ R A : ℝ} {r : ℝ → ℝ}
    (hm : 0 < m) (he : 0 < e) (hδ : 0 < δ) (hR : 0 ≤ R)
    (hr : IntervalIntegrable r volume a b)
    (hn : ∀ t ∈ uIcc a b, 0 ≤ A+∫ s in a..t, r s)
    (hb : ∀ t ∈ uIcc a b, A+(∫ s in a..t, r s) ≤ R) :
    (∫ t in a..b, Real.log (((A+∫ s in a..t, r s)+δ*e)/m)*r t) =
      regularizedEntropy m e δ (A+∫ s in a..b, r s)-regularizedEntropy m e δ A := by
  have hprimitive := hr.absolutelyContinuousOnInterval_intervalIntegral
    (left_mem_uIcc : a ∈ uIcc a b)
  have hconstant : AbsolutelyContinuousOnInterval (fun _ : ℝ => A) a b := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  have hp : AbsolutelyContinuousOnInterval (fun t => A+∫ s in a..t, r s) a b :=
    hconstant.add hprimitive
  have hd : ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (fun t => A+∫ s in a..t, r s) (r t) t := by
    filter_upwards [hr.ae_hasDerivAt_integral] with t ht hmem
    exact (ht hmem a left_mem_uIcc).const_add A
  simpa only [intervalIntegral.integral_same,add_zero] using
    regularizedEntropy_chain_rule hm he hδ hR hp hn hb hd

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

theorem entropyDual_log_ratio {m u : ℝ} (hm : 0 < m) (hu : 0 < u) :
    entropyDual m u (Real.log (u/m)) = scalarRelativeEntropy m u := by
  rw [scalarRelativeEntropy_eq hm]
  unfold entropyDual
  rw [Real.exp_log (div_pos hu hm)]
  field_simp
  ring

theorem entropyDual_zero_tendsto (m : ℝ) :
    Tendsto (fun r : ℝ => entropyDual m 0 (-r)) atTop (𝓝 m) := by
  have h : Tendsto (fun r : ℝ => Real.exp (-r)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have ht : Tendsto (fun r : ℝ => m-m*Real.exp (-r)) atTop (𝓝 m) := by
    simpa only [mul_zero,sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => m) atTop (𝓝 m)).sub (h.const_mul m)
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext r
  dsimp [entropyDual]
  ring

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_MarginalUniformIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-fibre integration preserves uniform integrability -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem uniformIntegrable_restrict {μ : Measure X} {f : ℕ → X → ℝ}
    (hf : UniformIntegrable f 1 μ) (s : Set X) :
    UniformIntegrable f 1 (μ.restrict s) := by
  obtain ⟨C,hC⟩ := hf.2
  exact ⟨hf.1.restrict s,C,fun n =>
    (eLpNorm_mono_measure (f n) Measure.restrict_le_self).trans (hC n)⟩

theorem uniformIntegrable_comp {μ : Measure X} {f : ℕ → X → ℝ}
    (hf : UniformIntegrable f 1 μ) (a : ℕ → ℕ) :
    UniformIntegrable (fun n => f (a n)) 1 μ := by
  obtain ⟨C,hC⟩ := hf.2
  exact ⟨hf.1.comp a,C,fun n => hC (a n)⟩

theorem eLpNorm_integral_le {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : X × Y → ℝ} (hf : Measurable f) :
    eLpNorm (fun x => ∫ y, f (x,y) ∂ν) 1 μ ≤ eLpNorm f 1 (μ.prod ν) := by
  rw [eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_one_eq_lintegral_enorm,lintegral_prod _ hf.enorm.aemeasurable]
  exact lintegral_mono (fun x => enorm_integral_le_lintegral_enorm _)

end BoltzmannNonuniqueness.Compactness

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

section

/-! # Bounded changes of measure for weak L1 limits -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.Published
variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.withDensity_bounded {μ : Measure X}
    {f : ℕ → X → ℝ} {g w : X → ℝ} (h : WeakL1Converges μ f g)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hwB : ∃ B : ℝ, ∀ x, |w x| ≤ B) :
    WeakL1Converges (μ.withDensity (fun x => ENNReal.ofReal (w x))) f g := by
  obtain ⟨B,hB⟩ := hwB
  have hi : Integrable (fun x => w x*g x) μ :=
    h.2.1.bdd_mul hw.aestronglyMeasurable (ae_of_all _ hB)
  refine ⟨h.1,?_,?_⟩
  · apply (integrable_withDensity_iff_integrable_smul' hw.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
    simpa only [ENNReal.toReal_ofReal (hw0 _),smul_eq_mul] using hi
  · intro ψ hψ hψB
    obtain ⟨C,hC⟩ := hψB
    have hb : ∃ D : ℝ, ∀ x, |w x*ψ x| ≤ D := by
      refine ⟨max B 0 * max C 0,fun x => ?_⟩
      rw [abs_mul]
      exact mul_le_mul ((hB x).trans (le_max_left _ _))
        ((hC x).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    have ht := h.2.2 (fun x => w x*ψ x) (hw.mul hψ) hb
    have he (u : X → ℝ) :
        (∫ x, ψ x*u x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) =
          ∫ x, (w x*ψ x)*u x ∂μ := by
      rw [integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (hw0 _),smul_eq_mul,mul_assoc]
    simpa only [he] using ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Transfer of weak L¹ convergence through a measure-preserving chart -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem integral_comp_measurePreserving {μ : Measure X} {ν : Measure Y}
    {φ : X → Y} (hφ : MeasurePreserving φ μ ν) {f : Y → ℝ} (hf : Measurable f) :
    (∫ x, f (φ x) ∂μ) = ∫ y, f y ∂ν := by
  have h := integral_map (μ := μ) hφ.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hφ.map_eq] at h
  exact h.symm

theorem WeakL1Converges.of_comp_measurePreserving {μ : Measure X} {ν : Measure Y}
    {φ : X → Y} (hφ : MeasurePreserving φ μ ν) {f : ℕ → Y → ℝ} {g : Y → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (h : WeakL1Converges μ (fun n => f n ∘ φ) (g ∘ φ)) :
    WeakL1Converges ν f g := by
  refine ⟨hg,(hφ.integrable_comp hg.aestronglyMeasurable).mp h.2.1,?_⟩
  intro ψ hψ hB
  have ht := h.2.2 (ψ ∘ φ) (hψ.comp hφ.measurable)
    (by obtain ⟨C,hC⟩ := hB; exact ⟨C,fun x => hC (φ x)⟩)
  have he (u : Y → ℝ) (hu : Measurable u) :
      (∫ x, (ψ ∘ φ) x*(u ∘ φ) x ∂μ) = ∫ y, ψ y*u y ∂ν :=
    integral_comp_measurePreserving hφ (hψ.mul hu)
  simp_rw [he _ (hf _)] at ht
  rw [he _ hg] at ht
  exact ht

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform L¹ approximation preserves uniform integrability

This is the analytic bridge from the fixed outer-annulus majorants and the
vanishing small-annulus collision integrals to full uniform integrability.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_of_approximation {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ℕ → X → ℝ} {g : ℕ → ℕ → X → ℝ}
    (hg : ∀ j, UniformIntegrable (g j) 1 μ)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ j : ℕ, ∀ n,
      eLpNorm (fun x => f n x-g j n x) 1 μ ≤ ε)
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) :
    UniformIntegrable f 1 μ := by
  have htri (j n : ℕ) (ν : Measure X) (hν : ν ≤ μ) : eLpNorm (f n) 1 ν ≤
      eLpNorm (fun x => f n x-g j n x) 1 ν+eLpNorm (g j n) 1 ν := by
    have he : f n = (fun x => f n x-g j n x)+(g j n) := by funext x; simp
    calc
      _ = eLpNorm ((fun x => f n x-g j n x)+(g j n)) 1 ν :=
        congrArg (fun h : X → ℝ => eLpNorm h 1 ν) he
      _ ≤ _ := eLpNorm_add_le (hf := ((hfm n).sub ((hg j).aestronglyMeasurable n)).mono_measure hν)
          (hg := ((hg j).aestronglyMeasurable n).mono_measure hν) (by norm_num)
  constructor
  · apply OAI.UnifIntegrable.of_enn
    intro ε hε
    obtain ⟨j,hj⟩ := happrox (ε/2) (ε.half_pos hε.ne')
    obtain ⟨δ,hδ,hgδ⟩ := OAI.UnifIntegrable.enn_spec (hg j).1 (ε/2) (ε.half_pos hε.ne')
    refine ⟨δ,hδ,?_⟩
    intro n s hs
    calc
      _ ≤ eLpNorm (fun x => f n x-g j n x) 1 (μ.restrict s)+
          eLpNorm (g j n) 1 (μ.restrict s) := htri j n _ Measure.restrict_le_self
      _ ≤ ε/2+ε/2 := add_le_add
        ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hj n)) (hgδ n s hs)
      _ = ε := ε.add_halves
    exact hfm
  · obtain ⟨j,hj⟩ := happrox 1 (by norm_num)
    obtain ⟨C,hC⟩ := (hg j).2
    refine ⟨1+C,?_⟩
    intro n
    calc
      _ ≤ eLpNorm (fun x => f n x-g j n x) 1 μ+eLpNorm (g j n) 1 μ := htri j n _ le_rfl
      _ ≤ 1+C := add_le_add (hj n) (hC n)
      _ = _ := by simp

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform integrability transferred through a measure-preserving chart -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_of_comp_measurePreserving
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {φ : X → Y} (hφ : MeasurePreserving φ μ ν)
    {f : ℕ → Y → ℝ} (hf : ∀ n, Measurable (f n))
    (h : UniformIntegrable (fun n => f n ∘ φ) 1 μ) : UniformIntegrable f 1 ν := by
  constructor
  · apply OAI.UnifIntegrable.of_enn'
    intro ε hε
    obtain ⟨δ,hδ,hsmall⟩ := OAI.UnifIntegrable.enn_spec' h.1 ε hε
    refine ⟨δ,hδ,?_⟩
    intro n s hs hνs
    have hpre : μ (φ ⁻¹' s) ≤ δ := by
      rw [hφ.measure_preimage hs.nullMeasurableSet]
      exact hνs
    have hb := hsmall n (φ ⁻¹' s) (hs.preimage hφ.measurable) hpre
    rw [eLpNorm_comp_measurePreserving (hf n).aestronglyMeasurable.restrict
      (hφ.restrict_preimage hs)] at hb
    exact hb
    exact fun n => (hf n).aestronglyMeasurable
  · obtain ⟨C,hC⟩ := h.2
    refine ⟨C,fun n => ?_⟩
    have he := eLpNorm_comp_measurePreserving (p := (1 : ℝ≥0∞))
      (hf n).aestronglyMeasurable hφ
    rw [← he]
    exact hC n

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Tensoring a uniformly integrable family with one fixed integrable function -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

 theorem eLpNorm_mul_prod_one {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (fun p : X × Y => f p.1*g p.2) 1 (μ.prod ν) =
      eLpNorm f 1 μ*eLpNorm g 1 ν := by
  have hm : AEStronglyMeasurable (fun p : X × Y => f p.1*g p.2) (μ.prod ν) :=
    ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_one_eq_lintegral_enorm]
  simp only [enorm_mul]
  have he : AEMeasurable (fun p : X × Y => ‖f p.1‖ₑ*‖g p.2‖ₑ) (μ.prod ν) :=
    ((hf.enorm.comp measurable_fst).mul (hg.enorm.comp measurable_snd)).aemeasurable
  rw [lintegral_prod _ he]
  simp_rw [lintegral_const_mul _ hg.enorm]
  exact lintegral_mul_const _ hf.enorm

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Nonnegative uniformly integrable densities have uniformly small clipping errors -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem uniform_min_truncation {f : ℕ → X → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n x, 0 ≤ f n x)
    (hui : UniformIntegrable f 1 μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C : ℝ≥0, ∀ K : ℝ, (C:ℝ) ≤ K → ∀ n,
      eLpNorm (fun x => f n x-min (f n x) K) 1 μ ≤ ε := by
  obtain ⟨C,hC⟩ := hui.spec (by norm_num) (by norm_num) hε
  refine ⟨C,fun K hK n => ?_⟩
  apply le_trans _ (hC n)
  apply eLpNorm_mono
  intro x
  change ‖f n x-min (f n x) K‖ ≤ ‖{x | C ≤ ‖f n x‖₊}.indicator (f n) x‖
  by_cases hx : f n x ≤ K
  · rw [min_eq_left hx,sub_self,norm_zero]
    exact norm_nonneg _
  · have hlt : K < f n x := lt_of_not_ge hx
    have hcx : C ≤ ‖f n x‖₊ := by
      have hb : (C:ℝ) ≤ ‖f n x‖ := by
        rw [Real.norm_of_nonneg (hf n x)]
        exact hK.trans hlt.le
      exact_mod_cast hb
    rw [min_eq_right hlt.le,indicator_of_mem (show x ∈ {x | C ≤ ‖f n x‖₊} from hcx),
      Real.norm_of_nonneg (sub_nonneg.mpr hlt.le),Real.norm_of_nonneg (hf n x)]
    exact sub_le_self _ (C.coe_nonneg.trans hK)

end BoltzmannNonuniqueness.Compactness

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

theorem preRate_measurable {f : X × Velocity → ℝ} (hf : Measurable f) : Measurable (preRate f) := by
  unfold preRate collisionKernel normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem preRate_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z)
    (z : (X × (Velocity × Velocity)) × Sphere) : 0 ≤ preRate f z :=
  mul_nonneg (mul_nonneg (collisionKernel_nonneg _ _ _) (hf _)) (hf _)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable physical gain and loss and their equal total mass -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_r413687_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
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

theorem lossDensity_formula (f : X × Velocity → ℝ) (p : X × Velocity) :
    lossDensity f p = ∫ q : Velocity × Sphere,
      collisionKernel p.2 q.1 q.2*f (p.1,p.2)*f (p.1,q.1)
        ∂((volume : Measure Velocity).prod sphereArea) := rfl

theorem gainDensity_nonneg {f : X × Velocity → ℝ} (hf : ∀ z, 0 ≤ f z) (p : X × Velocity) :
    0 ≤ gainDensity f p := integral_nonneg (fun _ => preRate_nonneg hf _)

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveSourceFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! # A bounded comparison variable for two positive characteristic equations -/
noncomputable section
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem positiveDifference_derivative_identity {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (a b k l e f : ℝ) :
    (((a-k*u+e)-(b-l*v+f))*(1+u+v)-
      (u-v)*((a-k*u+e)+(b-l*v+f)))/(1+u+v)^2 =
      positiveDifferenceForcing u v a b k l e f-
        positiveDifferenceDamping u v a b k l e f*positiveDifference u v := by
  have hd : (1+u+v) ≠ 0 := by positivity
  unfold positiveDifferenceForcing positiveDifferenceDamping positiveDifference
  field_simp
  ring

theorem positiveDifference_damping_nonneg {u v a b k l e f : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hk : 0 ≤ k) (hl : 0 ≤ l) (he : 0 ≤ e) (hf : 0 ≤ f) :
    0 ≤ positiveDifferenceDamping u v a b k l e f := by
  unfold positiveDifferenceDamping
  positivity

theorem positiveDifference_forcing_bound {u v a b k l e f : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (he : 0 ≤ e) (hf : 0 ≤ f) :
    |positiveDifferenceForcing u v a b k l e f| ≤
      |a-b|/(1+u+v)+e/(1+u)+f/(1+v)+|k-l| := by
  let d := 1+u+v
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hp : 0 ≤ u+v+4*u*v := by positivity
  have hp' : u+v+4*u*v ≤ 2*d^2 := by dsimp [d] <;> nlinarith [sq_nonneg (u-v)]
  have hc : (u+v+4*u*v)/(2*d^2) ≤ 1 := (div_le_one (by positivity)).mpr hp'
  have hfq : |(l-k)*(u+v+4*u*v)/(2*d^2)| ≤ |k-l| := by
    rw [mul_div_assoc,abs_mul,abs_of_nonneg (div_nonneg hp (by positivity)),abs_sub_comm]
    exact mul_le_of_le_one_right (abs_nonneg _) hc
  have hab : |a-b+e-f| ≤ |a-b|+e+f := by
    calc
      _ ≤ |a-b+e|+|f| := abs_sub _ _
      _ ≤ (|a-b|+|e|)+|f| := add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [abs_of_nonneg he,abs_of_nonneg hf]
  have heq : e/d ≤ e/(1+u) := div_le_div_of_nonneg_left he (by positivity) (by dsimp [d] <;> linarith)
  have hfq' : f/d ≤ f/(1+v) := div_le_div_of_nonneg_left hf (by positivity) (by dsimp [d] <;> linarith)
  calc
    _ ≤ |(a-b+e-f)/d|+|(l-k)*(u+v+4*u*v)/(2*d^2)| := abs_add_le _ _
    _ ≤ (|a-b|+e+f)/d+|k-l| := by
      gcongr
      · rw [abs_div,abs_of_pos hd]
        exact div_le_div_of_nonneg_right hab hd.le
    _ = |a-b|/d+e/d+f/d+|k-l| := by ring
    _ ≤ _ := by dsimp [d] at * <;> linarith

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # A bounded density truncation is controlled by the positive-difference metric -/
noncomputable section
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem min_difference_le_positiveDifference {u v K : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hK : 0 ≤ K) :
    |min u K-min v K| ≤ (1+2*K)*|positiveDifference u v| := by
  have hd : 0 < 1+u+v := by positivity
  rw [positiveDifference,abs_div,abs_of_pos hd,← mul_div_assoc]
  apply (le_div_iff₀ hd).mpr
  by_cases huK : u ≤ K
  · rw [min_eq_left huK]
    by_cases hvK : v ≤ K
    · rw [min_eq_left hvK]
      calc
        _ ≤ |u-v| * (1+2*K) :=
          mul_le_mul_of_nonneg_left (by linarith : 1+u+v ≤ 1+2*K) (abs_nonneg _)
        _ = _ := mul_comm _ _
    · have hKv : K ≤ v := le_of_not_ge hvK
      rw [min_eq_right hKv,abs_of_nonpos (sub_nonpos.mpr huK),
        abs_of_nonpos (sub_nonpos.mpr (huK.trans hKv))]
      nlinarith [mul_nonneg (sub_nonneg.mpr hKv)
        (show 0 ≤ 1+K+u by positivity),sq_nonneg (K-u)]
  · have hKu : K ≤ u := le_of_not_ge huK
    rw [min_eq_right hKu]
    by_cases hvK : v ≤ K
    · rw [min_eq_left hvK,abs_of_nonneg (sub_nonneg.mpr hvK),
        abs_of_nonneg (sub_nonneg.mpr (hvK.trans hKu))]
      nlinarith [mul_nonneg (sub_nonneg.mpr hKu)
        (show 0 ≤ 1+K+v by positivity),sq_nonneg (K-v)]
    · rw [min_eq_right (le_of_not_ge hvK),sub_self,abs_zero,zero_mul]
      exact mul_nonneg (by positivity) (abs_nonneg _)

end BoltzmannNonuniqueness.TransportPrimitive

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionDissipation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end CollisionCompactness
end BoltzmannNonuniqueness

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

/-! # Maxwellian and density logarithms under collision symmetry -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness

namespace CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem collisionJump_log_maxwellian (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p : X × Velocity => Real.log (maxwellian p.2)) z = 0 := by
  have hw : ‖(z.2 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp z.2.property
  have he := scatter_energy z.1.2.1 z.1.2.2 z.2 hw
  unfold collisionJump
  simp only [log_maxwellian]
  linarith

omit [MeasurableSpace X] in
theorem collisionJump_log_density (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p => Real.log (f p)) z =
      Real.log ((f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
        f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))/(f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))) := by
  rw [Real.log_div (mul_ne_zero (hf _).ne' (hf _).ne') (mul_ne_zero (hf _).ne' (hf _).ne'),
    Real.log_mul (hf _).ne' (hf _).ne',Real.log_mul (hf _).ne' (hf _).ne']
  unfold collisionJump
  ring

omit [MeasurableSpace X] in
theorem collisionJump_scatter (ψ : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump ψ (scatterTriple z) = -collisionJump ψ z := by
  have hi := scatterTriple_involutive (X := X) z
  have hl := congrArg (fun p => p.1.2.1) hi
  have hr := congrArg (fun p => p.1.2.2) hi
  change scatterLeft (scatterLeft z.1.2.1 z.1.2.2 z.2)
    (scatterRight z.1.2.1 z.1.2.2 z.2) z.2 = z.1.2.1 at hl
  change scatterRight (scatterLeft z.1.2.1 z.1.2.2 z.2)
    (scatterRight z.1.2.1 z.1.2.2 z.2) z.2 = z.1.2.2 at hr
  change ψ (z.1.1,scatterLeft (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2)+
    ψ (z.1.1,scatterRight (scatterLeft z.1.2.1 z.1.2.2 z.2)
      (scatterRight z.1.2.1 z.1.2.2 z.2) z.2)-
    ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)-
    ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) = _
  rw [hl,hr]
  unfold collisionJump
  ring

end CollisionCompactness
end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedVelocityIntegral
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Absolute entropy for bounded densities with bounded velocity support -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X]

theorem bounded_velocity_integrable {μ : Measure X} [IsFiniteMeasure μ] {N A : ℝ}
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hfb : ∀ p, |f p| ≤ A)
    (hfs : ∀ p, N < ‖p.2‖ → f p = 0) : Integrable f (μ.prod (volume : Measure Velocity)) := by
  have hi : Integrable ((Metric.closedBall (0 : Velocity) N).indicator (fun _ : Velocity => A)) :=
    (integrableOn_const (isCompact_closedBall (0 : Velocity) N).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  apply (hi.comp_snd μ).mono' hfm.aestronglyMeasurable
  filter_upwards [] with p
  change ‖f p‖ ≤ (Metric.closedBall (0 : Velocity) N).indicator (fun _ => A) p.2
  by_cases hp : p.2 ∈ Metric.closedBall 0 N
  · rw [indicator_of_mem hp,Real.norm_eq_abs]
    exact hfb p
  · have hv : N < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
    rw [hfs p hv,norm_zero,indicator_of_notMem hp]

theorem bounded_velocity_finiteEntropy {N A : ℝ} (hN : 0 ≤ N) {f : Density}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ A)
    (hfs : ∀ p, N < ‖p.2‖ → f p = 0) : FiniteEntropyDatum f := by
  have hi : Integrable f (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact bounded_velocity_integrable hfm (fun p => (abs_of_nonneg (hfn p)).trans_le (hfb p)) hfs
  have hEm : Measurable (fun p : Phase => ‖p.2‖^2*f p) :=
    (measurable_snd.norm.pow_const 2).mul hfm
  have hEi : Integrable (fun p : Phase => ‖p.2‖^2*f p) := by
    rw [Measure.volume_eq_prod]
    apply bounded_velocity_integrable (A := N^2*A) hEm
    · intro p
      by_cases hp : N < ‖p.2‖
      · rw [hfs p hp,mul_zero,abs_zero]
        have hA : 0 ≤ A := (hfn p).trans (hfb p)
        positivity
      · rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (hfn p))]
        have hs : ‖p.2‖^2 ≤ N^2 := (sq_le_sq₀ (norm_nonneg _) hN).mpr (le_of_not_gt hp)
        exact mul_le_mul hs (hfb p) (hfn p) (sq_nonneg N)
    · intro p hp
      rw [hfs p hp,mul_zero]
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) A)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  have hlog : Integrable (fun p : Phase => f p*Real.log (f p)) := by
    rw [Measure.volume_eq_prod]
    exact bounded_velocity_integrable (Real.continuous_mul_log.measurable.comp hfm)
      (fun p => by simpa only [Real.norm_eq_abs] using hB (f p) ⟨hfn p,hfb p⟩)
      (fun p hp => by rw [hfs p hp,zero_mul])
  refine ⟨Filter.Eventually.of_forall hfn,hfm.aestronglyMeasurable,?_⟩
  apply ((hi.add hEi).add hlog.norm).congr
  filter_upwards [] with p
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg (hfn p),entropyMoment]
  ring

end BoltzmannNonuniqueness

end

end

section

/-! # Velocity fibers of bounded supported densities -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness

theorem bounded_velocity_fiber_integrable {N A : ℝ} {f : Velocity → ℝ}
    (hfm : Measurable f) (hfb : ∀ v, |f v| ≤ A)
    (hfs : ∀ v, N < ‖v‖ → f v = 0) : Integrable f := by
  have hi : Integrable ((Metric.closedBall (0 : Velocity) N).indicator (fun _ : Velocity => A)) :=
    (integrableOn_const (isCompact_closedBall (0 : Velocity) N).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  apply hi.mono' hfm.aestronglyMeasurable
  filter_upwards [] with v
  by_cases hv : v ∈ Metric.closedBall 0 N
  · rw [indicator_of_mem hv,Real.norm_eq_abs]
    exact hfb v
  · have hNv : N < ‖v‖ := by
      simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hv
    rw [hfs v hNv,norm_zero,indicator_of_notMem hv]

theorem bounded_velocity_fiber_weighted {N A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    {f ψ : Velocity → ℝ} (hfm : Measurable f) (hψm : Measurable ψ)
    (hfb : ∀ v, |f v| ≤ A) (hfs : ∀ v, N < ‖v‖ → f v = 0)
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C) : Integrable (fun v => ψ v*f v) := by
  apply bounded_velocity_fiber_integrable (N := N) (A := C*A) (hψm.mul hfm)
  · intro v
    change |ψ v*f v| ≤ C*A
    by_cases hv : N < ‖v‖
    · rw [hfs v hv,mul_zero,abs_zero]
      exact mul_nonneg hC hA
    · rw [abs_mul]
      exact mul_le_mul (hψ v (le_of_not_gt hv)) (hfb v) (abs_nonneg _) hC
  · intro v hv
    change ψ v*f v = 0
    rw [hfs v hv,mul_zero]

end BoltzmannNonuniqueness

end

end

section

/-! # An explicit integral bound for compact velocity support -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X]

theorem bounded_velocity_integral_bound {μ : Measure X} [IsFiniteMeasure μ] {N A : ℝ}
    {f : X × Velocity → ℝ} (hfb : ∀ p, |f p| ≤ A)
    (hfs : ∀ p, N < ‖p.2‖ → f p = 0) :
    |∫ p, f p ∂μ.prod volume| ≤
      μ.real univ*(volume : Measure Velocity).real (Metric.closedBall 0 N)*A := by
  have hi : Integrable ((Metric.closedBall (0 : Velocity) N).indicator (fun _ : Velocity => A)) :=
    (integrableOn_const (isCompact_closedBall (0 : Velocity) N).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  have h := norm_integral_le_of_norm_le (hi.comp_snd μ) (show ∀ᵐ p ∂μ.prod volume,
      ‖f p‖ ≤ (Metric.closedBall (0 : Velocity) N).indicator (fun _ => A) p.2 from by
    filter_upwards [] with p
    by_cases hp : p.2 ∈ Metric.closedBall 0 N
    · rw [indicator_of_mem hp,Real.norm_eq_abs]; exact hfb p
    · have hv : N < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
      rw [hfs p hv,norm_zero,indicator_of_notMem hp])
  rw [Real.norm_eq_abs,integral_fun_snd,integral_indicator Metric.isClosed_closedBall.measurableSet,
    setIntegral_const,smul_eq_mul,smul_eq_mul] at h
  exact h.trans_eq (by ring)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyUniformIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Joint value and velocity truncation controlled by absolute entropy -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem entropyTruncation_measurable (R : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (entropyTruncation R f) :=
  Measurable.ite ((measurableSet_le measurable_snd.norm measurable_const).inter
    (measurableSet_le hf measurable_const)) hf measurable_const

omit [MeasurableSpace X] in
theorem entropyGauge_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ entropyGauge f p := mul_nonneg (hf p) (by positivity)

omit [MeasurableSpace X] in
theorem entropyGauge_ge_density {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    f p ≤ entropyGauge f p := by
  have hs := mul_nonneg (hf p) (sq_nonneg ‖p.2‖)
  have hl := mul_nonneg (hf p) (abs_nonneg (Real.log (f p)))
  unfold entropyGauge
  nlinarith

omit [MeasurableSpace X] in
theorem entropyTruncation_bounds (R : ℝ) {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ entropyTruncation R f p ∧ entropyTruncation R f p ≤ Real.exp R := by
  unfold entropyTruncation
  split_ifs with hp
  · exact ⟨hf p,hp.2⟩
  · exact ⟨le_rfl,(Real.exp_pos R).le⟩

omit [MeasurableSpace X] in
theorem entropyTruncation_support (R : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity)
    (hp : R < ‖p.2‖) : entropyTruncation R f p = 0 := by
  simp only [entropyTruncation,not_le.mpr hp,false_and,ite_false, if_false]

omit [MeasurableSpace X] in
theorem entropyTruncation_error {R : ℝ} (hR : 1 ≤ R) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    |f p-entropyTruncation R f p| ≤ entropyGauge f p/R := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  unfold entropyTruncation
  split_ifs with hp
  · rw [sub_self,abs_zero]
    exact div_nonneg (entropyGauge_nonneg hf p) hR0.le
  · rw [sub_zero,abs_of_nonneg (hf p)]
    apply (le_div_iff₀ hR0).mpr
    have hn := hf p
    have he : 0 ≤ ‖p.2‖^2 := sq_nonneg _
    have hl : 0 ≤ |Real.log (f p)| := abs_nonneg _
    by_cases hv : ‖p.2‖ ≤ R
    · have hbig : Real.exp R < f p := lt_of_not_ge (fun ha => hp ⟨hv,ha⟩)
      have hlog : R ≤ Real.log (f p) := by
        simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos R) hbig.le
      have hh := mul_le_mul_of_nonneg_left (hlog.trans (le_abs_self _)) hn
      unfold entropyGauge
      nlinarith [mul_nonneg hn he]
    · have hvR : R < ‖p.2‖ := lt_of_not_ge hv
      have hs : R ≤ ‖p.2‖^2 := by nlinarith [norm_nonneg p.2]
      have hh := mul_le_mul_of_nonneg_left hs hn
      unfold entropyGauge
      nlinarith [mul_nonneg hn hl]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform L1 approximation by bounded velocity truncations -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem integrable_of_entropyGauge {μ : Measure (X × Velocity)} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyGauge f) μ) : Integrable f μ := by
  apply hi.mono' hfm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    rw [Real.norm_of_nonneg (hf p)]
    exact entropyGauge_ge_density hf p)

theorem entropyTruncation_integrable {μ : Measure X} [IsFiniteMeasure μ]
    (R : ℝ) {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    Integrable (entropyTruncation R f) (μ.prod volume) :=
  bounded_velocity_integrable (entropyTruncation_measurable R hfm)
    (fun p => (abs_of_nonneg (entropyTruncation_bounds R hf p).1).trans_le
      (entropyTruncation_bounds R hf p).2) (entropyTruncation_support R f)

theorem entropyTruncation_L1_bound {μ : Measure X} [IsFiniteMeasure μ]
    {R C : ℝ} (hR : 1 ≤ R) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyGauge f) (μ.prod volume))
    (hb : (∫ p, entropyGauge f p ∂μ.prod volume) ≤ C) :
    eLpNorm (fun p => f p-entropyTruncation R f p) 1 (μ.prod volume) ≤ ENNReal.ofReal (C/R) := by
  have hei := (integrable_of_entropyGauge hfm hf hi).sub (entropyTruncation_integrable R hfm hf)
  change Integrable (fun p => f p-entropyTruncation R f p) (μ.prod volume) at hei
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hei]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ p, entropyGauge f p/R ∂μ.prod volume :=
      integral_mono hei.norm (hi.div_const R) (fun p => by
        simpa only [Real.norm_eq_abs] using entropyTruncation_error hR hf p)
    _ = (∫ p, entropyGauge f p ∂μ.prod volume)/R := integral_div R _
    _ ≤ C/R := div_le_div_of_nonneg_right hb (zero_le_one.trans hR)

theorem entropyTruncation_uniformIntegrable {μ : Measure X} [IsFiniteMeasure μ]
    (R : ℝ) {f : ℕ → X × Velocity → ℝ} (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p) :
    UniformIntegrable (fun n => entropyTruncation R (f n)) 1 (μ.prod volume) := by
  let g : X × Velocity → ℝ := fun p =>
    (Metric.closedBall (0:Velocity) R).indicator (fun _ => Real.exp R) p.2
  have hi : Integrable g (μ.prod volume) :=
    ((integrableOn_const (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet).comp_snd μ
  have hg := uniformIntegrable_const (ι := ℕ) (by norm_num : (1:ℝ≥0∞) ≤ 1) (by norm_num) (memLp_one_iff_integrable.mpr hi)
  have hdom (n : ℕ) (p : X × Velocity) : ‖entropyTruncation R (f n) p‖ ≤ g p := by
    rw [Real.norm_of_nonneg (entropyTruncation_bounds R (hf n) p).1]
    by_cases hp : p.2 ∈ Metric.closedBall 0 R
    · rw [show g p = Real.exp R from indicator_of_mem hp _]
      exact (entropyTruncation_bounds R (hf n) p).2
    · have hv : R < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
      rw [entropyTruncation_support R (f n) p hv,show g p = 0 from indicator_of_notMem hp _]
  have hmono (n : ℕ) (s : Set (X × Velocity)) :
      eLpNorm (entropyTruncation R (f n)) 1 ((μ.prod volume).restrict s) ≤
        eLpNorm g 1 ((μ.prod volume).restrict s) :=
    eLpNorm_mono_real (hdom n)
  refine ⟨OAI.UnifIntegrable.of_enn ?_ (fun n => (entropyTruncation_measurable R (hfm n)).aestronglyMeasurable),?_⟩
  · intro ε hε
    obtain ⟨δ,hδ,hgδ⟩ := OAI.UnifIntegrable.enn_spec hg.1 ε hε
    exact ⟨δ,hδ,fun n s hs => (hmono n s).trans (hgδ n s hs)⟩
  · obtain ⟨C,hC⟩ := hg.2
    refine ⟨C,fun n => ?_⟩
    have h := (hmono n univ).trans (by simpa only [Measure.restrict_univ] using hC n)
    simpa only [Measure.restrict_univ] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform entropy and velocity moments imply L1 compactness hypotheses -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

 theorem exists_entropyTruncation_radius (C : ℝ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ j : ℕ, ENNReal.ofReal (C/((j:ℝ)+1)) ≤ ε := by
  have h : Tendsto (fun j : ℕ => C/((j:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have ht : Tendsto (fun j : ℕ => ENNReal.ofReal (C/((j:ℝ)+1))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h
  obtain ⟨j,hj⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨j,hj.le⟩

variable {X : Type*} [MeasurableSpace X]

theorem uniformIntegrable_of_entropyGauge {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable f 1 (μ.prod volume) := by
  apply Compactness.uniformIntegrable_of_approximation
    (g := fun j n => entropyTruncation ((j:ℝ)+1) (f n))
    (fun j => entropyTruncation_uniformIntegrable ((j:ℝ)+1) hfm hf)
  intro ε hε
  obtain ⟨j,hj⟩ := exists_entropyTruncation_radius C hε
  refine ⟨j,fun n => ?_⟩
  exact (entropyTruncation_L1_bound (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
    (hfm n) (hf n) (hi n) (hb n)).trans hj
  exact fun n => (hfm n).aestronglyMeasurable

theorem unifTight_of_entropyGauge {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UnifTight f 1 (μ.prod volume) := by
  intro ε hε
  obtain ⟨j,hj⟩ := exists_entropyTruncation_radius C hε
  let R : ℝ := (j:ℝ)+1
  let s : Set (X × Velocity) := univ ×ˢ Metric.closedBall 0 R
  have hs : MeasurableSet s := MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet
  refine ⟨s,?_,fun n => ?_⟩
  · rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  · have hdom (p : X × Velocity) : ‖sᶜ.indicator (f n) p‖ ≤ ‖f n p-entropyTruncation R (f n) p‖ := by
      by_cases hp : p ∈ s
      · rw [indicator_of_notMem (notMem_compl_iff.mpr hp),norm_zero]
        exact norm_nonneg _
      · have hv : R < ‖p.2‖ := by
          have hnv : p.2 ∉ Metric.closedBall 0 R := fun hv => hp ⟨mem_univ _,hv⟩
          simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hnv
        rw [indicator_of_mem (mem_compl hp),entropyTruncation_support R (f n) p hv,sub_zero]
    exact (eLpNorm_mono hdom).trans
      ((entropyTruncation_L1_bound (by dsimp [R]; have := Nat.cast_nonneg (α := ℝ) j; linarith)
        (hfm n) (hf n) (hi n) (hb n)).trans hj)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusTransport
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
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

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityCutoffEntropyError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform integrability of the linear velocity moment from entropy and energy -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem linearMoment_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (linearMoment f) := (measurable_const.add measurable_snd.norm).mul hf

theorem linearMoment_integrable {μ : Measure (X × Velocity)} {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyGauge f) μ) :
    Integrable (linearMoment f) μ := by
  apply (hi.const_mul 2).mono' (linearMoment_measurable hfm).aestronglyMeasurable
  filter_upwards [] with p
  change ‖(1+‖p.2‖)*f p‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hf p))]
  have h : 1+‖p.2‖ ≤ 2*(1+‖p.2‖^2+|Real.log (f p)|) := by
    nlinarith [sq_nonneg (‖p.2‖-1),abs_nonneg (Real.log (f p))]
  simpa only [linearMoment,entropyGauge,mul_assoc,mul_left_comm,mul_comm] using
    mul_le_mul_of_nonneg_right h (hf p)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RelativeCutoffConvergence
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The cutoff relative-entropy production about the Maxwellian -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem collisionJump_log_relative (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p => Real.log (f p/maxwellian p.2)) z =
      collisionJump (fun p => Real.log (f p)) z := by
  have hl (p : X × Velocity) : Real.log (f p/maxwellian p.2) =
      Real.log (f p)-Real.log (maxwellian p.2) :=
    Real.log_div (hf p).ne' (maxwellian_pos p.2).ne'
  have he : collisionJump (fun p => Real.log (f p/maxwellian p.2)) z =
      collisionJump (fun p => Real.log (f p)) z-
        collisionJump (fun p : X × Velocity => Real.log (maxwellian p.2)) z := by
    simp only [collisionJump,hl]
    ring
  rw [he,collisionJump_log_maxwellian,sub_zero]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_L1VelocityTranslationApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Four vanishing error terms have a vanishing nonnegative L1 sum -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strongL1_sub_of_common_limit {f g : ℕ → X → ℝ} {h : X → ℝ}
    (hf : Tendsto (fun n => eLpNorm (fun x => f n x-h x) 1 μ) atTop (𝓝 0))
    (hg : Tendsto (fun n => eLpNorm (fun x => g n x-h x) 1 μ) atTop (𝓝 0))
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hgm : ∀ n, AEStronglyMeasurable (g n) μ)
    (hhm : AEStronglyMeasurable h μ) :
    Tendsto (fun n => eLpNorm (fun x => f n x-g n x) 1 μ) atTop (𝓝 0) := by
  have ht := hf.add hg
  simp only [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  have he : (fun x => f n x-g n x) = (fun x => f n x-h x)+(fun x => h x-g n x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  dsimp only
  rw [he]
  exact (eLpNorm_add_le (hf := (hfm n).sub hhm) (hg := hhm.sub (hgm n)) (by norm_num)).trans_eq
    (congrArg (fun t => eLpNorm (fun x => f n x-h x) 1 μ+t) (eLpNorm_sub_comm h (g n) 1 μ))

end BoltzmannNonuniqueness.Compactness

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

/-! # The regularization error vanishes as the Gaussian is removed -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem tendsto_mul_abs_log_zero :
    Tendsto (fun δ : ℝ => δ*|Real.log δ|) (𝓝 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : Tendsto (fun δ : ℝ => |δ*Real.log δ|) (𝓝 0) (𝓝 0) := by
    simpa using Real.continuous_mul_log.abs.tendsto 0
  simpa only [norm_mul,Real.norm_eq_abs,abs_abs,abs_mul] using h

theorem tendsto_mul_affine_abs_log_zero (a b : ℝ) :
    Tendsto (fun δ : ℝ => δ*(a+b*|Real.log δ|)) (𝓝 0) (𝓝 0) := by
  have h := ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0)).mul_const a).add
    (tendsto_mul_abs_log_zero.mul_const b)
  convert h using 1
  · funext δ
    simp only [id_eq]
    ring
  · ring_nf

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedEntropyProduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded logarithmic tests recovering nonnegative relative entropy -/

noncomputable section

open Filter
open scoped Topology

namespace BoltzmannNonuniqueness

theorem boundedEntropyTest_bound (n : ℕ) (m u : ℝ) :
    |boundedEntropyTest n m u| ≤ n := by
  unfold boundedEntropyTest
  split_ifs with h hlog
  · simp
  · exact hlog
  · simp

theorem entropyDual_boundedEntropyTest_nonneg (n : ℕ) {m u : ℝ}
    (hm : 0 < m) (hu : 0 ≤ u) :
    0 ≤ entropyDual m u (boundedEntropyTest n m u) := by
  unfold boundedEntropyTest
  split_ifs with hz hlog
  · subst u
    dsimp [entropyDual]
    have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
    nlinarith
  · rw [entropyDual_log_ratio hm (lt_of_le_of_ne hu (Ne.symm hz))]
    exact scalarRelativeEntropy_nonneg hm hu
  · simp [entropyDual]

theorem entropyDual_boundedEntropyTest_tendsto {m u : ℝ}
    (hm : 0 < m) (hu : 0 ≤ u) :
    Tendsto (fun n : ℕ => entropyDual m u (boundedEntropyTest n m u)) atTop
      (𝓝 (scalarRelativeEntropy m u)) := by
  by_cases hz : u = 0
  · subst u
    simpa [boundedEntropyTest,scalarRelativeEntropy,Function.comp_def] using
      (entropyDual_zero_tendsto m).comp tendsto_natCast_atTop_atTop
  · have he : (fun n : ℕ => entropyDual m u (boundedEntropyTest n m u)) =ᶠ[atTop]
        (fun _ => scalarRelativeEntropy m u) := by
      filter_upwards [eventually_ge_atTop (Nat.ceil |Real.log (u/m)|)] with n hn
      have hlog : |Real.log (u/m)| ≤ (n:ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hn)
      simpa [boundedEntropyTest,hz,hlog] using
        entropyDual_log_ratio hm (lt_of_le_of_ne hu (Ne.symm hz))
    exact tendsto_const_nhds.congr' he.symm

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyRegularizationLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrable bounded entropy tests on the phase and spacetime measures -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem measurable_boundedEntropyTest (n : ℕ) {m u : X → ℝ}
    (hm : Measurable m) (hu : Measurable u) :
    Measurable (fun x => boundedEntropyTest n (m x) (u x)) := by
  have hlog := (hu.div hm).log
  exact Measurable.ite (measurableSet_eq_fun hu measurable_const) measurable_const
    (Measurable.ite (measurableSet_le hlog.abs measurable_const) hlog measurable_const)

theorem measurable_entropyDual {m u s : X → ℝ}
    (hm : Measurable m) (hu : Measurable u) (hs : Measurable s) :
    Measurable (fun x => entropyDual (m x) (u x) (s x)) :=
  (hu.mul hs).sub (hm.mul (hs.exp.sub measurable_const))

theorem integrable_entropyDual {m u s : X → ℝ}
    (hm : Integrable m μ) (hu : Integrable u μ) (hs : Measurable s)
    {C : ℝ} (hC : ∀ x, |s x| ≤ C) :
    Integrable (fun x => entropyDual (m x) (u x) (s x)) μ := by
  have hfirst := hu.bdd_mul hs.aestronglyMeasurable (ae_of_all μ hC)
  have hbound : ∀ x, |Real.exp (s x)-1| ≤ Real.exp C+1 := by
    intro x
    calc
      |Real.exp (s x)-1| ≤ |Real.exp (s x)|+|1| := abs_sub _ _
      _ = Real.exp (s x)+1 := by rw [abs_of_pos (Real.exp_pos _),abs_one]
      _ ≤ Real.exp C+1 := add_le_add (Real.exp_le_exp.mpr ((le_abs_self _).trans (hC x))) le_rfl
  have hsecond := hm.bdd_mul (hs.exp.sub measurable_const).aestronglyMeasurable
    (ae_of_all μ hbound)
  simpa only [entropyDual,mul_comm,Pi.sub_def,Pi.mul_def] using hfirst.sub hsecond

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_VolterraFubini
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Triangular Fubini identity for measurable characteristic sources

This elementary identity allows integration by parts against an integral
primitive without assuming the collision source is continuous in time.
-/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

theorem integral_mul_primitive {a b : ℝ} (hab : a ≤ b) {h g : ℝ → ℝ}
    (hh : IntervalIntegrable h volume a b) (hg : IntervalIntegrable g volume a b) :
    (∫ s in a..b, h s * (∫ t in a..s, g t)) =
      ∫ t in a..b, (∫ s in t..b, h s) * g t := by
  let ν : Measure ℝ := volume.restrict (Ioc a b)
  have hh' : Integrable h ν := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hh
  have hg' : Integrable g ν := (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hg
  let k : ℝ → ℝ → ℝ := fun s t => if t ≤ s then h s * g t else 0
  have hk : Integrable (Function.uncurry k) (ν.prod ν) := by
    have he : Function.uncurry k = {z : ℝ × ℝ | z.2 ≤ z.1}.indicator
        (fun z => h z.1 * g z.2) := rfl
    rw [he]
    exact (hh'.mul_prod hg').indicator (measurableSet_le measurable_snd measurable_fst)
  have hleft (s : ℝ) (hs : s ∈ Ioc a b) :
      (∫ t, k s t ∂ν) = h s * (∫ t in a..s, g t) := by
    have he : (fun t => k s t) = (Iic s).indicator (fun t => h s * g t) := rfl
    rw [he, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    have hset : Iic s ∩ Ioc a b = Ioc a s := by
      ext t
      simp only [mem_inter_iff, mem_Iic, mem_Ioc]
      constructor
      · rintro ⟨ht,ha,_⟩; exact ⟨ha,ht⟩
      · rintro ⟨ha,ht⟩; exact ⟨ht,ha,ht.trans hs.2⟩
    rw [hset, integral_const_mul, intervalIntegral.integral_of_le hs.1.le]
  have hright (t : ℝ) (ht : t ∈ Ioc a b) :
      (∫ s, k s t ∂ν) = (∫ s in t..b, h s) * g t := by
    have he : (fun s => k s t) = (Ici t).indicator (fun s => h s * g t) := rfl
    rw [he, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hset : Ici t ∩ Ioc a b = Icc t b := by
      ext s
      simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
      constructor
      · rintro ⟨ht,_,hb⟩; exact ⟨ht,hb⟩
      · rintro ⟨hs,hb⟩; exact ⟨hs,ht.1.trans_le hs,hb⟩
    rw [hset, integral_mul_const, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le ht.2]
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  calc
    _ = ∫ s, ∫ t, k s t ∂ν ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact (hleft s hs).symm
    _ = ∫ t, ∫ s, k s t ∂ν ∂ν := integral_integral_swap hk
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hright t ht

/-- Integration by parts with an integrable, possibly discontinuous source. -/
theorem integral_deriv_mul_primitive {a b : ℝ} (hab : a ≤ b) {h h' g : ℝ → ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt h (h' t) t)
    (hh' : IntervalIntegrable h' volume a b) (hg : IntervalIntegrable g volume a b)
    (hhg : IntervalIntegrable (fun t => h t*g t) volume a b) :
    (∫ s in a..b, h' s * (∫ t in a..s, g t)) =
      h b * (∫ t in a..b, g t) - ∫ t in a..b, h t*g t := by
  rw [integral_mul_primitive hab hh' hg]
  have he (t : ℝ) (ht : t ∈ Icc a b) : (∫ s in t..b, h' s) = h b-h t := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro s hs
      rw [uIcc_of_le ht.2] at hs
      exact hd s ⟨ht.1.trans hs.1,hs.2⟩
    · exact hh'.mono_set (by
        rw [uIcc_of_le ht.2, uIcc_of_le hab]
        exact Icc_subset_Icc ht.1 le_rfl)
  calc
    _ = ∫ t in a..b, (h b-h t)*g t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      change (∫ s in t..b, h' s) * g t = (h b-h t)*g t
      rw [he t ht]
    _ = _ := by
      simp_rw [sub_mul]
      rw [intervalIntegral.integral_sub (hg.const_mul _) hhg, intervalIntegral.integral_const_mul]

end BoltzmannNonuniqueness.TransportPrimitive

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

/-! # Weak calculus for the actual damped characteristic formula -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

theorem damped_eq (L c : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    damped L c g t = Real.exp (-L*t)*c +
      ∫ r in 0..t, Real.exp (-L*(t-r))*g r := by
  unfold damped
  rw [mul_add, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  dsimp
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem primitive_integration_by_parts {a b c : ℝ} (hab : a ≤ b) {h h' g : ℝ → ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivAt h (h' t) t)
    (hh' : IntervalIntegrable h' volume a b) (hg : IntervalIntegrable g volume a b)
    (hh : ContinuousOn h (Icc a b)) :
    (∫ t in a..b, h' t * (c + ∫ r in a..t, g r)) + (∫ t in a..b, h t*g t) =
      h b*(c + ∫ r in a..b, g r) - h a*c := by
  have hp := intervalIntegral.continuousOn_primitive_interval' hg (left_mem_uIcc : a ∈ uIcc a b)
  have hhg := hg.continuousOn_mul (by simpa only [uIcc_of_le hab] using hh)
  have hb := integral_deriv_mul_primitive hab hd hh' hg hhg
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (by simpa only [uIcc_of_le hab] using ht)) hh'
  simp_rw [mul_add]
  rw [intervalIntegral.integral_add (hh'.mul_const c) (hh'.mul_continuousOn hp),
    intervalIntegral.integral_mul_const, hi, hb]
  ring

/-- Weak integration by parts for measurable characteristic forcing. -/
theorem damped_integration_by_parts {T L c : ℝ} (hT : 0 ≤ T) {g ψ ψ' : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T)
    (hψ : ContinuousOn ψ (Icc 0 T)) (hψ' : ContinuousOn ψ' (Icc 0 T))
    (hdψ : ∀ t ∈ Icc 0 T, HasDerivAt ψ (ψ' t) t) :
    (∫ t in 0..T, ψ' t*damped L c g t + ψ t*(g t-L*damped L c g t)) =
      ψ T*damped L c g T - ψ 0*c := by
  let h : ℝ → ℝ := fun t => ψ t*Real.exp (-L*t)
  let h' : ℝ → ℝ := fun t => (ψ' t-L*ψ t)*Real.exp (-L*t)
  let G : ℝ → ℝ := fun t => Real.exp (L*t)*g t
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt h (h' t) t := by
    intro t ht
    have he : HasDerivAt (fun r : ℝ => Real.exp (-L*r))
        (-L*Real.exp (-L*t)) t := by
      simpa only [id_eq, neg_mul, mul_comm, mul_one] using ((hasDerivAt_id t).const_mul (-L)).exp
    convert (hdψ t ht).mul he using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [h,h']
    ring
  have hc : ContinuousOn h (Icc 0 T) := hψ.mul (by fun_prop)
  have hc' : ContinuousOn h' (Icc 0 T) := (hψ'.sub (hψ.const_mul L)).mul (by fun_prop)
  have hGi : IntervalIntegrable G volume 0 T :=
    hg.continuousOn_mul (by fun_prop)
  have hh'i : IntervalIntegrable h' volume 0 T :=
    (hc'.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  have H := primitive_integration_by_parts (c := c) hT hd hh'i hGi hc
  have he (t : ℝ) : Real.exp (-L*t)*Real.exp (L*t) = 1 := by
    rw [← Real.exp_add]
    simp only [neg_mul, neg_add_cancel, Real.exp_zero]
  have hfirst (t : ℝ) : h' t*(c+∫ r in 0..t, G r) =
      ψ' t*damped L c g t - L*ψ t*damped L c g t := by
    dsimp [h',damped,G]
    ring
  have hsecond (t : ℝ) : h t*G t = ψ t*g t := by
    dsimp [h,G]
    calc
      _ = ψ t*(Real.exp (-L*t)*Real.exp (L*t))*g t := by ring
      _ = _ := by rw [he]; ring
  have h3i : IntervalIntegrable (fun t => h' t*(c+∫ r in 0..t,G r)) volume 0 T := by
    apply hh'i.mul_continuousOn
    exact continuousOn_const.add (intervalIntegral.continuousOn_primitive_interval' hGi left_mem_uIcc)
  have h4i : IntervalIntegrable (fun t => h t*G t) volume 0 T :=
    hGi.continuousOn_mul (by simpa only [uIcc_of_le hT] using hc)
  rw [← intervalIntegral.integral_add h3i h4i] at H
  have heq : (∫ t in 0..T, ψ' t*damped L c g t + ψ t*(g t-L*damped L c g t)) =
      ∫ t in 0..T, h' t*(c+∫ r in 0..t,G r) + h t*G t := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [hfirst,hsecond]
    ring
  rw [heq,H]
  dsimp [h,damped,G]
  simp only [mul_zero, neg_mul, Real.exp_zero, mul_one]
  ring

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Quantitative survival for positive characteristic equations -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.TransportPrimitive

theorem damped_absolutelyContinuous {T L c : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T) :
    AbsolutelyContinuousOnInterval (damped L c g) 0 T := by
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp (-L*t)) := by fun_prop
  have hi : IntervalIntegrable (fun r => Real.exp (L*r)*g r) volume 0 T :=
    hg.continuousOn_mul (by fun_prop)
  have hp := hi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 T := by
    simpa only [AbsolutelyContinuousOnInterval,dist_self,Finset.sum_const_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ × (ℕ → ℝ × ℝ) => (0:ℝ)) _ _)
  exact he.contDiffOn.absolutelyContinuousOnInterval.mul (hc.add hp)

theorem damped_derivative_ae {T L c : ℝ} {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 0 T) :
    ∀ᵐ t, t ∈ uIcc (0:ℝ) T →
      HasDerivAt (damped L c g) (g t-L*damped L c g t) t := by
  have hi : IntervalIntegrable (fun r => Real.exp (L*r)*g r) volume 0 T :=
    hg.continuousOn_mul (by fun_prop)
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht hm
  have hp := (ht hm 0 left_mem_uIcc).const_add c
  have he := ((hasDerivAt_id t).const_mul (-L)).exp
  have hd := he.mul hp
  have hexp : Real.exp (-L*t)*Real.exp (L*t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  refine hd.congr_deriv (Eq.symm ?_)
  · dsimp only [damped]
    dsimp only [id_eq] at hexp ⊢
    nlinarith only [congrArg (fun x : ℝ => x*g t) hexp]

end BoltzmannNonuniqueness.TransportPrimitive

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_VariableSurvival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Positive characteristic forcing with an integrable loss frequency -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem exp_absolutelyContinuous {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => Real.exp (f t)) a b := by
  obtain ⟨C,hC⟩ := hf.exists_bound
  obtain ⟨L,hL⟩ := (Real.contDiff_exp.contDiffOn :
    ContDiffOn ℝ 1 Real.exp (Icc (-C) C)).exists_lipschitzOnWith
      (by norm_num) (convex_Icc _ _) isCompact_Icc
  apply hL.comp_absolutelyContinuousOnInterval _ hf
  intro t ht
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hC t ht)

/-- The integrating factor keeps the positive forcing when the frequency is only integrable. -/
theorem variable_survival_with_source {T : ℝ} (hT : 0 ≤ T)
    {u r k g : ℝ → ℝ} (hu : AbsolutelyContinuousOnInterval u 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hg : IntervalIntegrable g volume 0 T)
    (hr : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt u (r t) t)
    (hb : ∀ᵐ t, t ∈ Icc 0 T → g t-k t*u t ≤ r t) :
    Real.exp (-(∫ t in 0..T, k t))*u 0 +
      (∫ t in 0..T, Real.exp (-((∫ s in 0..T, k s)-(∫ s in 0..t, k s)))*g t) ≤ u T := by
  let K : ℝ → ℝ := fun t => ∫ s in 0..t, k s
  let W : ℝ → ℝ := fun t => Real.exp (K t)*u t
  have hK : AbsolutelyContinuousOnInterval K 0 T :=
    hk.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have he := exp_absolutelyContinuous hK
  have hW : AbsolutelyContinuousOnInterval W 0 T := he.mul hu
  have hi : IntervalIntegrable (fun t => Real.exp (K t)*g t) volume 0 T :=
    hg.continuousOn_mul he.continuousOn
  have hd : ∀ᵐ t, t ∈ Icc 0 T → Real.exp (K t)*g t ≤ deriv W t := by
    filter_upwards [hk.ae_hasDerivAt_integral,hr,hb] with t ht hrt hbt hmem
    have hkt : HasDerivAt K (k t) t := ht (by simpa only [uIcc_of_le hT] using hmem)
      0 left_mem_uIcc
    have hwt := hkt.exp.mul (hrt hmem)
    change HasDerivAt W _ t at hwt
    rw [hwt.deriv]
    have hp := mul_le_mul_of_nonneg_left (hbt hmem) (Real.exp_pos (K t)).le
    nlinarith only [hp]
  have hint : (∫ t in 0..T, Real.exp (K t)*g t) ≤ ∫ t in 0..T, deriv W t := by
    apply intervalIntegral.integral_mono_ae_restrict hT hi hW.intervalIntegrable_deriv
    filter_upwards [ae_restrict_of_ae hd,ae_restrict_mem measurableSet_Icc] with t ht hm
    exact ht hm
  rw [hW.integral_deriv_eq_sub] at hint
  have hW0 : W 0 = u 0 := by simp [W,K]
  rw [hW0] at hint
  have hmul := mul_le_mul_of_nonneg_left hint (Real.exp_pos (-K T)).le
  have hcancel : Real.exp (-K T)*Real.exp (K T) = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  have heq : Real.exp (-K T)*(∫ t in 0..T, Real.exp (K t)*g t) =
      ∫ t in 0..T, Real.exp (-(K T-K t))*g t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [heq] at hmul
  dsimp only [W] at hmul
  rw [mul_sub,← mul_assoc,hcancel,one_mul] at hmul
  dsimp only [K] at hmul
  linarith

end BoltzmannNonuniqueness.TransportPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LinearCharacteristicBalance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The positive linear characteristic solution with locally integrable data -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem linearSolution_initial (a : ℝ) (k g : ℝ → ℝ) : linearSolution a k g 0 = a := by
  simp [linearSolution]

theorem linearSolution_formula (a : ℝ) (k g : ℝ → ℝ) (t : ℝ) :
    linearSolution a k g t = Real.exp (-(∫ s in 0..t, k s))*a+
      ∫ s in 0..t, Real.exp (-((∫ r in 0..t, k r)-(∫ r in 0..s, k r)))*g s := by
  rw [linearSolution,mul_add,← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [← mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem linearSolution_absolutelyContinuous {T : ℝ} (a : ℝ) {k g : ℝ → ℝ}
    (hk : IntervalIntegrable k volume 0 T) (hg : IntervalIntegrable g volume 0 T) :
    AbsolutelyContinuousOnInterval (linearSolution a k g) 0 T := by
  let K t := ∫ s in 0..t, k s
  have hK : AbsolutelyContinuousOnInterval K 0 T :=
    hk.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have he := exp_absolutelyContinuous hK
  have hgi : IntervalIntegrable (fun t => Real.exp (K t)*g t) volume 0 T :=
    hg.continuousOn_mul he.continuousOn
  have hG := hgi.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => a) 0 T :=
    (LipschitzWith.const a).lipschitzOnWith.absolutelyContinuousOnInterval
  exact (exp_absolutelyContinuous hK.neg).mul (hc.add hG)

theorem linearSolution_hasDerivAt_ae {T : ℝ} (hT : 0 ≤ T) (a : ℝ) {k g : ℝ → ℝ}
    (hk : IntervalIntegrable k volume 0 T) (hg : IntervalIntegrable g volume 0 T) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt (linearSolution a k g) (g t-k t*linearSolution a k g t) t := by
  let K t := ∫ s in 0..t, k s
  have hK : AbsolutelyContinuousOnInterval K 0 T :=
    hk.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hgi : IntervalIntegrable (fun t => Real.exp (K t)*g t) volume 0 T :=
    hg.continuousOn_mul (exp_absolutelyContinuous hK).continuousOn
  filter_upwards [hk.ae_hasDerivAt_integral,hgi.ae_hasDerivAt_integral] with t hkt hgt ht
  have htm : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using ht
  have hkd : HasDerivAt K (k t) t := hkt htm 0 left_mem_uIcc
  have hgd := (hgt htm 0 left_mem_uIcc).const_add a
  have hd := hkd.neg.exp.mul hgd
  have he : Real.exp (-K t)*Real.exp (K t) = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  change HasDerivAt (linearSolution a k g)
    (Real.exp (-K t)*(-k t)*(a+∫ s in 0..t, Real.exp (K s)*g s)+
      Real.exp (-K t)*(Real.exp (K t)*g t)) t at hd
  convert hd using 1
  all_goals try with_reducible_and_instances rfl
  change g t-k t*(Real.exp (-K t)*(a+∫ s in 0..t, Real.exp (K s)*g s)) =
    Real.exp (-K t)*(-k t)*(a+∫ s in 0..t, Real.exp (K s)*g s)+
      Real.exp (-K t)*(Real.exp (K t)*g t)
  rw [← mul_assoc (Real.exp (-K t)) (Real.exp (K t)),he,one_mul]
  ring

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Stability of a signed characteristic equation with nonnegative damping -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem linear_path_eq_solution {T : ℝ} (hT : 0 ≤ T) {u k r : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hr : IntervalIntegrable r volume 0 T)
    (hd : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt u (r t-k t*u t) t) :
    u T = linearSolution (u 0) k r T := by
  have hl := variable_survival_with_source hT hu hk hr hd
    (ae_of_all _ (fun _ _ => le_rfl))
  have hdn : ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt (fun s => -u s) ((-r t)-k t*(-u t)) t := by
    filter_upwards [hd] with t ht hmem
    convert (ht hmem).neg using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hn := variable_survival_with_source hT hu.neg hk hr.neg hdn
    (ae_of_all _ (fun _ _ => le_rfl))
  simp only [Pi.neg_apply,mul_neg,intervalIntegral.integral_neg] at hn
  rw [linearSolution_formula]
  linarith

theorem damped_path_abs_le {T : ℝ} (hT : 0 ≤ T) {u k r : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hr : IntervalIntegrable r volume 0 T)
    (hk0 : ∀ t ∈ Icc 0 T, 0 ≤ k t)
    (hd : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt u (r t-k t*u t) t) :
    |u T| ≤ |u 0|+∫ t in 0..T, |r t| := by
  rw [linear_path_eq_solution hT hu hk hr hd,linearSolution_formula]
  have hK : 0 ≤ ∫ t in 0..T, k t := intervalIntegral.integral_nonneg hT hk0
  have he : Real.exp (-(∫ t in 0..T, k t)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hK)
  have hs : |Real.exp (-(∫ t in 0..T, k t))*u 0| ≤ |u 0| := by
    rw [abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (abs_nonneg _) he
  have hkae : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] k := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hk0 t ⟨ht.1.le,ht.2⟩
  have hsource : |∫ t in 0..T,
      Real.exp (-((∫ s in 0..T, k s)-(∫ s in 0..t, k s)))*r t| ≤
      ∫ t in 0..T, |r t| := by
    have hb : ∀ᵐ t ∂volume, t ∈ Ioc 0 T →
        ‖Real.exp (-((∫ s in 0..T, k s)-(∫ s in 0..t, k s)))*r t‖ ≤ ‖r t‖ := by
      filter_upwards [] with t ht
      have hKt : (∫ s in 0..t, k s) ≤ ∫ s in 0..T, k s :=
        intervalIntegral.integral_mono_interval le_rfl ht.1.le ht.2 hkae hk
      have hex : Real.exp (-((∫ s in 0..T, k s)-(∫ s in 0..t, k s))) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (abs_nonneg _) hex
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le hT hb hr.norm
  exact (abs_add_le _ _).trans (add_le_add hs hsource)

end BoltzmannNonuniqueness.TransportPrimitive

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveComparisonBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform integrability upgrades positive-difference convergence to strong L1 convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
open TransportPrimitive
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem positiveDifference_L1 {u v : ℕ → X → ℝ}
    (hum : ∀ n, Measurable (u n)) (hvm : ∀ n, Measurable (v n))
    (hu : ∀ n x, 0 ≤ u n x) (hv : ∀ n x, 0 ≤ v n x)
    (hui : UniformIntegrable u 1 μ) (hvi : UniformIntegrable v 1 μ)
    (hd : Tendsto (fun n => eLpNorm (fun x => positiveDifference (u n x) (v n x)) 1 μ)
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => u n x-v n x) 1 μ) atTop (𝓝 0) := by
  have hclip (K : ℝ) (hK : 0 ≤ K) :
      Tendsto (fun n => eLpNorm (fun x => min (u n x) K-min (v n x) K) 1 μ) atTop (𝓝 0) := by
    have hmul := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (1+2*K)) hd
      (Or.inr ENNReal.ofReal_ne_top)
    simp only [mul_zero] at hmul
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul (fun _ => zero_le)
    intro n
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    exact ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using
        min_difference_le_positiveDifference (hu n x) (hv n x) hK)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hε4 : 0 < ε/4 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨C,hC⟩ := uniform_min_truncation hum hu hui hε4
  obtain ⟨D,hD⟩ := uniform_min_truncation hvm hv hvi hε4
  let K : ℝ := max (C:ℝ) (D:ℝ)
  have hK : 0 ≤ K := C.coe_nonneg.trans (le_max_left _ _)
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hclip K hK) (ε/4) hε4] with n hn
  have he : (fun x => u n x-v n x) =
      (fun x => u n x-min (u n x) K)+
      (fun x => min (u n x) K-min (v n x) K)+
      (fun x => min (v n x) K-v n x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [he]
  calc
    _ ≤ (eLpNorm (fun x => u n x-min (u n x) K) 1 μ+
        eLpNorm (fun x => min (u n x) K-min (v n x) K) 1 μ)+
        eLpNorm (fun x => min (v n x) K-v n x) 1 μ :=
      (eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)).trans
        (add_le_add (eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)) le_rfl)
    _ ≤ (ε/4+ε/4)+ε/4 := by
      apply add_le_add (add_le_add (hC K (le_max_left _ _) n) hn)
      change eLpNorm ((fun x => min (v n x) K)-v n) 1 μ ≤ _
      rw [eLpNorm_sub_comm]
      exact hD K (le_max_right _ _) n
    _ ≤ ε := by
      calc
        (ε/4+ε/4)+ε/4 ≤ (ε/4+ε/4)+(ε/4+ε/4) := add_le_add le_rfl le_self_add
        _ = 4*(ε/4) := by ring
        _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Absolute continuity and evolution of the bounded positive-path difference -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem inv_lipschitzOn_one : LipschitzOnWith 1 (fun x : ℝ => x⁻¹) (Ici 1) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have he : x⁻¹-y⁻¹ = (y-x)/(x*y) := by field_simp
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  rw [he,abs_div,abs_of_pos (mul_pos hx0 hy0),abs_sub_comm y x]
  apply (div_le_iff₀ (mul_pos hx0 hy0)).mpr
  have hxy : 1 ≤ x*y := by simpa only [one_mul] using mul_le_mul hx hy (by norm_num) hx0.le
  nlinarith [abs_nonneg (x-y)]

theorem positiveDifference_absolutelyContinuous {T : ℝ} (hT : 0 ≤ T) {u v : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u 0 T) (hv : AbsolutelyContinuousOnInterval v 0 T)
    (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc 0 T, 0 ≤ v t) :
    AbsolutelyContinuousOnInterval (fun t => positiveDifference (u t) (v t)) 0 T := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1:ℝ)) 0 T :=
    (LipschitzWith.const 1).lipschitzOnWith.absolutelyContinuousOnInterval
  have hd : AbsolutelyContinuousOnInterval (fun t => 1+u t+v t) 0 T := (hc.add hu).add hv
  have hi := inv_lipschitzOn_one.comp_absolutelyContinuousOnInterval
    (fun t ht => by
      have hmem : t ∈ Icc 0 T := by simpa only [uIcc_of_le hT] using ht
      change 1 ≤ 1+u t+v t
      linarith [hu0 t hmem,hv0 t hmem]) hd
  exact (hu.sub hv).mul hi

theorem positiveDifference_hasDerivAt {u v : ℝ → ℝ} {du dv t : ℝ}
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) (hu0 : 0 ≤ u t) (hv0 : 0 ≤ v t) :
    HasDerivAt (fun s => positiveDifference (u s) (v s))
      (((du-dv)*(1+u t+v t)-(u t-v t)*(du+dv))/(1+u t+v t)^2) t := by
  exact (hu.sub hv).div ((hu.const_add 1).add hv) (by positivity)

theorem positiveDifference_evolution {u v : ℝ → ℝ} {a b k l e f t : ℝ}
    (hu : HasDerivAt u (a-k*u t+e) t) (hv : HasDerivAt v (b-l*v t+f) t)
    (hu0 : 0 ≤ u t) (hv0 : 0 ≤ v t) :
    HasDerivAt (fun s => positiveDifference (u s) (v s))
      (positiveDifferenceForcing (u t) (v t) a b k l e f-
        positiveDifferenceDamping (u t) (v t) a b k l e f*positiveDifference (u t) (v t)) t := by
  have h := positiveDifference_hasDerivAt hu hv hu0 hv0
  rwa [positiveDifference_derivative_identity hu0 hv0] at h

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Stability in a bounded metric for positive characteristic profiles -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem positiveDifference_stability {T : ℝ} (hT : 0 ≤ T)
    {u v a b k l e f : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u 0 T) (hv : AbsolutelyContinuousOnInterval v 0 T)
    (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc 0 T, 0 ≤ v t)
    (ha : ∀ t ∈ Icc 0 T, 0 ≤ a t) (hb : ∀ t ∈ Icc 0 T, 0 ≤ b t)
    (hk0 : ∀ t ∈ Icc 0 T, 0 ≤ k t) (hl0 : ∀ t ∈ Icc 0 T, 0 ≤ l t)
    (he0 : ∀ t ∈ Icc 0 T, 0 ≤ e t) (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (hdi : IntervalIntegrable
      (fun t => positiveDifferenceDamping (u t) (v t) (a t) (b t) (k t) (l t) (e t) (f t)) volume 0 T)
    (hri : IntervalIntegrable
      (fun t => positiveDifferenceForcing (u t) (v t) (a t) (b t) (k t) (l t) (e t) (f t)) volume 0 T)
    (hdu : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt u (a t-k t*u t+e t) t)
    (hdv : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt v (b t-l t*v t+f t) t) :
    |positiveDifference (u T) (v T)| ≤ |positiveDifference (u 0) (v 0)|+
      ∫ t in 0..T, |positiveDifferenceForcing (u t) (v t) (a t) (b t) (k t) (l t) (e t) (f t)| := by
  have hw := positiveDifference_absolutelyContinuous hT hu hv hu0 hv0
  apply damped_path_abs_le hT hw hdi hri
  · intro t ht
    exact positiveDifference_damping_nonneg (hu0 t ht) (hv0 t ht) (ha t ht) (hb t ht)
      (hk0 t ht) (hl0 t ht) (he0 t ht) (hf0 t ht)
  · filter_upwards [hdu,hdv] with t htu htv ht
    exact positiveDifference_evolution (htu ht) (htv ht) (hu0 t ht) (hv0 t ht)

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Integrability of the exact bounded positive-comparison equation -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem positiveComparison_integrable {T : ℝ} (hT : 0 ≤ T)
    {u v a b k l e f : ℝ → ℝ}
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc 0 T, 0 ≤ v t)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hl : IntervalIntegrable l volume 0 T)
    (he : IntervalIntegrable e volume 0 T) (hf : IntervalIntegrable f volume 0 T) :
    IntervalIntegrable (fun t =>
      positiveDifferenceDamping (u t) (v t) (a t) (b t) (k t) (l t) (e t) (f t)) volume 0 T ∧
    IntervalIntegrable (fun t =>
      positiveDifferenceForcing (u t) (v t) (a t) (b t) (k t) (l t) (e t) (f t)) volume 0 T := by
  have hd0 t (ht : t ∈ Icc 0 T) : 1+u t+v t ≠ 0 := by
    have := hu0 t ht
    have := hv0 t ht
    positivity
  have hc : ContinuousOn (fun t => (1+u t+v t)⁻¹) (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    exact ((continuousOn_const.add hu).add hv).inv₀ hd0
  have hq : ContinuousOn (fun t => (u t+v t+4*u t*v t)/(2*(1+u t+v t)^2))
      (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    apply ((hu.add hv).add ((continuousOn_const.mul hu).mul hv)).div
      (continuousOn_const.mul (((continuousOn_const.add hu).add hv).pow 2))
    intro t ht
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (hd0 t ht))
  constructor
  · have h := (((ha.add hb).add he).add hf |>.add ((hk.add hl).div_const 2)).mul_continuousOn hc
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    exact div_eq_mul_inv _ _
  · have h := (((ha.sub hb).add he).sub hf).mul_continuousOn hc
    have h' := (hl.sub hk).mul_continuousOn hq
    convert h.add h' using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    unfold positiveDifferenceForcing
    ring

theorem positiveComparison_error_integrable {T : ℝ} (hT : 0 ≤ T)
    {u v a b k l e f : ℝ → ℝ}
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc 0 T, 0 ≤ v t)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hl : IntervalIntegrable l volume 0 T)
    (he : IntervalIntegrable e volume 0 T) (hf : IntervalIntegrable f volume 0 T) :
    IntervalIntegrable (fun t => |a t-b t|/(1+u t+v t)+e t/(1+u t)+f t/(1+v t)+|k t-l t|)
      volume 0 T := by
  have hdu t (ht : t ∈ Icc 0 T) : 1+u t ≠ 0 := by have := hu0 t ht; positivity
  have hdv t (ht : t ∈ Icc 0 T) : 1+v t ≠ 0 := by have := hv0 t ht; positivity
  have hd t (ht : t ∈ Icc 0 T) : 1+u t+v t ≠ 0 := by
    have := hu0 t ht
    have := hv0 t ht
    positivity
  have cu : ContinuousOn (fun t => (1+u t)⁻¹) (uIcc 0 T) := by
    rw [uIcc_of_le hT]; exact (continuousOn_const.add hu).inv₀ hdu
  have cv : ContinuousOn (fun t => (1+v t)⁻¹) (uIcc 0 T) := by
    rw [uIcc_of_le hT]; exact (continuousOn_const.add hv).inv₀ hdv
  have cd : ContinuousOn (fun t => (1+u t+v t)⁻¹) (uIcc 0 T) := by
    rw [uIcc_of_le hT]; exact ((continuousOn_const.add hu).add hv).inv₀ hd
  have h := ((((ha.sub hb).abs.mul_continuousOn cd).add
    (he.mul_continuousOn cu)).add (hf.mul_continuousOn cv)).add (hk.sub hl).abs
  simpa only [div_eq_mul_inv] using h

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # A positive-path stability bound using only the physical source discrepancies -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive

theorem positiveDifference_error_bound {T : ℝ} (hT : 0 ≤ T)
    {u v a b k l e f : ℝ → ℝ}
    (hu : AbsolutelyContinuousOnInterval u 0 T) (hv : AbsolutelyContinuousOnInterval v 0 T)
    (hu0 : ∀ t ∈ Icc 0 T, 0 ≤ u t) (hv0 : ∀ t ∈ Icc 0 T, 0 ≤ v t)
    (ha0 : ∀ t ∈ Icc 0 T, 0 ≤ a t) (hb0 : ∀ t ∈ Icc 0 T, 0 ≤ b t)
    (hk0 : ∀ t ∈ Icc 0 T, 0 ≤ k t) (hl0 : ∀ t ∈ Icc 0 T, 0 ≤ l t)
    (he0 : ∀ t ∈ Icc 0 T, 0 ≤ e t) (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (hk : IntervalIntegrable k volume 0 T) (hl : IntervalIntegrable l volume 0 T)
    (he : IntervalIntegrable e volume 0 T) (hf : IntervalIntegrable f volume 0 T)
    (hdu : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt u (a t-k t*u t+e t) t)
    (hdv : ∀ᵐ t, t ∈ Icc 0 T → HasDerivAt v (b t-l t*v t+f t) t) :
    |positiveDifference (u T) (v T)| ≤ |positiveDifference (u 0) (v 0)|+
      ∫ t in 0..T, |a t-b t|/(1+u t+v t)+e t/(1+u t)+f t/(1+v t)+|k t-l t| := by
  have huc : ContinuousOn u (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using hu.continuousOn
  have hvc : ContinuousOn v (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using hv.continuousOn
  obtain ⟨hdi,hri⟩ := positiveComparison_integrable hT huc hvc hu0 hv0 ha hb hk hl he hf
  have h := positiveDifference_stability hT hu hv hu0 hv0 ha0 hb0 hk0 hl0 he0 hf0 hdi hri hdu hdv
  apply h.trans
  apply add_le_add le_rfl
  apply intervalIntegral.integral_mono_on hT hri.abs
    (positiveComparison_error_integrable hT huc hvc hu0 hv0 ha hb hk hl he hf)
  intro t ht
  exact positiveDifference_forcing_bound (hu0 t ht) (hv0 t ht) (he0 t ht) (hf0 t ht)

end BoltzmannNonuniqueness.TransportPrimitive

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_GaussianLocalExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A finite time measure equivalent to Lebesgue measure on every time window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem timeWeight_measurable : Measurable timeWeight := by unfold timeWeight; fun_prop

theorem windowInverseWeight_measurable (T : ℝ) : Measurable (windowInverseWeight T) :=
  (by fun_prop : Measurable (fun t : ℝ => Real.exp (t^2))).indicator measurableSet_Icc

theorem windowInverseWeight_nonneg (T t : ℝ) : 0 ≤ windowInverseWeight T t := by
  exact indicator_nonneg (fun t _ => (Real.exp_pos (t^2)).le) t

theorem windowInverseWeight_bound {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    |windowInverseWeight T t| ≤ Real.exp (T^2) := by
  rw [abs_of_nonneg (windowInverseWeight_nonneg T t)]
  by_cases ht : t ∈ Icc 0 T
  · simp only [windowInverseWeight,indicator_of_mem ht]
    apply Real.exp_le_exp.mpr
    nlinarith [ht.1,ht.2]
  · simp only [windowInverseWeight,indicator_of_notMem ht]
    exact (Real.exp_pos _).le

theorem finiteTimeMeasure_reweight (T : ℝ) :
    finiteTimeMeasure.withDensity (fun t => ENNReal.ofReal (windowInverseWeight T t)) =
      volume.restrict (Icc 0 T) := by
  rw [finiteTimeMeasure,← withDensity_mul _ timeWeight_measurable.ennreal_ofReal
    (windowInverseWeight_measurable T).ennreal_ofReal]
  have he : (fun t => ENNReal.ofReal (timeWeight t) *
      ENNReal.ofReal (windowInverseWeight T t)) = (Icc 0 T).indicator (fun _ => 1) := by
    funext t
    by_cases ht : t ∈ Icc 0 T
    · simp only [windowInverseWeight,indicator_of_mem ht,timeWeight]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      simp
    · simp [windowInverseWeight,ht]
  change volume.withDensity (fun t => ENNReal.ofReal (timeWeight t) *
    ENNReal.ofReal (windowInverseWeight T t)) = _
  rw [he]
  exact withDensity_indicator_one measurableSet_Icc

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_PairwiseSubsequenceCauchy
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A sequential criterion for a Cauchy sequence -/
noncomputable section
open Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness

theorem cauchySeq_of_pairwise_subsequences {X : Type*} [PseudoEMetricSpace X] (u : ℕ → X)
    (h : ∀ i j : ℕ → ℕ, Tendsto i atTop atTop → Tendsto j atTop atTop →
      Tendsto (fun n => edist (u (i n)) (u (j n))) atTop (𝓝 0)) : CauchySeq u := by
  classical
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  by_contra hn
  push Not at hn
  choose i hi j hj hd using hn
  have hit : Tendsto i atTop atTop := tendsto_atTop_mono hi tendsto_id
  have hjt : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  obtain ⟨n,hsmall⟩ := ((h i j hit hjt).eventually (gt_mem_nhds hε)).exists
  exact not_lt_of_ge (hd n) hsmall

end BoltzmannNonuniqueness.Compactness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_StrongMassClip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong L¹ convergence implies the bounded-test weak convergence used here -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem weakL1_of_integral_norm_sub {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hgm : Measurable g) (hg : Integrable g μ)
    (h : Tendsto (fun n => ∫ x, ‖f n x-g x‖ ∂μ) atTop (𝓝 0)) :
    WeakL1Converges μ f g := by
  refine ⟨hgm,hg,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have he n : (∫ x, ψ x*f n x ∂μ)-(∫ x, ψ x*g x ∂μ) =
      ∫ x, ψ x*(f n x-g x) ∂μ := by
    rw [← integral_sub ((hf n).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC))
      (hg.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC))]
    congr 1
    funext x
    ring
  have hzero : Tendsto (fun n => (∫ x, ψ x*f n x ∂μ)-(∫ x, ψ x*g x ∂μ))
      atTop (𝓝 0) := by
    simp_rw [he]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
    · intro n
      calc
        _ ≤ ∫ x, |C| * ‖f n x-g x‖ ∂μ := by
          apply norm_integral_le_of_norm_le (((hf n).sub hg).norm.const_mul |C|)
          filter_upwards [] with x
          rw [norm_mul,Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right ((hC x).trans (le_abs_self C)) (norm_nonneg _)
        _ = |C| * (∫ x, ‖f n x-g x‖ ∂μ) := integral_const_mul _ _
    · simpa using h.const_mul |C|
  have hplus := hzero.add (tendsto_const_nhds (x := ∫ x, ψ x*g x ∂μ))
  simpa only [sub_add_cancel,zero_add] using hplus

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Pairwise strong convergence identifies the existing weak L1 limit -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
open Published
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strongL1_of_pairwise_subsequences {f : ℕ → X → ℝ} {g : X → ℝ}
    (hfi : ∀ n, Integrable (f n) μ) (hw : WeakL1Converges μ f g)
    (hp : ∀ i j : ℕ → ℕ, Tendsto i atTop atTop → Tendsto j atTop atTop →
      Tendsto (fun n => eLpNorm (fun x => f (i n) x-f (j n) x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => f n x-g x) 1 μ) atTop (𝓝 0) := by
  let u n : Lp ℝ 1 μ := (hfi n).toL1 (f n)
  have hc : CauchySeq u := by
    apply cauchySeq_of_pairwise_subsequences
    intro i j hi hj
    have ht := hp i j hi hj
    apply ht.congr'
    apply Eventually.of_forall
    intro n
    exact (Lp.edist_toLp_toLp (f (i n)) (f (j n))
      (memLp_one_iff_integrable.mpr (hfi (i n))) (memLp_one_iff_integrable.mpr (hfi (j n)))).symm
  obtain ⟨q,hq⟩ := cauchySeq_tendsto_of_complete hc
  let v : X → ℝ := (Lp.aestronglyMeasurable q).mk q
  have hvm : Measurable v := (Lp.aestronglyMeasurable q).stronglyMeasurable_mk.measurable
  have hqv : (q : X → ℝ) =ᵐ[μ] v := (Lp.aestronglyMeasurable q).ae_eq_mk
  have hvi : Integrable v μ := (L1.integrable_coeFn q).congr hqv
  have hs : Tendsto (fun n => eLpNorm (fun x => f n x-v x) 1 μ) atTop (𝓝 0) := by
    have ht := hq.edist (tendsto_const_nhds (x := q))
    simp only [edist_self] at ht
    apply ht.congr'
    apply Eventually.of_forall
    intro n
    change edist ((memLp_one_iff_integrable.mpr (hfi n)).toLp (f n)) q = _
    rw [Lp.edist_def]
    apply eLpNorm_congr_ae
    filter_upwards [(hfi n).coeFn_toL1,hqv] with x hx hqx
    exact congrArg₂ (fun a b : ℝ => a-b) hx hqx
  have hvw : WeakL1Converges μ f v := by
    apply weakL1_of_integral_norm_sub hfi hvm hvi
    have he n : (∫ x, ‖f n x-v x‖ ∂μ) =
        (eLpNorm (fun x => f n x-v x) 1 μ).toReal := by
      change (∫ x, ‖(f n-v) x‖ ∂μ) = (eLpNorm (f n-v) 1 μ).toReal
      rw [eLpNorm_one_eq_lintegral_enorm,
        integral_norm_eq_lintegral_enorm ((hfi n).sub hvi).aestronglyMeasurable]
    simp only [he]
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hs
  have hvg : v =ᵐ[μ] g := hvw.unique hw
  apply hs.congr'
  exact Eventually.of_forall (fun n => eLpNorm_congr_ae
    (hvg.mono (fun x hx => congrArg (fun y : ℝ => f n x-y) hx)))

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicMildApproximation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A bounded collision window preserving the elastic symmetries -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem windowKernel_particleSwap (N : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    windowKernel N (particleSwap z) = windowKernel N z := by
  have hw : particleSwap z ∈ collisionWindow N ↔ z ∈ collisionWindow N := by
    change (‖z.1.2.2‖^2+‖z.1.2.1‖^2 ≤ N^2) ↔ _
    rw [add_comm]
    rfl
  have hk : collisionKernel z.1.2.2 z.1.2.1 z.2 = collisionKernel z.1.2.1 z.1.2.2 z.2 := by
    unfold collisionKernel normalComponent
    rw [show z.1.2.2-z.1.2.1 = -(z.1.2.1-z.1.2.2) by abel,inner_neg_left,abs_neg]
  by_cases hz : z ∈ collisionWindow N
  · rw [windowKernel,indicator_of_mem (hw.mpr hz),windowKernel,indicator_of_mem hz]
    exact hk
  · rw [windowKernel,indicator_of_notMem (fun h => hz (hw.mp h)),
      windowKernel,indicator_of_notMem hz]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # A symmetric bounded-rate approximation for global periodic construction -/
noncomputable section
open Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem pairRate_eq (N a b c d : ℝ) :
    pairRate N a b c d = N^2*a*b/(N+rateSum a b c d)^2 := by unfold pairRate; simp only [div_eq_mul_inv, ← inv_pow] <;> ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual symmetric regularized hard-sphere collision rates -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem regularizedPostRate_scatter (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPostRate N f (scatterTriple z) = regularizedPreRate N f z := by
  unfold regularizedPostRate
  rw [scatterTriple_involutive]

theorem regularizedPreRate_particleSwap (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPreRate N f (particleSwap z) = regularizedPreRate N f z := by
  unfold regularizedPreRate
  rw [windowKernel_particleSwap]
  change windowKernel N z * pairRate N (f (z.1.1,z.1.2.2)) (f (z.1.1,z.1.2.1))
    (f (z.1.1,scatterLeft z.1.2.2 z.1.2.1 z.2))
    (f (z.1.1,scatterRight z.1.2.2 z.1.2.1 z.2)) = _
  rw [scatterLeft_swap z.1.2.2 z.1.2.1 z.2,scatterRight_swap z.1.2.2 z.1.2.1 z.2]
  congr 1
  unfold pairRate rateSum
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform compact-velocity logarithmic bounds for positive regularization -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem maxwellian_le_center (v : Velocity) : maxwellian v ≤ maxwellian 0 := by
  have h0 : maxwellian 0 = (2*Real.pi)^(-(3/2:ℝ)) := by norm_num [maxwellian]
  rw [h0]
  have he : Real.exp (-‖v‖^2/2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖v‖])
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

theorem maxwellian_lower_on_ball {N : ℝ} (hN : 0 ≤ N) (v : Velocity) (hv : ‖v‖ ≤ N) :
    maxwellian 0*Real.exp (-N^2/2) ≤ maxwellian v := by
  have h0 : maxwellian 0 = (2*Real.pi)^(-(3/2:ℝ)) := by norm_num [maxwellian]
  rw [h0]
  unfold maxwellian
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hs := (sq_le_sq₀ (norm_nonneg _) hN).mpr hv
  linarith

theorem log_regularization_bound {N B δ a : ℝ} (hN : 0 ≤ N) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ a) (haB : a ≤ B)
    (v : Velocity) (hv : ‖v‖ ≤ N) :
    |Real.log ((a+δ*maxwellian v)/maxwellian v)| ≤
      |Real.log δ|+logRegularizationConstant N B := by
  have hm := maxwellian_pos v
  have hm0 : 0 < maxwellian 0*Real.exp (-N^2/2) :=
    mul_pos (maxwellian_pos 0) (Real.exp_pos _)
  have hl := maxwellian_lower_on_ball hN v hv
  have hu : 0 < B/(maxwellian 0*Real.exp (-N^2/2))+1 := by positivity
  have hlo : δ ≤ (a+δ*maxwellian v)/maxwellian v := by
    rw [le_div_iff₀ hm]
    linarith
  have hhi : (a+δ*maxwellian v)/maxwellian v ≤
      B/(maxwellian 0*Real.exp (-N^2/2))+1 := by
    calc
      _ = a/maxwellian v+δ := by field_simp
      _ ≤ B/(maxwellian 0*Real.exp (-N^2/2))+1 :=
        add_le_add (div_le_div₀ hB haB hm0 hl) hδ1
  have hloglo := Real.log_le_log hδ hlo
  have hloghi := Real.log_le_log (hδ.trans_le hlo) hhi
  unfold logRegularizationConstant
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log δ),abs_nonneg (Real.log (B/(maxwellian 0*Real.exp (-N^2/2))+1))]
  · linarith [le_abs_self (Real.log (B/(maxwellian 0*Real.exp (-N^2/2))+1)),abs_nonneg (Real.log δ)]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integral symmetries of the actual regularized collision rates -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem regularizedPostRate_particleSwap (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPostRate N f (particleSwap z) = regularizedPostRate N f z := by
  unfold regularizedPostRate
  rw [scatterTriple_particleSwap,regularizedPreRate_particleSwap]

theorem integral_regularizedPreRate_swap (μ : Measure X) [SFinite μ] (N : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPreRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*regularizedPreRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate N f z)
  simp only [regularizedPreRate_particleSwap] at h
  exact h.symm

theorem integral_regularizedPostRate_swap (μ : Measure X) [SFinite μ] (N : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.2)*regularizedPostRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (particleSwap_measurePreserving μ).integral_comp particleSwap.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z)
  simp only [regularizedPostRate_particleSwap] at h
  exact h.symm

theorem integral_regularizedPostRate_scatter (μ : Measure X) [SFinite μ] (N : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*regularizedPreRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z)
  simp only [regularizedPostRate_scatter] at h
  exact h.symm

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicFiniteMild
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The common pre/post multiplier in the conservative approximation -/
noncomputable section
open Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem attenuation_nonneg (N S : ℝ) : 0 ≤ attenuation N S :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem attenuation_le_one {N S : ℝ} (hN : 0 < N) (hS : 0 ≤ S) : attenuation N S ≤ 1 := by
  have hp : 0 < N+S := add_pos_of_pos_of_nonneg hN hS
  apply (div_le_one (sq_pos_of_pos hp)).mpr
  exact (sq_le_sq₀ hN.le hp.le).mpr (by linarith)

variable {X : Type*}

theorem rateMultiplier_bounds {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ rateMultiplier N f z ∧ rateMultiplier N f z ≤ 1 := by
  exact ⟨attenuation_nonneg _ _,attenuation_le_one hN
    (rateSum_nonneg (hf _) (hf _) (hf _) (hf _))⟩

theorem regularizedPreRate_factor (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPreRate N f z = windowKernel N z*rateMultiplier N f z*
      f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) := by
  unfold regularizedPreRate
  rw [pairRate_eq]
  unfold rateMultiplier attenuation
  ring

theorem regularizedPostRate_factor (N : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    regularizedPostRate N f z = windowKernel N z*rateMultiplier N f z*
      f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
      f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2) := by
  rw [regularizedPostRate_formula,pairRate_eq]
  unfold rateMultiplier attenuation rateSum
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrability of the bounded collision rates without a quadratic moment assumption -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem pairBall_compact (N : ℝ) : IsCompact (pairBall N) :=
  (isCompact_closedBall (0 : Velocity) N).prod (isCompact_closedBall (0 : Velocity) N)

omit [MeasurableSpace X] in
theorem regularizedPreRate_zero_of_outside {N : ℝ} (hN : 0 ≤ N)
    (f : X × Velocity → ℝ) {z : (X × (Velocity × Velocity)) × Sphere}
    (hz : z.1.2 ∉ pairBall N) : regularizedPreRate N f z = 0 := by
  have hw : z ∉ collisionWindow N := by
    intro h
    have hb := collisionWindow_bounds hN h
    apply hz
    simpa only [pairBall,Set.mem_prod,Metric.mem_closedBall,dist_zero_right] using hb
  simp only [regularizedPreRate,windowKernel,indicator_of_notMem hw,zero_mul]

theorem regularizedPreRate_integrable {N : ℝ} (hN : 0 < N) {μ : Measure X} [IsFiniteMeasure μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    Integrable (regularizedPreRate N f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hi : Integrable ((pairBall N).indicator (fun _ : Velocity × Velocity => 2*N^3))
      (volume : Measure (Velocity × Velocity)) :=
    (integrableOn_const (pairBall_compact N).measure_lt_top.ne).integrable_indicator
      (pairBall_compact N).measurableSet
  have hh := (hi.comp_snd μ).comp_fst sphereArea
  apply hh.mono' (regularizedPreRate_measurable N hfm).aestronglyMeasurable
  filter_upwards [] with z
  change ‖regularizedPreRate N f z‖ ≤ (pairBall N).indicator (fun _ => 2*N^3) z.1.2
  by_cases hz : z.1.2 ∈ pairBall N
  · rw [indicator_of_mem hz,Real.norm_of_nonneg (regularizedPreRate_bounds hN hf z).1]
    exact (regularizedPreRate_bounds hN hf z).2
  · rw [regularizedPreRate_zero_of_outside hN.le f hz,indicator_of_notMem hz,norm_zero]

theorem regularizedPostRate_integrable {N : ℝ} (hN : 0 < N) {μ : Measure X} [IsFiniteMeasure μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    Integrable (regularizedPostRate N f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (scatterTriple_measurePreserving μ).integrable_comp_of_integrable
    (regularizedPreRate_integrable hN hfm hf)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Compact velocity tests of the approximate collision rates are integrable -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem regularizedPreRate_test_integrable {N C : ℝ} (hN : 0 < N)
    {μ : Measure X} [IsFiniteMeasure μ] {f ψ : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hψm : Measurable ψ)
    (hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ C) :
    Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate N f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hi := (regularizedPreRate_integrable (μ := μ) hN hfm hf).norm.const_mul C
  apply hi.mono'
    ((hψm.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).mul
      (regularizedPreRate_measurable N hfm)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖ψ (z.1.1,z.1.2.1)*regularizedPreRate N f z‖ ≤ C*‖regularizedPreRate N f z‖
  by_cases hz : N < ‖z.1.2.1‖
  · rw [regularizedPreRate_zero_of_velocity hN.le f z hz,mul_zero,norm_zero,mul_zero]
  · rw [norm_mul,Real.norm_eq_abs (ψ _)]
    exact mul_le_mul_of_nonneg_right (hψ _ (le_of_not_gt hz)) (norm_nonneg _)

theorem regularizedPostRate_test_integrable {N C : ℝ} (hN : 0 < N)
    {μ : Measure X} [IsFiniteMeasure μ] {f ψ : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hψm : Measurable ψ)
    (hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ C) :
    Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hi := (regularizedPostRate_integrable (μ := μ) hN hfm hf).norm.const_mul C
  apply hi.mono'
    ((hψm.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).mul
      (regularizedPostRate_measurable N hfm)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z‖ ≤ C*‖regularizedPostRate N f z‖
  by_cases hz : N < ‖z.1.2.1‖
  · rw [regularizedPostRate_zero_of_velocity hN.le f z hz,mul_zero,norm_zero,mul_zero]
  · rw [norm_mul,Real.norm_eq_abs (ψ _)]
    exact mul_le_mul_of_nonneg_right (hψ _ (le_of_not_gt hz)) (norm_nonneg _)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The finite partner integral equals the full physical collision integral -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem regularizedPreRate_zero_of_partner {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) (hz : N < ‖z.1.2.2‖) :
    regularizedPreRate N f z = 0 := by
  rw [← regularizedPreRate_particleSwap N f z]
  exact regularizedPreRate_zero_of_velocity hN f _ hz

theorem regularizedPostRate_zero_of_partner {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) (hz : N < ‖z.1.2.2‖) :
    regularizedPostRate N f z = 0 := by
  rw [← regularizedPostRate_particleSwap N f z]
  exact regularizedPostRate_zero_of_velocity hN f _ hz

theorem fiberMeasure_eq_restrict (N : ℝ) : fiberMeasure N =
    ((volume : Measure Velocity).prod sphereArea).restrict (Metric.closedBall 0 N ×ˢ Set.univ) := by
  simpa only [fiberMeasure,Measure.restrict_univ] using
    (Measure.prod_restrict (μ := (volume : Measure Velocity)) (ν := sphereArea)
      (Metric.closedBall 0 N) Set.univ)

theorem loss_eq_full_integral {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ) (p : X × Velocity) :
    loss N f p = ∫ q, regularizedPreRate N f (collisionGrouping.symm (p,q))
      ∂((volume : Measure Velocity).prod sphereArea) := by
  rw [loss,fiberMeasure_eq_restrict,← integral_indicator (measurableSet_closedBall.prod MeasurableSet.univ)]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q ∈ Metric.closedBall 0 N ×ˢ (Set.univ : Set Sphere)
  · exact indicator_of_mem hq _
  · rw [indicator_of_notMem hq]
    symm
    apply regularizedPreRate_zero_of_partner hN
    change N < ‖q.1‖
    simpa only [Set.mem_prod,Set.mem_univ,and_true,Metric.mem_closedBall,dist_zero_right,not_le] using hq

theorem gain_eq_full_integral {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ) (p : X × Velocity) :
    gain N f p = ∫ q, regularizedPostRate N f (collisionGrouping.symm (p,q))
      ∂((volume : Measure Velocity).prod sphereArea) := by
  rw [gain,fiberMeasure_eq_restrict,← integral_indicator (measurableSet_closedBall.prod MeasurableSet.univ)]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q ∈ Metric.closedBall 0 N ×ˢ (Set.univ : Set Sphere)
  · exact indicator_of_mem hq _
  · rw [indicator_of_notMem hq]
    symm
    apply regularizedPostRate_zero_of_partner hN
    change N < ‖q.1‖
    simpa only [Set.mem_prod,Set.mem_univ,and_true,Metric.mem_closedBall,dist_zero_right,not_le] using hq

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The conservative weak identity for the bounded-rate approximation -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem integral_regularizedPostRate_scatter_right (μ : Measure X) [SFinite μ] (N : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, ψ (z.1.1,z.1.2.2)*regularizedPostRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*regularizedPreRate N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => ψ (z.1.1,z.1.2.2)*regularizedPostRate N f z)
  simp only [regularizedPostRate_scatter] at h
  exact h.symm

theorem regularized_weak_identity {μ : Measure X} [SFinite μ] (b : ℝ) (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) -
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    (1/2:ℝ) * ∫ z, collisionJump ψ z*regularizedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  have hr : Integrable (fun z => ψ (z.1.1,z.1.2.2)*regularizedPreRate b f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpre
    simp only [Function.comp_def,regularizedPreRate_particleSwap] at h
    exact h
  have hrpost : Integrable (fun z => ψ (z.1.1,z.1.2.2)*regularizedPostRate b f z) ν := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,regularizedPostRate_particleSwap] at h
    exact h
  have hl' : Integrable (fun z =>
      ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,regularizedPostRate_scatter] at h
    exact h
  have hr' : Integrable (fun z =>
      ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z) ν := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hrpost
    simp only [Function.comp_def,regularizedPostRate_scatter] at h
    exact h
  have he : (fun z => collisionJump ψ z*regularizedPreRate b f z) =
      (fun z => ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z)+
      (fun z => ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z)-
      (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z)-
      (fun z => ψ (z.1.1,z.1.2.2)*regularizedPreRate b f z) := by
    funext z
    dsimp [collisionJump]
    ring
  rw [he,integral_sub' ((hl'.add hr').sub hpre) hr,
    integral_sub' (hl'.add hr') hpre,integral_add' hl' hr']
  rw [← integral_regularizedPostRate_scatter,← integral_regularizedPostRate_scatter_right,
    ← integral_regularizedPostRate_swap,← integral_regularizedPreRate_swap]
  ring


end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Mass, momentum, and energy for the actual bounded-rate collision operator -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem regularized_test_marginals {N C : ℝ} (hN : 0 < N)
    {μ : Measure X} [IsFiniteMeasure μ] {f ψ : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hψm : Measurable ψ)
    (hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ C) :
    Integrable (fun p => ψ p*gain N f p) (μ.prod volume) ∧
    Integrable (fun p => ψ p*loss N f p) (μ.prod volume) ∧
    (∫ p, ψ p*gain N f p ∂μ.prod volume) =
      ∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate N f z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea ∧
    (∫ p, ψ p*loss N f p ∂μ.prod volume) =
      ∫ z, ψ (z.1.1,z.1.2.1)*regularizedPreRate N f z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have hp := collision_test_marginal (regularizedPostRate N f) ψ
    (regularizedPostRate_test_integrable (μ := μ) hN hfm hf hψm hψ)
  have hl := collision_test_marginal (regularizedPreRate N f) ψ
    (regularizedPreRate_test_integrable (μ := μ) hN hfm hf hψm hψ)
  simp only [← gain_eq_full_integral hN.le f] at hp
  simp only [← loss_eq_full_integral hN.le f] at hl
  exact ⟨hp.1,hl.1,hp.2,hl.2⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Symmetric collision production and its entropy sign -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem integral_jump_post (μ : Measure X) [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ) :
    (∫ z, collisionJump ψ z*regularizedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    -(∫ z, collisionJump ψ z*regularizedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := (scatterTriple_measurePreserving μ).integral_comp scatterTripleEquiv.measurableEmbedding
    (fun z => collisionJump ψ z*regularizedPostRate b f z)
  simp only [collisionJump_scatter,regularizedPostRate_scatter,neg_mul,integral_neg] at h
  exact h.symm

theorem collisionJump_integrable {μ : Measure X} [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (fun z => collisionJump ψ z*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    Integrable (fun z => collisionJump ψ z*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hr : Integrable (fun z => ψ (z.1.1,z.1.2.2)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpre
    simp only [Function.comp_def,regularizedPreRate_particleSwap] at h
    exact h
  have hrpost : Integrable (fun z => ψ (z.1.1,z.1.2.2)*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (particleSwap_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,regularizedPostRate_particleSwap] at h
    exact h
  have hl' : Integrable (fun z =>
      ψ (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hpost
    simp only [Function.comp_def,regularizedPostRate_scatter] at h
    exact h
  have hr' : Integrable (fun z =>
      ψ (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hrpost
    simp only [Function.comp_def,regularizedPostRate_scatter] at h
    exact h
  have hp : Integrable (fun z => collisionJump ψ z*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have h := ((hl'.add hr').sub hpre).sub hr
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    dsimp [collisionJump]
    ring
  refine ⟨hp,?_⟩
  have ht := (scatterTriple_measurePreserving μ).integrable_comp_of_integrable hp
  simp only [Function.comp_def,collisionJump_scatter,neg_mul] at ht
  convert ht.neg using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  simp only [Pi.neg_apply,neg_neg]
  rfl

theorem regularized_production_identity {μ : Measure X} [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) -
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    -(1/4:ℝ) * ∫ z, collisionJump ψ z*(regularizedPostRate b f z-regularizedPreRate b f z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  obtain ⟨hjpre,hjpost⟩ := collisionJump_integrable b f ψ hpre hpost
  simp_rw [mul_sub]
  rw [integral_sub hjpost hjpre,integral_jump_post]
  have h := regularized_weak_identity b f ψ hpre hpost
  linarith


end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Entropy sign for the symmetric bounded-rate collision operator -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem regularized_entropy_production_nonneg (b : ℝ) (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ collisionJump (fun p => Real.log (f p)) z*
      (regularizedPostRate b f z-regularizedPreRate b f z) := by
  let A := f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)
  let B := f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)
  have hA : 0 < A := mul_pos (hf _) (hf _)
  have hB : 0 < B := mul_pos (hf _) (hf _)
  have hsign : 0 ≤ (Real.log A-Real.log B)*(A-B) := by
    by_cases hBA : B ≤ A
    · exact mul_nonneg (sub_nonneg.mpr (Real.log_le_log hB hBA)) (sub_nonneg.mpr hBA)
    · have hAB : A ≤ B := le_of_lt (lt_of_not_ge hBA)
      exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (Real.log_le_log hA hAB)) (sub_nonpos.mpr hAB)
  rw [collisionJump_log_density f hf,Real.log_div hA.ne' hB.ne']
  rw [regularizedPostRate_factor,regularizedPreRate_factor]
  have he : windowKernel b z*rateMultiplier b f z*
      f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
      f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)-
      windowKernel b z*rateMultiplier b f z*f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2) =
      (windowKernel b z*rateMultiplier b f z)*(A-B) := by dsimp [A,B] <;> ring
  rw [he]
  have hw : 0 ≤ windowKernel b z := by
    by_cases hz : z ∈ collisionWindow b
    · rw [windowKernel,Set.indicator_of_mem hz]
      exact collisionKernel_nonneg _ _ _
    · rw [windowKernel,Set.indicator_of_notMem hz]
  have hk := mul_nonneg hw (attenuation_nonneg b
    (rateSum (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2))
      (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
      (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))))
  change 0 ≤ windowKernel b z*rateMultiplier b f z at hk
  convert mul_nonneg hk hsign using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [MeasurableSpace X] in
theorem regularized_relative_production_nonneg (N : ℝ) (f : X × Velocity → ℝ)
    (hf : ∀ p, 0 < f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ collisionJump (fun p => Real.log (f p/maxwellian p.2)) z*
      (regularizedPostRate N f z-regularizedPreRate N f z) := by
  rw [collisionJump_log_relative f hf]
  exact regularized_entropy_production_nonneg N f hf z

theorem regularized_relative_entropy_nonpositive {μ : Measure X} [IsFiniteMeasure μ]
    {N C : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hf : ∀ p, 0 < f p)
    (hlog : ∀ p, ‖p.2‖ ≤ N → |Real.log (f p/maxwellian p.2)| ≤ C) :
    (∫ p, Real.log (f p/maxwellian p.2)*gain N f p ∂μ.prod volume)-
      (∫ p, Real.log (f p/maxwellian p.2)*loss N f p ∂μ.prod volume) ≤ 0 := by
  have hψ : Measurable (fun p => Real.log (f p/maxwellian p.2)) := by
    have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by
      unfold maxwellian; fun_prop
    exact (hfm.div hm).log
  have hpre := regularizedPreRate_test_integrable (μ := μ) hN hfm
    (fun p => (hf p).le) hψ hlog
  have hpost := regularizedPostRate_test_integrable (μ := μ) hN hfm
    (fun p => (hf p).le) hψ hlog
  obtain ⟨_,_,hp,hl⟩ := regularized_test_marginals (μ := μ) hN hfm (fun p => (hf p).le) hψ hlog
  rw [hp,hl,regularized_production_identity N f (fun p => Real.log (f p/maxwellian p.2)) hpre hpost]
  have hn : 0 ≤ ∫ z, collisionJump (fun p => Real.log (f p/maxwellian p.2)) z*
      (regularizedPostRate N f z-regularizedPreRate N f z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea :=
    MeasureTheory.integral_nonneg (regularized_relative_production_nonneg N f hf)
  linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The bounded collision operator is stable under positive Gaussian shifts -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem gaussianShift_measurable (δ : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (gaussianShift δ f) := by
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  exact hf.add (hm.const_mul δ)

omit [MeasurableSpace X] in
theorem gaussianShift_pos {δ : ℝ} (hδ : 0 < δ) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) : 0 < gaussianShift δ f p :=
  add_pos_of_nonneg_of_pos (hf p) (mul_pos hδ (maxwellian_pos p.2))

omit [MeasurableSpace X] in
theorem gaussianShift_difference {δ : ℝ} (hδ : 0 ≤ δ) (f : X × Velocity → ℝ)
    (p : X × Velocity) : |f p-gaussianShift δ f p| ≤ δ*maxwellian 0 := by
  rw [gaussianShift,show f p-(f p+δ*maxwellian p.2) = -(δ*maxwellian p.2) by ring,
    abs_neg,abs_of_nonneg (mul_nonneg hδ (maxwellian_pos _).le)]
  exact mul_le_mul_of_nonneg_left (maxwellian_le_center p.2) hδ

theorem collisionOperator_support {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (p : X × Velocity) (hp : N < ‖p.2‖) : collisionOperator N f p = 0 := by
  rw [collisionOperator,gain_zero_of_velocity hN f p hp,loss_zero_of_velocity hN f p hp,sub_self]

theorem collisionOperator_gaussian_difference {N δ : ℝ} (hN : 0 < N) (hδ : 0 < δ)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (p : X × Velocity) :
    |collisionOperator N f p-collisionOperator N (gaussianShift δ f) p| ≤
      2*rateLipschitz N*δ*maxwellian 0 := by
  have hg := gaussianShift_measurable δ hfm
  have hgn := fun p => (gaussianShift_pos hδ hf p).le
  have ha := gain_difference hN hfm hg hf hgn (gaussianShift_difference hδ.le f) p
  have hb := loss_difference hN hfm hg hf hgn (gaussianShift_difference hδ.le f) p
  calc
    _ = |(gain N f p-gain N (gaussianShift δ f) p)-
          (loss N f p-loss N (gaussianShift δ f) p)| := by unfold collisionOperator; congr 1; ring
    _ ≤ |gain N f p-gain N (gaussianShift δ f) p|+
          |loss N f p-loss N (gaussianShift δ f) p| := abs_sub _ _
    _ ≤ _ := by linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrable endpoint entropy and removal of positive regularization -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem regularizedEntropy_parameter_continuous :
    Continuous (fun p : (ℝ × ℝ) × Velocity =>
      regularizedEntropy (maxwellian p.2) (maxwellian p.2) p.1.1 p.1.2) := by
  have hm : Continuous maxwellian := by unfold maxwellian; fun_prop
  have hl : Continuous (fun p : (ℝ × ℝ) × Velocity => Real.log (maxwellian p.2)) :=
    (hm.comp continuous_snd).log (fun p => (maxwellian_pos p.2).ne')
  unfold regularizedEntropy scalarRelativeEntropy
  fun_prop

theorem regularizedEntropy_uniform_bound (N B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ ∈ Icc (0:ℝ) 1, ∀ a ∈ Icc (0:ℝ) B, ∀ v : Velocity,
      ‖v‖ ≤ N → |regularizedEntropy (maxwellian v) (maxwellian v) δ a| ≤ C := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc.prod isCompact_Icc).prod (isCompact_closedBall (0:Velocity) N)).exists_bound_of_continuousOn
    regularizedEntropy_parameter_continuous.continuousOn
  refine ⟨|C|,abs_nonneg _,?_⟩
  intro δ hδ a ha v hv
  have h := hC ((δ,a),v) ⟨⟨hδ,ha⟩,by simpa only [Metric.mem_closedBall,dist_zero_right] using hv⟩
  have hb : |regularizedEntropy (maxwellian v) (maxwellian v) δ a| ≤ C := by
    simpa only [Real.norm_eq_abs] using h
  exact hb.trans (le_abs_self C)

variable {X : Type*} [MeasurableSpace X]

theorem scalarRelativeEntropy_measurable {m a : X → ℝ} (hm : Measurable m) (ha : Measurable a) :
    Measurable (fun p => scalarRelativeEntropy (m p) (a p)) :=
  ((Real.continuous_mul_log.measurable.comp ha).sub
    (ha.mul (measurable_const.add hm.log))).add hm

theorem regularizedEntropy_measurable (δ : ℝ) {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p)) := by
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  exact ((scalarRelativeEntropy_measurable hm (hfm.add (hm.const_mul δ))).sub
    (scalarRelativeEntropy_measurable hm (hm.const_mul δ))).add hm

theorem regularizedEntropy_integrable {μ : Measure X} [IsFiniteMeasure μ]
    {N B δ : ℝ} (hδ : δ ∈ Icc (0:ℝ) 1) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B)
    (hfs : ∀ p, N < ‖p.2‖ → f p = 0) :
    Integrable (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p))
      (μ.prod volume) := by
  obtain ⟨C,hC,hCb⟩ := regularizedEntropy_uniform_bound N B
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  have he : Integrable (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p)-maxwellian p.2)
      (μ.prod volume) := by
    apply bounded_velocity_integrable (N := N) ((regularizedEntropy_measurable δ hfm).sub hm)
      (A := C+maxwellian 0)
    · intro p
      change |regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p)-maxwellian p.2| ≤ C+maxwellian 0
      by_cases hp : N < ‖p.2‖
      · simp only [hfs p hp,regularizedEntropy,zero_add,sub_self,abs_zero]
        exact add_nonneg hC (maxwellian_pos 0).le
      · exact (abs_sub _ _).trans (add_le_add (hCb δ hδ (f p) ⟨hf p,hfb p⟩ p.2 (le_of_not_gt hp))
          ((abs_of_pos (maxwellian_pos _)).trans_le (maxwellian_le_center _)))
    · intro p hp
      simp [hfs p hp,regularizedEntropy]
  convert he.add (integrable_maxwellian.comp_snd μ) using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  simp only [Pi.add_apply,sub_add_cancel]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Vanishing Gaussian error in the actual approximate entropy production -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem entropy_error_bound {N B δ : ℝ} (hN : 0 < N) (hB : 0 ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B) (p : X × Velocity) :
    |Real.log (gaussianShift δ f p/maxwellian p.2)*
      (collisionOperator N f p-collisionOperator N (gaussianShift δ f) p)| ≤
      (|Real.log δ|+logRegularizationConstant N B)*(2*rateLipschitz N*δ*maxwellian 0) := by
  have hL : 0 ≤ rateLipschitz N := by unfold rateLipschitz; positivity
  have hC : 0 ≤ logRegularizationConstant N B := abs_nonneg _
  by_cases hp : N < ‖p.2‖
  · rw [collisionOperator_support hN.le f p hp,
      collisionOperator_support hN.le (gaussianShift δ f) p hp,sub_self,mul_zero,abs_zero]
    exact mul_nonneg (add_nonneg (abs_nonneg _) hC)
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hδ.le) (maxwellian_pos 0).le)
  · rw [abs_mul]
    exact mul_le_mul (log_regularization_bound hN.le hB hδ hδ1 (hf p) (hfb p) p.2
      (le_of_not_gt hp)) (collisionOperator_gaussian_difference hN hδ hfm hf p)
      (abs_nonneg _) (add_nonneg (abs_nonneg _) hC)

theorem entropy_error_integral {μ : Measure X} [IsFiniteMeasure μ]
    {N B δ : ℝ} (hN : 0 < N) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B) :
    |∫ p, Real.log (gaussianShift δ f p/maxwellian p.2)*
      (collisionOperator N f p-collisionOperator N (gaussianShift δ f) p) ∂μ.prod volume| ≤
      entropyErrorCoefficient μ N*δ*(|Real.log δ|+logRegularizationConstant N B) := by
  have he := bounded_velocity_integral_bound (μ := μ) (N := N)
    (entropy_error_bound hN hB hδ hδ1 hfm hf hfb)
    (fun p hp => by rw [collisionOperator_support hN.le f p hp,
      collisionOperator_support hN.le (gaussianShift δ f) p hp,sub_self,mul_zero])
  exact he.trans_eq (by unfold entropyErrorCoefficient; ring)

theorem entropy_error_tendsto (μ : Measure X) (N B : ℝ) :
    Tendsto (fun δ : ℝ => entropyErrorCoefficient μ N*δ*
      (|Real.log δ|+logRegularizationConstant N B)) (𝓝 0) (𝓝 0) := by
  have h := (tendsto_mul_affine_abs_log_zero (logRegularizationConstant N B) 1).const_mul
    (entropyErrorCoefficient μ N)
  convert h using 1
  · funext δ; ring
  · ring_nf

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing entropy regularization from supported bounded densities -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem entropyCompactMajorant_integrable (N C : ℝ) : Integrable (entropyCompactMajorant N C) := by
  exact ((integrableOn_const (isCompact_closedBall (0:Velocity) N).measure_lt_top.ne).integrable_indicator
    Metric.isClosed_closedBall.measurableSet).add integrable_maxwellian

omit [MeasurableSpace X] in
theorem regularizedEntropy_majorant {N B C : ℝ}
    (hCb : ∀ δ ∈ Icc (0:ℝ) 1, ∀ a ∈ Icc (0:ℝ) B, ∀ v : Velocity,
      ‖v‖ ≤ N → |regularizedEntropy (maxwellian v) (maxwellian v) δ a| ≤ C)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B)
    (hfs : ∀ p, N < ‖p.2‖ → f p = 0) {δ : ℝ} (hδ : δ ∈ Icc (0:ℝ) 1) (p : X × Velocity) :
    ‖regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p)‖ ≤
      entropyCompactMajorant N C p.2 := by
  rw [Real.norm_eq_abs]
  by_cases hp : p.2 ∈ Metric.closedBall 0 N
  · have hv : ‖p.2‖ ≤ N := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp
    exact (hCb δ hδ (f p) ⟨hf p,hfb p⟩ p.2 hv).trans (by
      unfold entropyCompactMajorant
      rw [indicator_of_mem hp]
      linarith [maxwellian_pos p.2])
  · have hv : N < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
    simp only [hfs p hv,regularizedEntropy,zero_add,sub_self,abs_of_pos (maxwellian_pos p.2),
      entropyCompactMajorant,indicator_of_notMem hp]
    exact le_rfl

theorem regularizedEntropy_integral_tendsto {μ : Measure X} [IsFiniteMeasure μ]
    {N B : ℝ} {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hfb : ∀ p, f p ≤ B) (hfs : ∀ p, N < ‖p.2‖ → f p = 0) :
    Tendsto (fun δ : ℝ => ∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f p) ∂μ.prod volume)
      (𝓝[>] 0) (𝓝 (∫ p, scalarRelativeEntropy (maxwellian p.2) (f p) ∂μ.prod volume)) := by
  obtain ⟨C,_,hCb⟩ := regularizedEntropy_uniform_bound N B
  apply tendsto_integral_filter_of_dominated_convergence (fun p => entropyCompactMajorant N C p.2)
  · exact Eventually.of_forall (fun δ => (regularizedEntropy_measurable δ hfm).aestronglyMeasurable)
  · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hδ
    exact Eventually.of_forall (regularizedEntropy_majorant hCb hf hfb hfs ⟨hδ.1.le,hδ.2.le⟩)
  · exact (entropyCompactMajorant_integrable N C).comp_snd μ
  · exact Eventually.of_forall (fun p =>
      (regularizedEntropy_tendsto (maxwellian p.2) (maxwellian p.2) (f p)).mono_left nhdsWithin_le_nhds)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicInitialEntropyLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Supported positive mild approximants and their finite entropy class -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem BoundedCutoffSolution.finiteEntropy {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hN : 0 ≤ N) (t : ℝ) :
    FiniteEntropyDatum (fun p => S.density (t,p)) := by
  obtain ⟨B,hB⟩ := S.bounded
  exact bounded_velocity_finiteEntropy hN
    (S.measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => S.nonnegative (t,p)) (fun p => hB (t,p)) (fun p => S.support (t,p))

theorem BoundedCutoffSolution.initial {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hT : 0 ≤ T) (p : Phase) : S.density (0,p) = f₀ p := by
  rw [S.mild]
  simp only [PositiveIntegral.value,PositiveIntegral.time,min_eq_right hT,max_self,
    mul_zero,Real.exp_zero,neg_zero,TorusFlight.flight_zero,one_mul,
    intervalIntegral.integral_same,add_zero]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual bounded initial approximations for the global construction -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialApproximation_le {N : ℝ} {f : Density}
    (hf : ∀ p, 0 ≤ f p) (p : Phase) : initialApproximation N f p ≤ f p := by
  unfold initialApproximation
  split_ifs
  · rw [max_eq_right (hf p)]
    exact min_le_right _ _
  · exact hf p

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Initial entropy bounds independent of the collision regularization -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialApproximation_entropy_le {N : ℝ} (hN : 1 ≤ N) {f : Density}
    (hf : ∀ p, 0 ≤ f p) (p : Phase) :
    entropyMoment (initialApproximation N f) p ≤ entropyMoment f p := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  by_cases hv : ‖p.2‖ ≤ N
  · by_cases hfN : f p ≤ N
    · simp only [entropyMoment,initialApproximation,hv,ite_true, if_true,max_eq_right (hf p),min_eq_right hfN]
      exact le_rfl
    · have hNf : N ≤ f p := (lt_of_not_ge hfN).le
      have hfone : 1 ≤ f p := hN.trans hNf
      have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
      have hlogf : 0 ≤ Real.log (f p) := Real.log_nonneg hfone
      have hlogs : Real.log N ≤ Real.log (f p) := Real.log_le_log hN0 hNf
      simp only [entropyMoment,initialApproximation,hv,ite_true, if_true,max_eq_right (hf p),min_eq_left hNf,
        abs_of_nonneg hlogN,abs_of_nonneg hlogf]
      exact mul_le_mul hNf (by linarith) (by positivity) (hf p)
  · simp only [entropyMoment,initialApproximation,hv,ite_false, if_false,zero_mul]
    exact mul_nonneg (hf p) (by positivity)

theorem initialApproximation_finiteEntropy {N : ℝ} (hN : 0 ≤ N) {f : Density}
    (hf : Measurable f) : FiniteEntropyDatum (initialApproximation N f) :=
  bounded_velocity_finiteEntropy hN (initialApproximation_measurable N hf)
    (fun p => (initialApproximation_bounds hN f p).1)
    (fun p => (initialApproximation_bounds hN f p).2) (initialApproximation_support N f)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong L1 and entropy convergence of the bounded initial approximations -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialApproximation_sequence_eventually_eq {f : Density} (hf : ∀ p, 0 ≤ f p) (p : Phase) :
    (fun n : ℕ => initialApproximation ((n:ℝ)+1) f p) =ᶠ[atTop] fun _ => f p := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n : ℕ, (n:ℝ) ≤ (n:ℝ)+1) tendsto_natCast_atTop_atTop
  filter_upwards [hn.eventually (eventually_ge_atTop (max ‖p.2‖ (f p)))] with n hn
  have hv : ‖p.2‖ ≤ (n:ℝ)+1 := (le_max_left _ _).trans hn
  have hfn : f p ≤ (n:ℝ)+1 := (le_max_right _ _).trans hn
  simp [initialApproximation,hv,max_eq_right (hf p),min_eq_right hfn]

theorem initialApproximation_L1_tendsto {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable f) :
    Tendsto (fun n : ℕ => ∫ p, |initialApproximation ((n:ℝ)+1) f p-f p|) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (F := fun n p => |initialApproximation ((n:ℝ)+1) f p-f p|)
    (f := fun _ => (0:ℝ)) f
    (fun n => ((initialApproximation_measurable ((n:ℝ)+1) hfm).sub hfm).abs.aestronglyMeasurable) hi
    (fun n => Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_of_nonneg (abs_nonneg _),abs_of_nonpos (sub_nonpos.mpr (initialApproximation_le hf p))]
      have hn := (initialApproximation_bounds (by positivity : 0 ≤ (n:ℝ)+1) f p).1
      linarith))
    (Filter.Eventually.of_forall (fun p => by
      apply tendsto_const_nhds.congr'
      filter_upwards [initialApproximation_sequence_eventually_eq hf p] with n hn
      rw [hn,sub_self,abs_zero]))
  simpa only [integral_zero] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong initial approximations in the time-extended local phase measure -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem initialApproximation_norm_tendsto {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable f) :
    Tendsto (fun n : ℕ => eLpNorm (initialApproximation ((n:ℝ)+1) f-f) 1 volume) atTop (𝓝 0) := by
  have hAi (n : ℕ) : Integrable (initialApproximation ((n:ℝ)+1) f) :=
    hi.mono' (initialApproximation_measurable ((n:ℝ)+1) hfm).aestronglyMeasurable
      (ae_of_all _ (fun p => by
        rw [Real.norm_of_nonneg (initialApproximation_bounds (N := (n:ℝ)+1) (by positivity) f p).1]
        exact initialApproximation_le hf p))
  have he (n : ℕ) : eLpNorm (initialApproximation ((n:ℝ)+1) f-f) 1 volume =
      ENNReal.ofReal (∫ p, |initialApproximation ((n:ℝ)+1) f p-f p|) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hAi n).sub hi)]
    rfl
  simp_rw [he]
  simpa only [Function.comp_def,ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp (initialApproximation_L1_tendsto hfm hf hi)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform relative entropy of the actual initial truncations -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialEntropyCoefficient_nonneg : 0 ≤ initialEntropyCoefficient := by
  unfold initialEntropyCoefficient
  positivity

theorem relativeEntropy_density_bound {f : Density} (hf : ∀ p, 0 ≤ f p) (p : Phase) :
    scalarRelativeEntropy (maxwellian p.2) (f p) ≤
      initialEntropyCoefficient*entropyMoment f p+maxwellian p.2 := by
  let c := |1-(3/2:ℝ)*Real.log (2*Real.pi)|
  have hc : 0 ≤ c := abs_nonneg _
  have hn := hf p
  have hE : 0 ≤ ‖p.2‖^2*f p := mul_nonneg (sq_nonneg _) (hf p)
  have hA : 0 ≤ f p*|Real.log (f p)| := mul_nonneg (hf p) (abs_nonneg _)
  have hlog := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (f p))) (hf p)
  have hcoeff : ((3/2:ℝ)*Real.log (2*Real.pi)-1)*f p ≤ c*f p := by
    apply mul_le_mul_of_nonneg_right _ (hf p)
    dsimp [c]
    linarith [neg_abs_le (1-(3/2:ℝ)*Real.log (2*Real.pi))]
  have h1 := mul_nonneg hc hE
  have h2 := mul_nonneg hc hA
  unfold scalarRelativeEntropy initialEntropyCoefficient entropyMoment
  rw [log_maxwellian]
  dsimp only [c] at hcoeff h1 h2
  nlinarith

theorem initialApproximation_relativeEntropy_le {N : ℝ} (hN : 1 ≤ N) {f : Density}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    relativeEntropy (initialApproximation N f) ≤
      initialEntropyCoefficient*(∫ p, entropyMoment f p)+(∫ p : Phase, maxwellian p.2) := by
  have hg := initialApproximation_finiteEntropy (zero_le_one.trans hN) hfm
  have hgn := fun p => (initialApproximation_bounds (zero_le_one.trans hN) f p).1
  have hH := hg.integrable_relativeEntropy
  have hmajor := (hi.const_mul initialEntropyCoefficient).add integrable_maxwellian_phase
  have hineq (p : Phase) : scalarRelativeEntropy (maxwellian p.2) (initialApproximation N f p) ≤
      initialEntropyCoefficient*entropyMoment f p+maxwellian p.2 :=
    (relativeEntropy_density_bound hgn p).trans
      (add_le_add (mul_le_mul_of_nonneg_left (initialApproximation_entropy_le hN hf p)
        initialEntropyCoefficient_nonneg) le_rfl)
  have h := integral_mono hH hmajor (fun p => by
    rw [← scalarRelativeEntropy_eq (maxwellian_pos p.2)]
    exact hineq p)
  rw [integral_add' (hi.const_mul initialEntropyCoefficient) integrable_maxwellian_phase,
    integral_const_mul] at h
  exact h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Measurable spacetime form of the bounded positive collision source -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem kineticSource_eq (N : ℝ) (F : ℝ × Phase → ℝ) (z : ℝ × Phase) :
    kineticSource N F z = positiveSource N (fun p => F (z.1,p)) z.2 := rfl

theorem kineticSource_measurable (N : ℝ) {F : ℝ × Phase → ℝ} (hF : Measurable F) :
    Measurable (kineticSource N F) := by
  have hm : Measurable (fun p : (ℝ × Position) × Velocity => F (p.1.1,(p.1.2,p.2))) :=
    hF.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact (positiveSource_measurable N hm).comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The exact characteristic equation of the supported periodic approximants -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.source_measurable (S : BoundedCutoffSolution N T f₀) :
    Measurable S.source := by
  have he : S.source = kineticSource N S.density := by
    funext z
    exact (kineticSource_eq N S.density z).symm
  rw [he]
  exact kineticSource_measurable N S.measurable

theorem BoundedCutoffSolution.source_bounded (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |S.source z| ≤ C := by
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  have hC : 0 ≤ gainBound N := by unfold gainBound; positivity
  have hL : 0 ≤ lossBound N := by unfold lossBound; positivity
  refine ⟨gainBound N+lossBound N*B,by positivity,?_⟩
  intro z
  have h := positiveSource_bounds hN
    (S.measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => S.nonnegative (z.1,p)) (fun p => hB (z.1,p)) z.2
  exact (abs_of_nonneg h.1).trans_le h.2

theorem BoundedCutoffSolution.source_path_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (p : Phase) (t : ℝ) :
    IntervalIntegrable (fun r => S.source (r,TorusFlight.flight r p)) volume 0 t := by
  obtain ⟨C,_,hC⟩ := S.source_bounded hN
  apply (intervalIntegrable_const (c := C)).mono_fun'
  · exact (S.source_measurable.comp (measurable_id.prodMk
      (TorusFlight.measurable_flight.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun r => by simpa only [Real.norm_eq_abs] using hC (r,TorusFlight.flight r p))

theorem BoundedCutoffSolution.along_eq_damped (S : BoundedCutoffSolution N T f₀)
    {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    S.density (t,TorusFlight.flight t p) = TransportPrimitive.damped (lossBound N) (f₀ p)
      (fun r => S.source (r,TorusFlight.flight r p)) t := by
  rw [S.mild,TransportPrimitive.damped_eq]
  change PositiveIntegral.value T (lossBound N) TorusFlight.flight f₀ S.source
    (t,TorusFlight.flight t p) = _
  unfold PositiveIntegral.value
  have htt : PositiveIntegral.time T t = t := by
    unfold PositiveIntegral.time
    rw [min_eq_right ht.2,max_eq_right ht.1]
  rw [htt,TorusFlight.flight_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [TorusFlight.flight_add,sub_add_cancel]

theorem BoundedCutoffSolution.tested_path (S : BoundedCutoffSolution N T f₀) (hN : 0 < N)
    {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) (χ χ' : ℝ → ℝ)
    (hc : ContinuousOn χ (Icc 0 t)) (hc' : ContinuousOn χ' (Icc 0 t))
    (hd : ∀ r ∈ Icc 0 t, HasDerivAt χ (χ' r) r) :
    (∫ r in 0..t, χ' r*S.density (r,TorusFlight.flight r p)+
      χ r*(S.source (r,TorusFlight.flight r p)-lossBound N*S.density (r,TorusFlight.flight r p))) =
      χ t*S.density (t,TorusFlight.flight t p)-χ 0*f₀ p := by
  have h := TransportPrimitive.damped_integration_by_parts (L := lossBound N) (c := f₀ p) ht.1
    (S.source_path_integrable hN p t) hc hc' hd
  rw [← S.along_eq_damped ht p] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro r hr
  have hrT : r ∈ Icc 0 T := by
    rw [uIcc_of_le ht.1] at hr
    exact ⟨hr.1,hr.2.trans ht.2⟩
  dsimp only
  rw [S.along_eq_damped hrT p]

theorem BoundedCutoffSolution.characteristic_integral (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    S.density (t,TorusFlight.flight t p) = f₀ p+
      ∫ r in 0..t, S.source (r,TorusFlight.flight r p)-lossBound N*S.density (r,TorusFlight.flight r p) := by
  have h := S.tested_path hN ht p (fun _ => 1) (fun _ => 0) continuousOn_const continuousOn_const
    (fun r _ => hasDerivAt_const r (1:ℝ))
  simp only [zero_mul,zero_add,one_mul] at h
  linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # An entropy-production bound for nonnegative approximate densities -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem collisionOperator_test_integrable {μ : Measure X} [IsFiniteMeasure μ]
    {N C : ℝ} (hN : 0 < N) {f ψ : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hψm : Measurable ψ)
    (hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ C) :
    Integrable (fun p => ψ p*collisionOperator N f p) (μ.prod volume) := by
  obtain ⟨hg,hl,_,_⟩ := regularized_test_marginals (μ := μ) hN hfm hf hψm hψ
  convert hg.sub hl using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  simp only [collisionOperator,mul_sub,Pi.sub_apply]

theorem nonnegative_entropy_production_bound {μ : Measure X} [IsFiniteMeasure μ]
    {N B δ : ℝ} (hN : 0 < N) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B) :
    (∫ p, Real.log (gaussianShift δ f p/maxwellian p.2)*collisionOperator N f p ∂μ.prod volume) ≤
      entropyErrorCoefficient μ N*δ*(|Real.log δ|+logRegularizationConstant N B) := by
  let g := gaussianShift δ f
  let ψ := fun p : X × Velocity => Real.log (g p/maxwellian p.2)
  have hgm : Measurable g := gaussianShift_measurable δ hfm
  have hgp : ∀ p, 0 < g p := gaussianShift_pos hδ hf
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hψm : Measurable ψ := (hgm.div hm).log
  have hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ |Real.log δ|+logRegularizationConstant N B :=
    fun p hp => log_regularization_bound hN.le hB hδ hδ1 (hf p) (hfb p) p.2 hp
  have hif := collisionOperator_test_integrable (μ := μ) hN hfm hf hψm hψ
  have hig := collisionOperator_test_integrable (μ := μ) hN hgm (fun p => (hgp p).le) hψm hψ
  obtain ⟨hg,hl,_,_⟩ := regularized_test_marginals (μ := μ) hN hgm (fun p => (hgp p).le) hψm hψ
  have hn := regularized_relative_entropy_nonpositive (μ := μ) hN hgm hgp hψ
  rw [← integral_sub hg hl] at hn
  simp only [← mul_sub] at hn
  have he := entropy_error_integral (μ := μ) hN hB hδ hδ1 hfm hf hfb
  have heq : (fun p => ψ p*(collisionOperator N f p-collisionOperator N g p)) =
      (fun p => ψ p*collisionOperator N f p)-(fun p => ψ p*collisionOperator N g p) := by
    funext p
    simp only [Pi.sub_apply,mul_sub]
  change |∫ p, ψ p*(collisionOperator N f p-collisionOperator N g p) ∂μ.prod volume| ≤ _ at he
  rw [heq,integral_sub' hif hig] at he
  change (∫ p, ψ p*collisionOperator N g p ∂μ.prod volume) ≤ 0 at hn
  have ha := (le_abs_self ((∫ p, ψ p*collisionOperator N f p ∂μ.prod volume)-
    (∫ p, ψ p*collisionOperator N g p ∂μ.prod volume))).trans he
  change (∫ p, ψ p*collisionOperator N f p ∂μ.prod volume) ≤ _
  linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The entropy chain rule for the actual supported cutoff solution -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.collision_path_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (p : Phase) (t : ℝ) :
    IntervalIntegrable (fun r => S.source (r,TorusFlight.flight r p)-
      lossBound N*S.density (r,TorusFlight.flight r p)) volume 0 t := by
  obtain ⟨B,hB⟩ := S.bounded
  have hi : IntervalIntegrable (fun r => S.density (r,TorusFlight.flight r p)) volume 0 t := by
    apply (intervalIntegrable_const (c := B)).mono_fun'
    · exact (S.measurable.comp (measurable_id.prodMk
        (TorusFlight.measurable_flight.comp (measurable_id.prodMk measurable_const)))).aestronglyMeasurable
    · filter_upwards [] with r
      rw [Real.norm_of_nonneg (S.nonnegative _)]
      exact hB _
  exact (S.source_path_integrable hN p t).sub (hi.const_mul (lossBound N))

theorem BoundedCutoffSolution.entropy_path_balance (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t δ : ℝ} (ht : t ∈ Icc 0 T) (hδ : 0 < δ) (p : Phase) :
    (∫ r in 0..t, Real.log ((S.density (r,TorusFlight.flight r p)+δ*maxwellian p.2)/maxwellian p.2)*
      (S.source (r,TorusFlight.flight r p)-lossBound N*S.density (r,TorusFlight.flight r p))) =
      regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,TorusFlight.flight t p))-
      regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p) := by
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  have he (r : ℝ) (hr : r ∈ uIcc 0 t) :
      f₀ p+(∫ s in 0..r, S.source (s,TorusFlight.flight s p)-
        lossBound N*S.density (s,TorusFlight.flight s p)) = S.density (r,TorusFlight.flight r p) := by
    rw [uIcc_of_le ht.1] at hr
    exact (S.characteristic_integral hN ⟨hr.1,hr.2.trans ht.2⟩ p).symm
  have h := regularizedEntropy_integral_path (maxwellian_pos p.2) (maxwellian_pos p.2) hδ hB0
    (S.collision_path_integrable hN p t)
    (fun r hr => (he r hr).symm ▸ S.nonnegative (r,TorusFlight.flight r p))
    (fun r hr => (he r hr).symm ▸ hB (r,TorusFlight.flight r p))
  rw [he t right_mem_uIcc] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro r hr
  dsimp only
  rw [he r hr]

end BoltzmannNonuniqueness.PeriodicApproximation

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

/-! # One weighted weak limit gives a compatible limit on all finite time windows -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]

theorem weak_localize_time {f : ℕ → ℝ × X → ℝ} {g : ℝ × X → ℝ}
    (h : Published.WeakL1Converges (finiteTimeMeasure.prod ν) f g)
    {T : ℝ} (hT : 0 ≤ T) :
    Published.WeakL1Converges ((volume.restrict (Icc 0 T)).prod ν) f g := by
  have hw : Measurable (fun p : ℝ × X => windowInverseWeight T p.1) :=
    (windowInverseWeight_measurable T).comp measurable_fst
  have ht := h.withDensity_bounded hw
    (fun p => windowInverseWeight_nonneg T p.1)
    ⟨Real.exp (T^2),fun p => windowInverseWeight_bound hT p.1⟩
  rw [← prod_withDensity_left (windowInverseWeight_measurable T).ennreal_ofReal,
    finiteTimeMeasure_reweight] at ht
  exact ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_MeasurableResolvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurability of a parameter-dependent interval primitive -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.TransportPrimitive
variable {P : Type*} [MeasurableSpace P]

theorem measurable_interval_primitive {f : ℝ × P → ℝ} (hf : Measurable f) :
    Measurable (fun z : ℝ × P => ∫ s in 0..z.1, f (s,z.2)) := by
  have hm : Measurable (fun q : (ℝ × P) × ℝ => f (q.2,q.1.2)) :=
    hf.comp (measurable_snd.prodMk measurable_fst.snd)
  have hplus : Measurable (fun q : (ℝ × P) × ℝ =>
      if 0 < q.2 ∧ q.2 ≤ q.1.1 then f (q.2,q.1.2) else 0) :=
    hm.ite ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst)) measurable_const
  have hminus : Measurable (fun q : (ℝ × P) × ℝ =>
      if q.1.1 < q.2 ∧ q.2 ≤ 0 then f (q.2,q.1.2) else 0) :=
    hm.ite ((measurableSet_lt measurable_fst.fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) measurable_const
  have hp := (hplus.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hn := (hminus.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hp.sub hn using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  change (∫ s in Ioc 0 z.1, f (s,z.2))-(∫ s in Ioc z.1 0, f (s,z.2)) = _
  rw [← integral_indicator measurableSet_Ioc,← integral_indicator measurableSet_Ioc]
  simp only [Set.indicator,mem_Ioc,Pi.sub_apply]

end BoltzmannNonuniqueness.TransportPrimitive

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

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicMomentEntropy
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrable undamped sources of the actual periodic cutoff solutions -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.collision_eq (S : BoundedCutoffSolution N T f₀) (z : ℝ × Phase) :
    S.collision z = gain N (fun p => S.density (z.1,p)) z.2-
      loss N (fun p => S.density (z.1,p)) z.2 := by
  unfold collision source positiveSource
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The approximate entropy-production estimate in physical coordinates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.kinetic_collision (S : BoundedCutoffSolution N T f₀)
    (p : (ℝ × Position) × Velocity) :
    collisionOperator N (fun p : (ℝ × Position) × Velocity => S.density (p.1.1,(p.1.2,p.2))) p =
      S.collision (p.1.1,(p.1.2,p.2)) := by
  rw [S.collision_eq]
  rfl

theorem BoundedCutoffSolution.log_collision_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {B δ : ℝ} (hB : 0 ≤ B) (hSb : ∀ z, S.density z ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) :
    Integrable (fun z : ℝ × Phase => Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z)
      ((volume.restrict (Icc 0 t)).prod volume) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 t)).prod volume
  let f : (ℝ × Position) × Velocity → ℝ := fun p => S.density (p.1.1,(p.1.2,p.2))
  have hfm : Measurable f := S.measurable.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hm : Measurable (fun p : (ℝ × Position) × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hψ := ((gaussianShift_measurable δ hfm).div hm).log
  have hi := collisionOperator_test_integrable (μ := μ) hN hfm
    (fun p => S.nonnegative (p.1.1,(p.1.2,p.2))) hψ
    (fun p hp => log_regularization_bound hN.le hB hδ hδ1 (S.nonnegative _)
      (hSb _) p.2 hp)
  dsimp only [f] at hi
  simp only [S.kinetic_collision] at hi
  have hr := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 t))).symm.integrable_comp_of_integrable hi
  change Integrable (fun z : ℝ × Phase => Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z)
    ((volume.restrict (Icc 0 t)).prod volume) at hr
  exact hr

theorem BoundedCutoffSolution.entropy_production_bound (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {B δ : ℝ} (hB : 0 ≤ B) (hSb : ∀ z, S.density z ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) :
    (∫ z : ℝ × Phase, Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z
      ∂(volume.restrict (Icc 0 t)).prod volume) ≤
      entropyErrorCoefficient ((volume.restrict (Icc 0 t)).prod (volume : Measure Position)) N*
        δ*(|Real.log δ|+logRegularizationConstant N B) := by
  let f : (ℝ × Position) × Velocity → ℝ := fun p => S.density (p.1.1,(p.1.2,p.2))
  have hfm : Measurable f := S.measurable.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have h := nonnegative_entropy_production_bound
    (μ := (volume.restrict (Icc 0 t)).prod (volume : Measure Position)) hN hB hδ hδ1 hfm
    (fun p => S.nonnegative (p.1.1,(p.1.2,p.2))) (fun p => hSb _)
  have he := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 t))).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun z : ℝ × Phase => Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z)
  rw [← he]
  dsimp only [f] at h
  simp only [S.kinetic_collision,gaussianShift] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrating the entropy balance of the constructed cutoff trajectories -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.endpoint_entropy_integrable (S : BoundedCutoffSolution N T f₀)
    {δ : ℝ} (hδ : δ ∈ Icc (0:ℝ) 1) (t : ℝ) :
    Integrable (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p))) := by
  obtain ⟨B,hB⟩ := S.bounded
  rw [Measure.volume_eq_prod]
  exact regularizedEntropy_integrable hδ
    (S.measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => S.nonnegative (t,p)) (fun p => hB (t,p)) (fun p => S.support (t,p))

theorem BoundedCutoffSolution.integrated_entropy_balance (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) {t δ : ℝ} (ht : t ∈ Icc 0 T)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p)))-
      (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)) =
    ∫ z : ℝ × Phase, Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z
      ∂(volume.restrict (Icc 0 t)).prod volume := by
  obtain ⟨B,hSb⟩ := S.bounded
  have hB : 0 ≤ B := (S.nonnegative (0,0)).trans (hSb (0,0))
  have hi := S.log_collision_integrable hN hB hSb hδ hδ1 t
  have halong := (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 t))).integrable_comp_of_integrable hi
  have htE := S.endpoint_entropy_integrable ⟨hδ.le,hδ1⟩ t
  have htEa := (TorusFlight.flight_measurePreserving t).integrable_comp_of_integrable htE
  have h0E : Integrable (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)) := by
    simpa only [S.initial hT] using S.endpoint_entropy_integrable ⟨hδ.le,hδ1⟩ 0
  have hpath (p : Phase) :
      regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,TorusFlight.flight t p))-
        regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p) =
      ∫ r, Real.log ((S.density (r,TorusFlight.flight r p)+δ*maxwellian p.2)/maxwellian p.2)*
        S.collision (r,TorusFlight.flight r p) ∂volume.restrict (Icc 0 t) := by
    have h := (S.entropy_path_balance hN ht hδ p).symm
    rw [intervalIntegral.integral_of_le ht.1,← integral_Icc_eq_integral_Ioc] at h
    exact h
  calc
    _ = (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ
          (S.density (t,TorusFlight.flight t p)))-
        (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)) := by
      rw [← TorusFlight.integral_flight
        (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p))) t]
      rfl
    _ = ∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ
          (S.density (t,TorusFlight.flight t p))-
        regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p) :=
      (integral_sub htEa h0E).symm
    _ = ∫ p, ∫ r, Real.log ((S.density (r,TorusFlight.flight r p)+δ*maxwellian p.2)/maxwellian p.2)*
        S.collision (r,TorusFlight.flight r p) ∂volume.restrict (Icc 0 t) :=
      integral_congr_ae (Filter.Eventually.of_forall hpath)
    _ = ∫ z : ℝ × Phase, Real.log ((S.density (z.1,TorusFlight.flight z.1 z.2)+δ*maxwellian z.2.2)/maxwellian z.2.2)*
        S.collision (z.1,TorusFlight.flight z.1 z.2) ∂(volume.restrict (Icc 0 t)).prod volume :=
      (integral_prod_symm _ halong).symm
    _ = _ := TorusFlight.integral_along hi

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual finite cutoff solutions satisfy a cutoff-independent entropy bound -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.endpoint_entropy_tendsto (S : BoundedCutoffSolution N T f₀) (t : ℝ) :
    Tendsto (fun δ : ℝ => ∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p)))
      (𝓝[>] 0) (𝓝 (∫ p, scalarRelativeEntropy (maxwellian p.2) (S.density (t,p)))) := by
  obtain ⟨B,hB⟩ := S.bounded
  simp only [Measure.volume_eq_prod]
  exact regularizedEntropy_integral_tendsto
    (S.measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => S.nonnegative (t,p)) (fun p => hB (t,p)) (fun p => S.support (t,p))

theorem BoundedCutoffSolution.entropy_inequality (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p, scalarRelativeEntropy (maxwellian p.2) (S.density (t,p))) ≤
      ∫ p, scalarRelativeEntropy (maxwellian p.2) (f₀ p) := by
  obtain ⟨B,hSb⟩ := S.bounded
  have hB : 0 ≤ B := (S.nonnegative (0,0)).trans (hSb (0,0))
  have h0 := S.endpoint_entropy_tendsto 0
  simp only [S.initial hT] at h0
  have hL := (S.endpoint_entropy_tendsto t).sub h0
  have hR := (entropy_error_tendsto
    ((volume.restrict (Icc 0 t)).prod (volume : Measure Position)) N B).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have hle : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p)))-
        (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)) ≤
      entropyErrorCoefficient ((volume.restrict (Icc 0 t)).prod (volume : Measure Position)) N*
        δ*(|Real.log δ|+logRegularizationConstant N B) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hδ
    rw [S.integrated_entropy_balance hN hT ht hδ.1 hδ.2.le]
    exact S.entropy_production_bound hN hB hSb hδ.1 hδ.2.le t
  have h := le_of_tendsto_of_tendsto hL hR hle
  linarith

theorem BoundedCutoffSolution.relativeEntropy_le (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    relativeEntropy (fun p => S.density (t,p)) ≤ relativeEntropy f₀ := by
  have h := S.entropy_inequality hN hT ht
  simpa only [relativeEntropy,scalarRelativeEntropy_eq (maxwellian_pos _)] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Retained dissipation of the actual finite periodic solutions -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.kineticProfile_measurable (S : BoundedCutoffSolution N T f₀) :
    Measurable S.kineticProfile :=
  S.measurable.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # One entropy and moment budget for all finite regularized approximants -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem BoundedCutoffSolution.uniform_entropyMoment {N T : ℝ} {f : Density}
    (S : BoundedCutoffSolution N T (initialApproximation N f))
    (hN : 1 ≤ N) (hT : 0 ≤ T) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p, entropyMoment (fun p => S.density (t,p)) p) ≤ approximationEntropyBudget f := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hE := entropyMoment_integral_control (S.finiteEntropy hN0.le t)
  have hR := (S.relativeEntropy_le hN0 hT ht).trans
    (initialApproximation_relativeEntropy_le hN hfm hf hi)
  have hC : 0 ≤ 1+4*entropyMomentCoefficient := by
    have := entropyMomentCoefficient_nonneg
    positivity
  exact hE.trans (by
    change (1+4*entropyMomentCoefficient)*relativeEntropy (fun p => S.density (t,p))+_+_ ≤
      (1+4*entropyMomentCoefficient)*initialEntropyBudget f+_+_
    gcongr
    exact hR)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # One actual cutoff solution sequence with growing horizons and uniform entropy -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem clippedTime_fixed {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    PositiveIntegral.time T (PositiveIntegral.time T t) = PositiveIntegral.time T t := by
  have ht := PositiveIntegral.time_bounds hT t
  change max 0 (min T (PositiveIntegral.time T t)) = PositiveIntegral.time T t
  rw [min_eq_right ht.2,max_eq_right ht.1]

theorem BoundedCutoffSolution.density_clipped {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hT : 0 ≤ T) (t : ℝ) (p : Phase) :
    S.density (t,p) = S.density (PositiveIntegral.time T t,p) := by
  rw [S.mild (t,p),S.mild (PositiveIntegral.time T t,p)]
  simp only [PositiveIntegral.value,clippedTime_fixed hT]

theorem BoundedCutoffSolution.uniform_entropyMoment_all_times {N T : ℝ} {f : Density}
    (S : BoundedCutoffSolution N T (initialApproximation N f))
    (hN : 1 ≤ N) (hT : 0 ≤ T) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) (t : ℝ) :
    (∫ p, entropyMoment (fun p => S.density (t,p)) p) ≤ approximationEntropyBudget f := by
  have he : (fun p => S.density (t,p)) = (fun p => S.density (PositiveIntegral.time T t,p)) :=
    funext (S.density_clipped hT t)
  rw [he]
  exact S.uniform_entropyMoment hN hT hfm hf hi (PositiveIntegral.time_bounds hT t)

theorem approximatingSolution_entropy (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (n : ℕ) (t : ℝ) :
    (∫ p, entropyMoment (fun p => (approximatingSolution f hfm n).density (t,p)) p) ≤
      approximationEntropyBudget f := by
  exact (approximatingSolution f hfm n).uniform_entropyMoment_all_times
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by positivity) hfm hf hi t

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SpacetimeRelativeEntropy
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrating a uniform entropy budget over a bounded time window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem spacetimeEntropy_measurable {F : ℝ × Phase → ℝ} (hF : Measurable F) :
    Measurable (spacetimeEntropy F) :=
  hF.mul ((measurable_const.add (measurable_snd.snd.norm.pow_const 2)).add hF.log.abs)

theorem spacetimeEntropy_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    {F : ℝ × Phase → ℝ} {C : ℝ} (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z)
    (hi : ∀ t, Integrable (entropyMoment (fun p => F (t,p))))
    (hb : ∀ t, (∫ p, entropyMoment (fun p => F (t,p)) p) ≤ C) :
    Integrable (spacetimeEntropy F) (μ.prod volume) := by
  have hm := spacetimeEntropy_measurable hFm
  have hn (z : ℝ × Phase) : 0 ≤ spacetimeEntropy F z := mul_nonneg (hF z) (by positivity)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall hi
  · have hnorm : (fun t => ∫ p, ‖spacetimeEntropy F (t,p)‖) =
        (fun t => ∫ p, spacetimeEntropy F (t,p)) := by
      funext t
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => Real.norm_of_nonneg (hn (t,p)))
    rw [hnorm]
    apply (integrable_const C).mono' hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [] with t
    rw [Real.norm_of_nonneg (integral_nonneg (fun p => hn (t,p)))]
    exact hb t

theorem spacetimeEntropy_integral_le {μ : Measure ℝ} [IsFiniteMeasure μ]
    {F : ℝ × Phase → ℝ} {C : ℝ} (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z)
    (hi : ∀ t, Integrable (entropyMoment (fun p => F (t,p))))
    (hb : ∀ t, (∫ p, entropyMoment (fun p => F (t,p)) p) ≤ C) :
    (∫ z, spacetimeEntropy F z ∂μ.prod volume) ≤ μ.real univ*C := by
  have hi' := spacetimeEntropy_integrable (μ := μ) hFm hF hi hb
  rw [integral_prod _ hi']
  exact (integral_mono hi'.integral_prod_left (integrable_const C) hb).trans_eq (integral_const C)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Relative entropy and the absolute entropy moment in spacetime -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem spacetimeRelativeEntropy_measurable {F : ℝ × Phase → ℝ} (hF : Measurable F) :
    Measurable (spacetimeRelativeEntropy F) :=
  scalarRelativeEntropy_measurable (by unfold maxwellian; fun_prop) hF

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {F : ℝ × Phase → ℝ}

omit [IsFiniteMeasure μ] in
theorem density_integrable_of_spacetimeEntropy (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z)
    (hi : Integrable (spacetimeEntropy F) (μ.prod volume)) :
    Integrable F (μ.prod volume) := by
  apply hi.mono' hFm.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_of_nonneg (hF z)]
    have h : 1 ≤ 1+‖z.2.2‖^2+|Real.log (F z)| := by
      nlinarith [sq_nonneg ‖z.2.2‖,abs_nonneg (Real.log (F z))]
    simpa only [spacetimeEntropy,mul_one] using mul_le_mul_of_nonneg_left h (hF z))

theorem relativeEntropy_integrable_of_spacetimeEntropy
    (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z)
    (hi : Integrable (spacetimeEntropy F) (μ.prod volume)) :
    Integrable (spacetimeRelativeEntropy F) (μ.prod volume) := by
  have hM := integrable_maxwellian_phase.comp_snd μ
  apply ((hi.const_mul initialEntropyCoefficient).add hM).mono'
    (spacetimeRelativeEntropy_measurable hFm).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    dsimp only [spacetimeRelativeEntropy,Pi.add_apply]
    rw [Real.norm_of_nonneg (scalarRelativeEntropy_nonneg (maxwellian_pos _) (hF z))]
    exact relativeEntropy_density_bound (fun p => hF (z.1,p)) z.2)

theorem spacetimeEntropy_integrable_of_relativeEntropy
    (hFm : Measurable F) (hF : ∀ z, 0 ≤ F z)
    (hi : Integrable (spacetimeRelativeEntropy F) (μ.prod volume)) :
    Integrable (spacetimeEntropy F) (μ.prod volume) := by
  have hG := (entropyGaussian_integrable.comp_snd (volume : Measure Position)).comp_snd μ
  have hM := integrable_maxwellian_phase.comp_snd μ
  have hmajor := ((hi.const_mul (1+4*entropyMomentCoefficient)).add
    (hG.const_mul (4*entropyMomentCoefficient))).add hM
  apply hmajor.mono' (spacetimeEntropy_measurable hFm).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_of_nonneg (show 0 ≤ spacetimeEntropy F z from
      mul_nonneg (hF z) (by positivity))]
    exact entropyMoment_control (f := fun p => F (z.1,p)) (z := z.2) (hF z))

theorem spacetimeRelativeEntropy_integral_le
    (hi : Integrable (spacetimeRelativeEntropy F) (μ.prod volume)) {C : ℝ}
    (hb : ∀ t, relativeEntropy (fun p => F (t,p)) ≤ C) :
    (∫ z, spacetimeRelativeEntropy F z ∂μ.prod volume) ≤ μ.real univ*C := by
  rw [integral_prod _ hi]
  have he (t : ℝ) : (∫ p, spacetimeRelativeEntropy F (t,p)) =
      relativeEntropy (fun p => F (t,p)) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)
  exact (integral_mono hi.integral_prod_left (integrable_const C)
    (fun t => (he t).trans_le (hb t))).trans_eq (integral_const C)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicRenormalizedCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Weak L1 extraction for the actual global approximation sequence -/
noncomputable section
open MeasureTheory Filter
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.kinetic_entropy_integrable
    (S : BoundedCutoffSolution N T f₀) (hN : 0 ≤ N)
    {μ : Measure ℝ} [IsFiniteMeasure μ] {C : ℝ}
    (hb : ∀ t, (∫ p, entropyMoment (fun p => S.density (t,p)) p) ≤ C) :
    Integrable (entropyGauge S.kineticProfile) ((μ.prod (volume : Measure Position)).prod volume) := by
  have hi := spacetimeEntropy_integrable (μ := μ) S.measurable S.nonnegative
    (fun t => (S.finiteEntropy hN t).2.2) hb
  have hr := (kineticGrouping_measurePreserving μ).integrable_comp_of_integrable hi
  exact hr

theorem BoundedCutoffSolution.kinetic_entropy_integral_le
    (S : BoundedCutoffSolution N T f₀) (hN : 0 ≤ N)
    {μ : Measure ℝ} [IsFiniteMeasure μ] {C : ℝ}
    (hb : ∀ t, (∫ p, entropyMoment (fun p => S.density (t,p)) p) ≤ C) :
    (∫ p, entropyGauge S.kineticProfile p ∂(μ.prod (volume : Measure Position)).prod volume) ≤ μ.real Set.univ*C := by
  have h := spacetimeEntropy_integral_le (μ := μ) S.measurable S.nonnegative
    (fun t => (S.finiteEntropy hN t).2.2) hb
  have he := (kineticGrouping_measurePreserving μ).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding (spacetimeEntropy S.density)
  rw [← he] at h
  exact h

theorem approximatingSolution_compactness_hypotheses (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    UniformIntegrable (fun n => (approximatingSolution f hfm n).kineticProfile) 1
      ((μ.prod (volume : Measure Position)).prod volume) ∧
    UnifTight (fun n => (approximatingSolution f hfm n).kineticProfile) 1
      ((μ.prod (volume : Measure Position)).prod volume) := by
  have hm := fun n => (approximatingSolution f hfm n).kineticProfile_measurable
  have hn : ∀ (n : ℕ) (p : (ℝ × Position) × Velocity),
      0 ≤ (approximatingSolution f hfm n).kineticProfile p :=
    fun n p => (approximatingSolution f hfm n).nonnegative (p.1.1,(p.1.2,p.2))
  have hg := fun n => (approximatingSolution f hfm n).kinetic_entropy_integrable
    (μ := μ) (by positivity) (approximatingSolution_entropy f hfm hf hi n)
  have hb := fun n => (approximatingSolution f hfm n).kinetic_entropy_integral_le
    (μ := μ) (by positivity) (approximatingSolution_entropy f hfm hf hi n)
  exact ⟨uniformIntegrable_of_entropyGauge hm hn hg hb,unifTight_of_entropyGauge hm hn hg hb⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual symmetric cutoff loss has a uniform normalized L1 bound -/
noncomputable section
open MeasureTheory Set Filter
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem windowKernel_le_physical (N : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    windowKernel N z ≤ collisionKernel z.1.2.1 z.1.2.2 z.2 := by
  by_cases hz : z ∈ collisionWindow N
  · rw [windowKernel,indicator_of_mem hz]
  · rw [windowKernel,indicator_of_notMem hz]
    exact collisionKernel_nonneg _ _ _

omit [MeasurableSpace X] in
theorem regularizedPreRate_le_physical {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) : regularizedPreRate N f z ≤ preRate f z := by
  have hm := rateMultiplier_bounds hN hf z
  have hw := windowKernel_bounds hN.le z
  have hk : windowKernel N z*rateMultiplier N f z ≤ collisionKernel z.1.2.1 z.1.2.2 z.2 :=
    (mul_le_mul_of_nonneg_left hm.2 hw.1).trans (by simpa using windowKernel_le_physical N z)
  rw [regularizedPreRate_factor]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk (hf _)) (hf _)

theorem loss_le_physical {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (p : X × Velocity)
    (h0 : Integrable (fun v => f (p.1,v))) (h1 : Integrable (fun v => ‖v‖*f (p.1,v))) :
    loss N f p ≤ lossDensity f p := by
  have hp : Integrable (fun q : Velocity × Sphere => preRate f (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea) :=
    integrable_loss_of_moments (fun z : Phase => f (p.1,z.2)) 0 p.2 h0 h1
  have hle : fiberMeasure N ≤ (volume : Measure Velocity).prod sphereArea := by
    rw [fiberMeasure_eq_restrict]
    exact Measure.restrict_le_self
  calc
    loss N f p ≤ ∫ q, preRate f (collisionGrouping.symm (p,q)) ∂fiberMeasure N :=
      integral_mono (pre_fiber_integrable hN hfm hf p) (hp.mono_measure hle)
        (fun q => regularizedPreRate_le_physical hN hf _)
    _ ≤ lossDensity f p := integral_mono_measure hle (ae_of_all _ (fun q => preRate_nonneg hf _)) hp

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Uniform relative entropy of the concrete global approximation sequence -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem BoundedCutoffSolution.relativeEntropy_all_times {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) (hT : 0 ≤ T) (t : ℝ) :
    relativeEntropy (fun p => S.density (t,p)) ≤ relativeEntropy f₀ := by
  have he : (fun p => S.density (t,p)) = (fun p => S.density (PositiveIntegral.time T t,p)) :=
    funext (S.density_clipped hT t)
  rw [he]
  exact S.relativeEntropy_le hN hT (PositiveIntegral.time_bounds hT t)

theorem approximatingSolution_relativeEntropy (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (n : ℕ) (t : ℝ) :
    relativeEntropy (fun p => (approximatingSolution f hfm n).density (t,p)) ≤
      initialEntropyBudget f := by
  exact ((approximatingSolution f hfm n).relativeEntropy_all_times (by positivity) (by positivity) t).trans
    (initialApproximation_relativeEntropy_le (by have := Nat.cast_nonneg (α := ℝ) n; linarith) hfm hf hi)

theorem approximatingSolution_spacetimeEntropy_integrable (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (n : ℕ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (spacetimeEntropy (approximatingSolution f hfm n).density) (μ.prod volume) :=
  spacetimeEntropy_integrable (approximatingSolution f hfm n).measurable
    (approximatingSolution f hfm n).nonnegative
    (fun t => ((approximatingSolution f hfm n).finiteEntropy (by positivity) t).2.2)
    (approximatingSolution_entropy f hfm hf hi n)

theorem approximatingSolution_spacetimeRelativeEntropy (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (n : ℕ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable (spacetimeRelativeEntropy (approximatingSolution f hfm n).density) (μ.prod volume) ∧
      (∫ z, spacetimeRelativeEntropy (approximatingSolution f hfm n).density z ∂μ.prod volume) ≤
        μ.real univ*initialEntropyBudget f := by
  have hE := relativeEntropy_integrable_of_spacetimeEntropy
    (approximatingSolution f hfm n).measurable (approximatingSolution f hfm n).nonnegative
    (approximatingSolution_spacetimeEntropy_integrable f hfm hf hi n μ)
  exact ⟨hE,spacetimeRelativeEntropy_integral_le hE (approximatingSolution_relativeEntropy f hfm hf hi n)⟩

theorem initialEntropyBudget_nonneg (f : Density) (hf : ∀ p, 0 ≤ f p) :
    0 ≤ initialEntropyBudget f := by
  apply add_nonneg
  · exact mul_nonneg initialEntropyCoefficient_nonneg
      (integral_nonneg (fun p => mul_nonneg (hf p) (by positivity)))
  · exact integral_nonneg (fun p => (maxwellian_pos p.2).le)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakEntropyMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Relative entropy bounds pass to weak L¹ limits -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem WeakL1Converges.entropy_bound {f : ℕ → X → ℝ} {g m : X → ℝ}
    (h : WeakL1Converges μ f g) (hfi : ∀ n, Integrable (f n) μ)
    (hfn : ∀ n, 0 ≤ᵐ[μ] f n) (hgn : 0 ≤ᵐ[μ] g)
    (hmm : Measurable m) (hmi : Integrable m μ) (hmp : ∀ᵐ x ∂μ, 0 < m x)
    (hHi : ∀ n, Integrable (fun x => scalarRelativeEntropy (m x) (f n x)) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hH : ∀ᶠ n in atTop, (∫ x, scalarRelativeEntropy (m x) (f n x) ∂μ) ≤ C) :
    Integrable (fun x => scalarRelativeEntropy (m x) (g x)) μ ∧
      (∫ x, scalarRelativeEntropy (m x) (g x) ∂μ) ≤ C := by
  let ψ : ℕ → X → ℝ := fun n x => boundedEntropyTest n (m x) (g x)
  let d : ℕ → X → ℝ := fun n x => entropyDual (m x) (g x) (ψ n x)
  have hψm n : Measurable (ψ n) := measurable_boundedEntropyTest n hmm h.1
  have hψb n x : |ψ n x| ≤ (n:ℝ) := boundedEntropyTest_bound n (m x) (g x)
  have hdi n : Integrable (d n) μ := integrable_entropyDual hmi h.2.1 (hψm n) (hψb n)
  have hdm n : Measurable (d n) := measurable_entropyDual hmm h.1 (hψm n)
  have hdn n : 0 ≤ᵐ[μ] d n := by
    filter_upwards [hmp,hgn] with x hmx hgx
    exact entropyDual_boundedEntropyTest_nonneg n hmx hgx
  have hdB n : (∫ x, d n x ∂μ) ≤ C := by
    have hcorr := hmi.bdd_mul ((hψm n).exp.sub measurable_const).aestronglyMeasurable
      (ae_of_all μ (fun x => show |Real.exp (ψ n x)-1| ≤ Real.exp (n:ℝ)+1 from by
        calc
          _ ≤ |Real.exp (ψ n x)|+|1| := abs_sub _ _
          _ = Real.exp (ψ n x)+1 := by rw [abs_of_pos (Real.exp_pos _),abs_one]
          _ ≤ _ := add_le_add (Real.exp_le_exp.mpr ((le_abs_self _).trans (hψb n x))) le_rfl))
    have hdki k := integrable_entropyDual hmi (hfi k) (hψm n) (hψb n)
    have he (u : X → ℝ) (hui : Integrable u μ) :
        (∫ x, entropyDual (m x) (u x) (ψ n x) ∂μ) =
          (∫ x, ψ n x*u x ∂μ)-(∫ x, (Real.exp (ψ n x)-1)*m x ∂μ) := by
      simpa only [entropyDual,mul_comm,Pi.sub_def,Pi.mul_def] using integral_sub
        (hui.bdd_mul (hψm n).aestronglyMeasurable (ae_of_all μ (hψb n))) hcorr
    have ht : Tendsto (fun k => ∫ x, entropyDual (m x) (f k x) (ψ n x) ∂μ)
        atTop (𝓝 (∫ x, d n x ∂μ)) := by
      simp only [he _ (hfi _),show (∫ x, d n x ∂μ) = _ from he g h.2.1]
      exact (h.2.2 (ψ n) (hψm n) ⟨n,hψb n⟩).sub_const _
    apply le_of_tendsto ht
    filter_upwards [hH] with k hk
    refine (integral_mono_ae (hdki k) (hHi k) ?_).trans hk
    filter_upwards [hmp,hfn k] with x hmx hfx
    exact entropyDual_le hmx hfx _
  have hHm : Measurable (fun x => scalarRelativeEntropy (m x) (g x)) :=
    ((h.1.mul h.1.log).sub (h.1.mul (measurable_const.add hmm.log))).add hmm
  have hHn : 0 ≤ᵐ[μ] (fun x => scalarRelativeEntropy (m x) (g x)) := by
    filter_upwards [hmp,hgn] with x hmx hgx
    exact scalarRelativeEntropy_nonneg hmx hgx
  have hfatou : (∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (g x)) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (d n x) ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (d n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hmp,hgn] with x hmx hgx
        exact (ENNReal.tendsto_ofReal (entropyDual_boundedEntropyTest_tendsto hmx hgx)).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le (fun n => (hdm n).ennreal_ofReal)
  have hbound : (∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (g x)) ∂μ) ≤
      ENNReal.ofReal C := by
    refine hfatou.trans (liminf_le_of_frequently_le ?_)
    exact (Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hdi n) (hdn n)]
      exact ENNReal.ofReal_le_ofReal (hdB n))).frequently
  have hgi : Integrable (fun x => scalarRelativeEntropy (m x) (g x)) μ :=
    ⟨hHm.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hHn).mpr
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hgi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hgi hHn] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hbound

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_StrongCompactPairTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong stability of positive survival factors from L1 convergence of the rates -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [SFinite ν]

theorem timeSurvival_measurable {f : ℝ × P → ℝ} (hf : Measurable f) :
    Measurable (timeSurvival μ f) := (timePrimitive_measurable μ hf).neg.exp

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Strong convergence of physical survival kernels with two time endpoints -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
open Compactness
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [SFinite ν]

theorem timeDifference_measurable {u : ℝ × P → ℝ} (hu : Measurable u) :
    Measurable (timeDifference u) :=
  (hu.comp measurable_fst).sub (hu.comp (measurable_snd.prodMk measurable_fst.snd))

theorem twoTimeSurvival_measurable {f : ℝ × P → ℝ} (hf : Measurable f) :
    Measurable (twoTimeSurvival μ f) :=
  (measurable_const.max (timeDifference_measurable (timePrimitive_measurable μ hf))).neg.exp

omit [MeasurableSpace P] [IsFiniteMeasure μ] [SFinite ν] in
theorem twoTimeSurvival_eq_interval {T s t : ℝ} (ht : t ∈ Set.Icc 0 T)
    (hs : s ∈ Set.Icc 0 t) {f : ℝ × P → ℝ} (hf : ∀ z, 0 ≤ f z) (p : P)
    (hi : IntervalIntegrable (fun r => f (r,p)) volume 0 T) :
    twoTimeSurvival (volume.restrict (Set.Icc 0 T)) f ((t,p),s) =
      Real.exp (-(∫ r in s..t, f (r,p))) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0s : IntervalIntegrable (fun r => f (r,p)) volume 0 s := by
    apply hi.mono_set
    rw [Set.uIcc_of_le hs.1,Set.uIcc_of_le hT]
    intro r hr
    exact ⟨hr.1,hr.2.trans (hs.2.trans ht.2)⟩
  have hst : IntervalIntegrable (fun r => f (r,p)) volume s t := by
    apply hi.mono_set
    rw [Set.uIcc_of_le hs.2,Set.uIcc_of_le hT]
    intro r hr
    exact ⟨hs.1.trans hr.1,hr.2.trans ht.2⟩
  have he := intervalIntegral.integral_add_adjacent_intervals h0s hst
  have hd : (∫ r in 0..t, f (r,p))-(∫ r in 0..s, f (r,p)) = ∫ r in s..t, f (r,p) := by
    linarith
  have hn : 0 ≤ ∫ r in s..t, f (r,p) :=
    intervalIntegral.integral_nonneg hs.2 (fun r _ => hf (r,p))
  simp only [twoTimeSurvival,timeDifference,timePrimitive_eq_interval ht,
    timePrimitive_eq_interval (show s ∈ Set.Icc 0 T from ⟨hs.1,hs.2.trans ht.2⟩),hd,max_eq_right hn]

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_SurvivalVolterraIntegrable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Measurability of a survival-weighted characteristic source -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.Published
variable {P : Type*} [MeasurableSpace P] {μ : Measure ℝ} [SFinite μ]

theorem survivalVolterra_measurable {a : (ℝ × P) × ℝ → ℝ} {f : ℝ × P → ℝ}
    (ha : Measurable a) (hf : Measurable f) : Measurable (survivalVolterra μ a f) := by
  have hm : Measurable (fun z : (ℝ × P) × ℝ =>
      if z.2 ≤ z.1.1 then a z*f (z.2,z.1.2) else 0) :=
    (ha.mul (hf.comp (measurable_snd.prodMk measurable_fst.snd))).ite
      (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Jets_TorusVelocityWindowAE
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Free torus flight preserves each fixed velocity restriction -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.TorusFlight

theorem flight_measurePreserving_velocity (t : ℝ) (ν : Measure Velocity) [SFinite ν] :
    MeasurePreserving (flight t) ((volume : Measure Position).prod ν)
      ((volume : Measure Position).prod ν) := by
  have hm : Measurable (Function.uncurry (fun (v : Velocity) (x : Position) =>
      x+torusProjection (t • v))) := by
    unfold Function.uncurry torusProjection
    fun_prop
  have hskew := (MeasurePreserving.id ν).skew_product hm
    (ae_of_all _ (fun v => (measurePreserving_add_right (volume : Measure Position)
      (torusProjection (t • v))).map_eq))
  have he : flight t = Prod.swap ∘ (fun z : Velocity × Position =>
      (z.1,z.2+torusProjection (t • z.1))) ∘ Prod.swap := rfl
  rw [he]
  exact (Measure.measurePreserving_swap (μ := ν) (ν := (volume : Measure Position))).comp
    (hskew.comp Measure.measurePreserving_swap)

theorem along_measurePreserving_velocity (μ : Measure ℝ) (ν : Measure Velocity)
    [SFinite μ] [SFinite ν] :
    MeasurePreserving (fun z : ℝ × Phase => (z.1,flight z.1 z.2))
      (μ.prod ((volume : Measure Position).prod ν))
      (μ.prod ((volume : Measure Position).prod ν)) :=
  (MeasurePreserving.id μ).skew_product measurable_flight
    (ae_of_all _ (fun t => (flight_measurePreserving_velocity t ν).map_eq))

theorem alongRegroup_measurePreserving (μ : Measure ℝ) (ν : Measure Velocity)
    [SFinite μ] [SFinite ν] :
    MeasurePreserving (fun z : ℝ × Phase => ((z.1,(flight z.1 z.2).1),z.2.2))
      (μ.prod ((volume : Measure Position).prod ν)) ((μ.prod volume).prod ν) :=
  (measurePreserving_prodAssoc μ (volume : Measure Position) ν).symm.comp
    (along_measurePreserving_velocity μ ν)

theorem strong_along_regroup {μ : Measure ℝ} {ν : Measure Velocity} [SFinite μ] [SFinite ν]
    {f : ℕ → (ℝ × Position) × Velocity → ℝ} {g : (ℝ × Position) × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (ht : Tendsto (fun n => eLpNorm (f n-g) 1 ((μ.prod volume).prod ν)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (along (regroup (f n))-along (regroup g))
      1 (μ.prod ((volume : Measure Position).prod ν))) atTop (𝓝 0) := by
  apply ht.congr'
  apply Eventually.of_forall
  intro n
  exact (eLpNorm_comp_measurePreserving ((hfm n).sub hgm).aestronglyMeasurable
    (alongRegroup_measurePreserving μ ν)).symm

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Weak limits and uniform integrability along flight with a fixed velocity restriction -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.TorusFlight

theorem flight_snd (t : ℝ) (p : Phase) : (flight t p).2 = p.2 := rfl

theorem backRegroup_measurePreserving (μ : Measure ℝ) (ν : Measure Velocity)
    [SFinite μ] [SFinite ν] :
    MeasurePreserving (fun z : (ℝ × Position) × Velocity =>
      (z.1.1,flight (-z.1.1) (z.1.2,z.2)))
      ((μ.prod volume).prod ν) (μ.prod ((volume : Measure Position).prod ν)) := by
  have hb : MeasurePreserving (fun z : ℝ × Phase => (z.1,flight (-z.1) z.2))
      (μ.prod ((volume : Measure Position).prod ν))
      (μ.prod ((volume : Measure Position).prod ν)) :=
    (MeasurePreserving.id μ).skew_product (g := fun (t : ℝ) (p : Phase) => flight (-t) p)
      (measurable_flight.comp (measurable_fst.neg.prodMk measurable_snd))
      (ae_of_all _ (fun t => (flight_measurePreserving_velocity (-t) ν).map_eq))
  exact hb.comp (measurePreserving_prodAssoc μ (volume : Measure Position) ν)

theorem uniformIntegrable_along_regroup_local {μ : Measure ℝ} {ν : Measure Velocity}
    [SFinite μ] [SFinite ν] {f : ℕ → (ℝ × Position) × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hu : UniformIntegrable f 1 ((μ.prod volume).prod ν)) :
    UniformIntegrable (fun n => along (regroup (f n))) 1
      (μ.prod ((volume : Measure Position).prod ν)) := by
  apply Compactness.uniformIntegrable_of_comp_measurePreserving (backRegroup_measurePreserving μ ν)
    (fun n => (hfm n).comp (alongRegroup_measurePreserving μ ν).measurable)
  simpa only [along,regroup,Function.comp_def,neg_flight,flight_snd] using hu

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Removing velocity windows from time-phase null-set statements -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness
variable {μ : Measure ℝ} [SFinite μ]

theorem ae_timePhase_of_velocity_windows {P : ℝ × Phase → Prop}
    (h : ∀ n : ℕ, ∀ᵐ z ∂μ.prod ((volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 (n:ℝ)))), P z) :
    ∀ᵐ z ∂μ.prod (volume : Measure Phase), P z := by
  have hg : ∀ n : ℕ, ∀ᵐ z ∂(μ.prod (volume : Measure Position)).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 (n:ℝ))),
      P (z.1.1,(z.1.2,z.2)) := fun n =>
    (measurePreserving_prodAssoc μ (volume : Measure Position)
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 (n:ℝ)))).quasiMeasurePreserving.ae (h n)
  have hh := ae_prod_of_velocity_windows hg
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_prodAssoc μ (volume : Measure Position)
    (volume : Measure Velocity)).symm.quasiMeasurePreserving.ae hh

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalFrequencyWindow
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Physical loss frequency in kinetic spacetime coordinates -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem kineticFrequency_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (kineticFrequency f) := by
  have hm : Measurable (fun p : (X × Velocity) × Velocity => ‖p.1.2-p.2‖*f (p.1.1,p.2)) := by
    fun_prop
  exact measurable_const.mul hm.stronglyMeasurable.integral_prod_right'.measurable

omit [MeasurableSpace X] in
theorem kineticFrequency_nonneg {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (p : X × Velocity) : 0 ≤ kineticFrequency f p := by
  unfold kineticFrequency
  exact mul_nonneg (by positivity) (integral_nonneg (fun w => mul_nonneg (norm_nonneg _) (hf _)))

theorem lossDensity_eq_mul_kineticFrequency (f : X × Velocity → ℝ) (p : X × Velocity)
    (hi : Integrable (fun q : Velocity × Sphere => preRate f (collisionGrouping.symm (p,q)))
      ((volume : Measure Velocity).prod sphereArea)) :
    lossDensity f p = f p*kineticFrequency f p := by
  change Integrable (fun q : Velocity × Sphere =>
    collisionKernel p.2 q.1 q.2*f (p.1,p.2)*f (p.1,q.1)) _ at hi
  rw [lossDensity_formula,integral_prod _ hi]
  simp_rw [integral_mul_const,integral_collisionKernel_sphereArea]
  calc
    (∫ w, 2*Real.pi*‖p.2-w‖*f (p.1,p.2)*f (p.1,w)) =
        ∫ w, (f p*(2*Real.pi))*(‖p.2-w‖*f (p.1,w)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun w => by dsimp <;> ring)
    _ = (f p*(2*Real.pi))*(∫ w, ‖p.2-w‖*f (p.1,w)) := integral_const_mul _ _
    _ = f p*kineticFrequency f p := by unfold kineticFrequency; ring

end BoltzmannNonuniqueness.CollisionCompactness

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

/-! # Finite first moments give locally integrable physical frequencies -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.CollisionCompactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem kineticFrequency_integrable_local {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (linearMoment f) (μ.prod volume))
    {R : ℝ} (hR : 0 ≤ R) :
    Integrable (kineticFrequency f)
      (μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))) := by
  let τ : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let : IsFiniteMeasure τ := isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  have hm := (hi.integral_prod_left.comp_fst τ).const_mul (2*Real.pi*(R+1))
  apply hm.mono' (kineticFrequency_measurable hfm).aestronglyMeasurable
  have hx := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := τ)).ae hi.prod_right_ae
  have hv := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := τ)).ae
    (ae_restrict_mem Metric.isClosed_closedBall.measurableSet)
  filter_upwards [hx,hv] with p hpx hpv
  have hpR : ‖p.2‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hpv
  have hb w : ‖‖p.2-w‖*f (p.1,w)‖ ≤ (R+1)*linearMoment f (p.1,w) := by
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hf _))]
    apply le_trans (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (hf _))
    dsimp only [linearMoment]
    have hc : ‖p.2‖+‖w‖ ≤ (R+1)*(1+‖w‖) := by nlinarith [norm_nonneg w]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hc (hf (p.1,w))
  have hh := norm_integral_le_of_norm_le (hpx.const_mul (R+1)) (ae_of_all _ hb)
  rw [integral_const_mul] at hh
  rw [Real.norm_of_nonneg (kineticFrequency_nonneg hf p)]
  dsimp only [kineticFrequency]
  calc
    2*Real.pi*(∫ w, ‖p.2-w‖*f (p.1,w)) ≤
        2*Real.pi*‖∫ w, ‖p.2-w‖*f (p.1,w)‖ :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    _ ≤ 2*Real.pi*((R+1)*(∫ w, linearMoment f (p.1,w))) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedGainCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Scalar majorants for the gain discrepancy of two positive profiles -/
namespace BoltzmannNonuniqueness.Compactness

theorem normalized_difference_abs_le {a b u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |(a-b)/(1+u+v)| ≤ |a-b| := by
  rw [abs_div,abs_of_pos (by positivity : 0 < 1+u+v)]
  exact div_le_self (abs_nonneg _) (by linarith)

end BoltzmannNonuniqueness.Compactness


end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicWeakCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A single nonnegative global weak limit of the actual periodic approximants -/
noncomputable section
open MeasureTheory Filter Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.weak_on_window {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) {T : ℝ} (hT : 0 ≤ T) :
    Published.WeakL1Converges ((volume.restrict (Icc 0 T)).prod volume)
      (fun n => (approximatingSolution f hfm (G.indices n)).density) G.density :=
  weak_localize_time G.weighted_weak hT

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Weak velocity averages of the same global periodic limit -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.kineticProfile_measurable {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) : Measurable G.kineticProfile :=
  G.measurable.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

theorem GlobalWeakLimit.kinetic_weak_on_window {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) {T : ℝ} (hT : 0 ≤ T) :
    Published.WeakL1Converges (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume)
      (fun n => (approximatingSolution f hfm (G.indices n)).kineticProfile) G.kineticProfile := by
  apply Published.WeakL1Converges.of_comp_measurePreserving
    (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm
    (fun n => (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)
    G.kineticProfile_measurable
  exact G.weak_on_window hT

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Entropy and velocity moments of the actual global weak limit -/
noncomputable section
open MeasureTheory Filter Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

variable {f : Density} {hfm : Measurable f}

theorem relativeEntropy_of_weak_approximation
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {μ : Measure ℝ} [IsFiniteMeasure μ] {φ : ℕ → ℕ} {g : ℝ × Phase → ℝ}
    (hg : Published.WeakL1Converges (μ.prod volume)
      (fun n => (approximatingSolution f hfm (φ n)).density) g)
    (hgn : ∀ z, 0 ≤ g z) :
    Integrable (spacetimeRelativeEntropy g) (μ.prod volume) ∧
      (∫ z, spacetimeRelativeEntropy g z ∂μ.prod volume) ≤ μ.real univ*initialEntropyBudget f := by
  have hE n := approximatingSolution_spacetimeEntropy_integrable f hfm hf hi (φ n) μ
  have hH n := approximatingSolution_spacetimeRelativeEntropy f hfm hf hi (φ n) μ
  exact hg.entropy_bound
    (fun n => density_integrable_of_spacetimeEntropy
      (approximatingSolution f hfm (φ n)).measurable (approximatingSolution f hfm (φ n)).nonnegative (hE n))
    (fun n => ae_of_all _ (approximatingSolution f hfm (φ n)).nonnegative)
    (ae_of_all _ hgn) (by unfold maxwellian; fun_prop)
    (integrable_maxwellian_phase.comp_snd μ) (ae_of_all _ (fun z => maxwellian_pos z.2.2))
    (fun n => (hH n).1) (mul_nonneg (by positivity) (initialEntropyBudget_nonneg f hf))
    (Eventually.of_forall (fun n => (hH n).2))

theorem GlobalWeakLimit.entropy_on_window (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (spacetimeRelativeEntropy G.density) ((volume.restrict (Icc 0 T)).prod volume) ∧
      (∫ z, spacetimeRelativeEntropy G.density z ∂(volume.restrict (Icc 0 T)).prod volume) ≤
        (volume.restrict (Icc 0 T)).real univ*initialEntropyBudget f :=
  relativeEntropy_of_weak_approximation hf hi (G.weak_on_window hT) G.nonnegative

theorem GlobalWeakLimit.entropyMoment_on_window (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (spacetimeEntropy G.density) ((volume.restrict (Icc 0 T)).prod volume) :=
  spacetimeEntropy_integrable_of_relativeEntropy G.measurable G.nonnegative
    (G.entropy_on_window hf hi hT).1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicJointBudgetLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual periodic normalized pairs converge with the collision velocity weight -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.kinetic_entropy_on_window {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (entropyGauge G.kineticProfile)
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) :=
  (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable
    (G.entropyMoment_on_window hf hi hT)

end BoltzmannNonuniqueness.PeriodicApproximation

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

/-! # The full physical gain is the almost-everywhere limit on characteristics -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem physicalCharacteristicGain_measurable {f : (ℝ × Position) × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (physicalCharacteristicGain f) :=
  (gainDensity_measurable hfm).comp
    ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

theorem physicalCharacteristicGain_nonneg {f : (ℝ × Position) × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : ℝ × Phase) : 0 ≤ physicalCharacteristicGain f z :=
  gainDensity_nonneg hf _

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_InitialLinearComparison
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Vanishing initial positive-difference error along arbitrary late subsequences -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness TransportPrimitive

theorem initialApproximation_comparison_L1 {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable f)
    {I J : ℕ → ℕ} (hI : Tendsto I atTop atTop) (hJ : Tendsto J atTop atTop)
    {ν : Measure Phase} (hν : ν ≤ volume) :
    Tendsto (fun n => eLpNorm (fun p =>
      |positiveDifference (initialApproximation ((I n:ℝ)+1) f p)
        (initialApproximation ((J n:ℝ)+1) f p)|) 1 ν) atTop (𝓝 0) := by
  have ht := strongL1_sub_of_common_limit
    ((initialApproximation_norm_tendsto hfm hf hi).comp hI)
    ((initialApproximation_norm_tendsto hfm hf hi).comp hJ)
    (fun n => (initialApproximation_measurable _ hfm).aestronglyMeasurable)
    (fun n => (initialApproximation_measurable _ hfm).aestronglyMeasurable) hfm.aestronglyMeasurable
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  apply le_trans _ (eLpNorm_mono_measure _ hν)
  have hm : Measurable (fun p => |positiveDifference
      (initialApproximation ((I n:ℝ)+1) f p) (initialApproximation ((J n:ℝ)+1) f p)|) :=
    (((initialApproximation_measurable _ hfm).sub (initialApproximation_measurable _ hfm)).div
      ((measurable_const.add (initialApproximation_measurable _ hfm)).add
        (initialApproximation_measurable _ hfm))).abs
  apply eLpNorm_mono
  intro p
  simp only [Real.norm_eq_abs,abs_abs]
  exact normalized_difference_abs_le
    (initialApproximation_bounds (by positivity : 0 ≤ (I n:ℝ)+1) f p).1
    (initialApproximation_bounds (by positivity : 0 ≤ (J n:ℝ)+1) f p).1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The initial approximation converges in the positive comparison metric -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness TransportPrimitive

theorem initialApproximation_linear_comparison_L1 {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable f)
    {I : ℕ → ℕ} (hI : Tendsto I atTop atTop)
    {ν : Measure Phase} (hν : ν ≤ volume) :
    Tendsto (fun n => eLpNorm (fun p =>
      |positiveDifference (initialApproximation ((I n:ℝ)+1) f p) (f p)|) 1 ν)
      atTop (𝓝 0) := by
  have ht := (initialApproximation_norm_tendsto hfm hf hi).comp hI
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  apply le_trans _ (eLpNorm_mono_measure _ hν)
  have hm : Measurable (fun p => |positiveDifference
      (initialApproximation ((I n:ℝ)+1) f p) (f p)|) :=
    (((initialApproximation_measurable _ hfm).sub hfm).div
      ((measurable_const.add (initialApproximation_measurable _ hfm)).add hfm)).abs
  apply eLpNorm_mono
  intro p
  simp only [Real.norm_eq_abs,abs_abs]
  exact normalized_difference_abs_le
    (initialApproximation_bounds (by positivity : 0 ≤ (I n:ℝ)+1) f p).1 (hf p)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LinearSurvivalIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The positive linear solution equals the survival-weighted source formula -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published
variable {P : Type*} [MeasurableSpace P]

omit [MeasurableSpace P] in
theorem linearSolution_eq_survival {T t : ℝ} (ht : t ∈ Icc 0 T)
    (a : ℝ) {k : ℝ × P → ℝ} (hk : ∀ z, 0 ≤ k z) (g : ℝ × P → ℝ) (p : P)
    (hki : IntervalIntegrable (fun s => k (s,p)) volume 0 T) :
    TransportPrimitive.linearSolution a (fun s => k (s,p)) (fun s => g (s,p)) t =
      timeSurvival (volume.restrict (Icc 0 T)) k (t,p)*a+
      survivalVolterra (volume.restrict (Icc 0 T))
        (twoTimeSurvival (volume.restrict (Icc 0 T)) k) g (t,p) := by
  have hsource := timePrimitive_eq_interval ht
    (fun z : ℝ × P => twoTimeSurvival (volume.restrict (Icc 0 T)) k ((t,p),z.1)*g z) p
  change survivalVolterra (volume.restrict (Icc 0 T))
    (twoTimeSurvival (volume.restrict (Icc 0 T)) k) g (t,p) = _ at hsource
  rw [TransportPrimitive.linearSolution_formula,hsource,timeSurvival,timePrimitive_eq_interval ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hs
  have h0s : IntervalIntegrable (fun r => k (r,p)) volume 0 s := by
    apply hki.mono_set
    rw [uIcc_of_le hs0.1,uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl (hs0.2.trans ht.2)
  have hst : IntervalIntegrable (fun r => k (r,p)) volume s t := by
    apply hki.mono_set
    rw [uIcc_of_le hs0.2,uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc hs0.1 ht.2
  have he := intervalIntegral.integral_add_adjacent_intervals h0s hst
  have hd : (∫ r in 0..t, k (r,p))-(∫ r in 0..s, k (r,p)) = ∫ r in s..t, k (r,p) := by
    linarith
  dsimp only
  rw [twoTimeSurvival_eq_interval ht hs0 hk p hki,hd]

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicStrongAverages
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual physical frequencies and survival along torus characteristics -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem physicalCharacteristicFrequency_measurable {f : (ℝ × Position) × Velocity → ℝ}
    (hf : Measurable f) : Measurable (physicalCharacteristicFrequency f) :=
  (kineticFrequency_measurable hf).comp
    ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

theorem physicalCharacteristicFrequency_nonneg {f : (ℝ × Position) × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : ℝ × Phase) : 0 ≤ physicalCharacteristicFrequency f z :=
  kineticFrequency_nonneg hf _

theorem physicalCharacteristicFrequency_integrable {f : (ℝ × Position) × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) {μ : Measure ℝ} [SFinite μ]
    (hi : Integrable (linearMoment f) ((μ.prod (volume : Measure Position)).prod volume))
    {R : ℝ} (hR : 0 ≤ R) :
    Integrable (physicalCharacteristicFrequency f)
      (μ.prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) :=
  (TorusFlight.alongRegroup_measurePreserving μ _).integrable_comp_of_integrable
    (kineticFrequency_integrable_local hfm hf hi hR)

theorem GlobalCollisionLimit.characteristic_frequency_integrable {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    (∀ n, Integrable
      (physicalCharacteristicFrequency (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) ∧
    Integrable (physicalCharacteristicFrequency G.weakLimit.kineticProfile)
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) := by
  constructor
  · intro n
    apply physicalCharacteristicFrequency_integrable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
      (fun p => (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _) _ hR
    exact linearMoment_integrable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
      (fun p => (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _)
      ((approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
        (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _))
  · exact physicalCharacteristicFrequency_integrable G.weakLimit.kineticProfile_measurable
      (fun _ => G.weakLimit.nonnegative _) (linearMoment_integrable G.weakLimit.kineticProfile_measurable
        (fun _ => G.weakLimit.nonnegative _) (G.weakLimit.kinetic_entropy_on_window hf hi hT)) hR

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The physical loss controls every supported approximation -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.velocity_fiber_moments (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (t : ℝ) (x : Position) :
    Integrable (fun v => S.density (t,(x,v))) ∧
      Integrable (fun v => ‖v‖*S.density (t,(x,v))) := by
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  have hm : Measurable (fun v => S.density (t,(x,v))) :=
    S.measurable.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hb v : |S.density (t,(x,v))| ≤ B :=
    (abs_of_nonneg (S.nonnegative _)).trans_le (hB _)
  exact ⟨bounded_velocity_fiber_integrable hm hb (fun v => S.support (t,(x,v))),
    bounded_velocity_fiber_weighted hB0 hN hm measurable_id.norm hb
      (fun v => S.support (t,(x,v))) (fun v hv => by simpa only [abs_norm] using hv)⟩

theorem BoundedCutoffSolution.loss_le_frequency (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (z : ℝ × Phase) :
    loss N (fun p => S.density (z.1,p)) z.2 ≤
      S.density z*kineticFrequency S.kineticProfile ((z.1,z.2.1),z.2.2) := by
  have hm : Measurable (fun p => S.density (z.1,p)) :=
    S.measurable.comp (measurable_const.prodMk measurable_id)
  obtain ⟨hi0,hi1⟩ := S.velocity_fiber_moments hN.le z.1 z.2.1
  have hi := integrable_loss_of_moments (fun p => S.density (z.1,p)) z.2.1 z.2.2 hi0 hi1
  have he := lossDensity_eq_mul_kineticFrequency (fun p => S.density (z.1,p)) z.2 hi
  exact (loss_le_physical hN hm (fun p => S.nonnegative _) z.2 hi0 hi1).trans_eq he

theorem BoundedCutoffSolution.frequency_bounded (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (v : Velocity) :
    ∃ C : ℝ, ∀ t x, |kineticFrequency S.kineticProfile ((t,x),v)| ≤ C := by
  obtain ⟨B,hB⟩ := S.bounded
  let b : Velocity → ℝ := (Metric.closedBall 0 N).indicator (fun _ => (‖v‖+N)*B)
  have hi : Integrable b :=
    (integrableOn_const (isCompact_closedBall (0 : Velocity) N).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  refine ⟨2*Real.pi*(∫ w, b w),?_⟩
  intro t x
  have hb w : ‖‖v-w‖*S.density (t,(x,w))‖ ≤ b w := by
    by_cases hw : w ∈ Metric.closedBall 0 N
    · have hwN : ‖w‖ ≤ N := by simpa only [Metric.mem_closedBall,dist_zero_right] using hw
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (S.nonnegative _))]
      change _ ≤ (Metric.closedBall 0 N).indicator (fun _ => (‖v‖+N)*B) w
      rw [indicator_of_mem hw]
      exact mul_le_mul ((norm_sub_le v w).trans (add_le_add le_rfl hwN)) (hB _)
        (S.nonnegative _) (add_nonneg (norm_nonneg _) hN)
    · have hwN : N < ‖w‖ := by
        simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hw
      change _ ≤ (Metric.closedBall 0 N).indicator (fun _ => (‖v‖+N)*B) w
      rw [S.support (t,(x,w)) hwN,mul_zero,norm_zero,indicator_of_notMem hw]
  have hh := norm_integral_le_of_norm_le hi (ae_of_all _ hb)
  change |2*Real.pi*(∫ w, ‖v-w‖*S.density (t,(x,w)))| ≤ _
  rw [abs_mul,abs_of_nonneg (show 0 ≤ 2*Real.pi by positivity)]
  exact mul_le_mul_of_nonneg_left hh (by positivity)

theorem BoundedCutoffSolution.frequency_path_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (p : Phase) (t : ℝ) :
    IntervalIntegrable (fun r => physicalCharacteristicFrequency S.kineticProfile (r,p))
      volume 0 t := by
  obtain ⟨C,hC⟩ := S.frequency_bounded hN p.2
  apply (intervalIntegrable_const (c := C)).mono_fun'
  · exact ((physicalCharacteristicFrequency_measurable S.kineticProfile_measurable).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · exact ae_of_all _ (fun r => by
      change |kineticFrequency S.kineticProfile ((r,(TorusFlight.flight r p).1),p.2)| ≤ C
      exact hC r (TorusFlight.flight r p).1)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The supported approximants dominate their physical positive characteristic source -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.characteristicGain_measurable (S : BoundedCutoffSolution N T f₀) :
    Measurable S.characteristicGain :=
  (gain_measurable N S.kineticProfile_measurable).comp
    ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

theorem BoundedCutoffSolution.gain_path_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (p : Phase) (t : ℝ) :
    IntervalIntegrable (fun r => S.characteristicGain (r,p)) volume 0 t := by
  apply (intervalIntegrable_const (c := gainBound N)).mono_fun'
  · exact (S.characteristicGain_measurable.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [] with r
    have hb := gain_bounds hN S.kineticProfile_measurable
      (fun q => S.nonnegative _) ((r,(TorusFlight.flight r p).1),p.2)
    exact (Real.norm_of_nonneg hb.1).trans_le hb.2

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The physical loss defect along each actual bounded characteristic -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.characteristicLossDefect_measurable
    (S : BoundedCutoffSolution N T f₀) : Measurable S.characteristicLossDefect :=
  ((lossDensity_measurable S.kineticProfile_measurable).sub
    (loss_measurable N S.kineticProfile_measurable)).comp
      ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

theorem BoundedCutoffSolution.physical_loss_eq (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (z : (ℝ × Position) × Velocity) :
    lossDensity S.kineticProfile z = S.kineticProfile z*kineticFrequency S.kineticProfile z := by
  obtain ⟨h0,h1⟩ := S.velocity_fiber_moments hN z.1.1 z.1.2
  exact lossDensity_eq_mul_kineticFrequency _ z
    (integrable_loss_of_moments (fun q : Phase => S.density (z.1.1,q)) z.1.2 z.2 h0 h1)

theorem BoundedCutoffSolution.characteristicLossDefect_eq (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (z : ℝ × Phase) :
    S.characteristicLossDefect z =
      S.density (z.1,TorusFlight.flight z.1 z.2)*physicalCharacteristicFrequency S.kineticProfile z-
        loss N (fun q => S.density (z.1,q)) (TorusFlight.flight z.1 z.2) := by
  change lossDensity S.kineticProfile ((z.1,(TorusFlight.flight z.1 z.2).1),z.2.2)-_ = _
  rw [S.physical_loss_eq hN]
  rfl

theorem BoundedCutoffSolution.characteristicLossDefect_nonneg (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (z : ℝ × Phase) : 0 ≤ S.characteristicLossDefect z := by
  rw [S.characteristicLossDefect_eq hN.le]
  exact sub_nonneg.mpr (S.loss_le_frequency hN (z.1,TorusFlight.flight z.1 z.2))

theorem BoundedCutoffSolution.lossDefect_path_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (p : Phase) (t : ℝ) :
    IntervalIntegrable (fun r => S.characteristicLossDefect (r,p)) volume 0 t := by
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  obtain ⟨C,hC⟩ := S.frequency_bounded hN.le p.2
  apply (intervalIntegrable_const (c := B*C)).mono_fun'
  · exact (S.characteristicLossDefect_measurable.comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [] with r
    rw [Real.norm_of_nonneg (S.characteristicLossDefect_nonneg hN (r,p)),
      S.characteristicLossDefect_eq hN.le]
    have hl := (loss_bounds hN
      (S.measurable.comp (measurable_const.prodMk measurable_id))
      (fun q => S.nonnegative (r,q)) (TorusFlight.flight r p)).1
    apply (sub_le_self _ hl).trans
    apply mul_le_mul (hB (r,TorusFlight.flight r p))
      ((le_abs_self _).trans (hC r (TorusFlight.flight r p).1))
      (physicalCharacteristicFrequency_nonneg (f := S.kineticProfile)
        (fun q => S.nonnegative _) (r,p)) hB0

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual damped path with its physical frequency and nonnegative loss defect -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.dampedPath_eq (S : BoundedCutoffSolution N T f₀)
    {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    S.dampedPath p t = S.density (t,TorusFlight.flight t p) := (S.along_eq_damped ht p).symm

theorem BoundedCutoffSolution.dampedPath_initial (S : BoundedCutoffSolution N T f₀) (p : Phase) :
    S.dampedPath p 0 = f₀ p := by simp [dampedPath,TransportPrimitive.damped]

theorem BoundedCutoffSolution.dampedPath_absolutelyContinuous (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (p : Phase) (t : ℝ) :
    AbsolutelyContinuousOnInterval (S.dampedPath p) 0 t :=
  TransportPrimitive.damped_absolutelyContinuous (S.source_path_integrable hN p t)

theorem BoundedCutoffSolution.dampedPath_physical_derivative (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    ∀ᵐ r, r ∈ Icc 0 t → HasDerivAt (S.dampedPath p)
      (S.characteristicGain (r,p)-physicalCharacteristicFrequency S.kineticProfile (r,p)*
        S.dampedPath p r+S.characteristicLossDefect (r,p)) r := by
  have hd := TransportPrimitive.damped_derivative_ae (S.source_path_integrable hN p t)
    (L := lossBound N) (c := f₀ p)
  filter_upwards [hd] with r hr hrt
  have hrr : r ∈ Icc 0 T := ⟨hrt.1,hrt.2.trans ht.2⟩
  have hv := S.dampedPath_eq hrr p
  have hder := hr (by simpa only [uIcc_of_le ht.1] using hrt)
  change HasDerivAt (S.dampedPath p)
    (S.source (r,TorusFlight.flight r p)-lossBound N*S.dampedPath p r) r at hder
  have he : S.source (r,TorusFlight.flight r p)-lossBound N*S.dampedPath p r =
      S.characteristicGain (r,p)-physicalCharacteristicFrequency S.kineticProfile (r,p)*
        S.dampedPath p r+S.characteristicLossDefect (r,p) := by
    rw [S.characteristicLossDefect_eq hN.le,hv]
    change positiveSource N (fun q => S.density (r,q)) (TorusFlight.flight r p)-
        lossBound N*S.density (r,TorusFlight.flight r p) =
      gain N (fun q => S.density (r,q)) (TorusFlight.flight r p)-
        physicalCharacteristicFrequency S.kineticProfile (r,p)*S.density (r,TorusFlight.flight r p)+
        (S.density (r,TorusFlight.flight r p)*physicalCharacteristicFrequency S.kineticProfile (r,p)-
          loss N (fun q => S.density (r,q)) (TorusFlight.flight r p))
    unfold positiveSource
    ring
  exact he ▸ hder

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Comparison of two actual periodic approximations along each characteristic -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness TransportPrimitive

theorem BoundedCutoffSolution.positive_comparison
    {N M H K : ℝ} {f₀ g₀ : Density}
    (S : BoundedCutoffSolution N H f₀) (P : BoundedCutoffSolution M K g₀)
    (hN : 0 < N) (hM : 0 < M) {t : ℝ} (ht : t ∈ Icc 0 H) (ht' : t ≤ K) (p : Phase) :
    |positiveDifference (S.density (t,TorusFlight.flight t p))
      (P.density (t,TorusFlight.flight t p))| ≤ |positiveDifference (f₀ p) (g₀ p)|+
      ∫ r in 0..t,
        |S.characteristicGain (r,p)-P.characteristicGain (r,p)|/
          (1+S.density (r,TorusFlight.flight r p)+P.density (r,TorusFlight.flight r p))+
        S.characteristicLossDefect (r,p)/(1+S.density (r,TorusFlight.flight r p))+
        P.characteristicLossDefect (r,p)/(1+P.density (r,TorusFlight.flight r p))+
        |physicalCharacteristicFrequency S.kineticProfile (r,p)-
          physicalCharacteristicFrequency P.kineticProfile (r,p)| := by
  have hs r (hr : r ∈ Icc 0 t) : S.dampedPath p r = S.density (r,TorusFlight.flight r p) :=
    S.dampedPath_eq ⟨hr.1,hr.2.trans ht.2⟩ p
  have hp r (hr : r ∈ Icc 0 t) : P.dampedPath p r = P.density (r,TorusFlight.flight r p) :=
    P.dampedPath_eq ⟨hr.1,hr.2.trans ht'⟩ p
  have hsu r (hr : r ∈ Icc 0 t) : 0 ≤ S.dampedPath p r := by rw [hs r hr]; exact S.nonnegative _
  have hpu r (hr : r ∈ Icc 0 t) : 0 ≤ P.dampedPath p r := by rw [hp r hr]; exact P.nonnegative _
  have hsa r (_hr : r ∈ Icc 0 t) : 0 ≤ S.characteristicGain (r,p) :=
    (gain_bounds hN S.kineticProfile_measurable (fun q => S.nonnegative _)
      ((r,(TorusFlight.flight r p).1),p.2)).1
  have hpa r (_hr : r ∈ Icc 0 t) : 0 ≤ P.characteristicGain (r,p) :=
    (gain_bounds hM P.kineticProfile_measurable (fun q => P.nonnegative _)
      ((r,(TorusFlight.flight r p).1),p.2)).1
  have hh := positiveDifference_error_bound ht.1
    (S.dampedPath_absolutelyContinuous hN p t) (P.dampedPath_absolutelyContinuous hM p t)
    hsu hpu hsa hpa
    (fun r _ => physicalCharacteristicFrequency_nonneg (f := S.kineticProfile)
      (fun q => S.nonnegative _) (r,p))
    (fun r _ => physicalCharacteristicFrequency_nonneg (f := P.kineticProfile)
      (fun q => P.nonnegative _) (r,p))
    (fun r _ => S.characteristicLossDefect_nonneg hN (r,p))
    (fun r _ => P.characteristicLossDefect_nonneg hM (r,p))
    (S.gain_path_integrable hN p t) (P.gain_path_integrable hM p t)
    (S.frequency_path_integrable hN.le p t) (P.frequency_path_integrable hM.le p t)
    (S.lossDefect_path_integrable hN p t) (P.lossDefect_path_integrable hM p t)
    (S.dampedPath_physical_derivative hN ht p)
    (P.dampedPath_physical_derivative hM ⟨ht.1,ht'⟩ p)
  rw [hs t ⟨ht.1,le_rfl⟩,hp t ⟨ht.1,le_rfl⟩,
    S.dampedPath_initial,P.dampedPath_initial] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hr
  dsimp only
  rw [hs r hr',hp r hr']

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionComparisonError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The four physical errors in positive characteristic comparison -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem collisionComparisonError_measurable {N M : ℝ} {F H : X × Velocity → ℝ}
    (hF : Measurable F) (hH : Measurable H) : Measurable (collisionComparisonError N M F H) := by
  exact (((((gain_measurable N hF).sub (gain_measurable M hH)).div
    ((measurable_const.add hF).add hH)).abs.add
      (((lossDensity_measurable hF).sub (loss_measurable N hF)).div (measurable_const.add hF)).abs).add
      (((lossDensity_measurable hH).sub (loss_measurable M hH)).div (measurable_const.add hH)).abs).add
      ((kineticFrequency_measurable hF).sub (kineticFrequency_measurable hH)).abs

theorem collisionComparisonError_nonneg (N M : ℝ) (F H : X × Velocity → ℝ) (p : X × Velocity) :
    0 ≤ collisionComparisonError N M F H p := by
  unfold collisionComparisonError
  positivity

end BoltzmannNonuniqueness.PeriodicApproximation

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PrefixComparisonConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Integrating a nonnegative characteristic comparison on a finite time window -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {P : Type*} [MeasurableSpace P] {ν : Measure P} [SFinite ν]

theorem prefixComparison_eLpNorm_le {T : ℝ} (hT : 0 ≤ T)
    {F e : ℝ × P → ℝ} {d : P → ℝ}
    (hFm : Measurable F) (hem : Measurable e) (hdm : Measurable d)
    (he0 : ∀ z, 0 ≤ e z)
    (hei : Integrable e ((volume.restrict (Icc 0 T)).prod ν))
    (hb : ∀ t ∈ Icc 0 T, ∀ p, |F (t,p)| ≤ d p+∫ s in 0..t, e (s,p)) :
    eLpNorm F 1 ((volume.restrict (Icc 0 T)).prod ν) ≤
      eLpNorm (fun _ : ℝ => (1:ℝ)) 1 (volume.restrict (Icc 0 T))*
        (eLpNorm d 1 ν+eLpNorm e 1 ((volume.restrict (Icc 0 T)).prod ν)) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let a : P → ℝ := fun p => ∫ s, e (s,p) ∂μ
  have ham : Measurable a := hem.stronglyMeasurable.integral_prod_left'.measurable
  have ha0 p : 0 ≤ a p := integral_nonneg (fun s => he0 (s,p))
  have ha : eLpNorm a 1 ν ≤ eLpNorm e 1 (μ.prod ν) := by
    have h := eLpNorm_integral_le (μ := ν) (ν := μ) (hem.comp measurable_swap)
    exact h.trans_eq (eLpNorm_comp_measurePreserving hem.aestronglyMeasurable
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)))
  have hbound : ∀ᵐ z ∂μ.prod ν, ‖F z‖ ≤ d z.2+a z.2 := by
    have ht : ∀ᵐ z ∂μ.prod ν, z.1 ∈ Icc 0 T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    have hi : ∀ᵐ z ∂μ.prod ν, Integrable (fun s => e (s,z.2)) μ :=
      Measure.quasiMeasurePreserving_snd.ae hei.prod_left_ae
    filter_upwards [ht,hi] with z hz hzi
    have hint : IntervalIntegrable (fun s => e (s,z.2)) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hzi
    have hm := intervalIntegral.integral_mono_interval (a := (0:ℝ)) (b := z.1)
      (c := (0:ℝ)) (d := T) le_rfl hz.1 hz.2
      (ae_of_all _ (fun s => he0 (s,z.2))) hint
    have heq : (∫ s in 0..T, e (s,z.2)) = a z.2 := by
      rw [intervalIntegral.integral_of_le hT,← integral_Icc_eq_integral_Ioc]
    rw [heq] at hm
    have hb' : ‖F z‖ ≤ d z.2+∫ s in 0..z.1, e (s,z.2) := by
      simpa only [Real.norm_eq_abs] using hb z.1 hz z.2
    exact hb'.trans (add_le_add le_rfl hm)
  have hprod : eLpNorm (fun z : ℝ × P => d z.2+a z.2) 1 (μ.prod ν) =
      eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ*eLpNorm (fun p => d p+a p) 1 ν := by
    simpa only [one_mul,Pi.add_apply] using eLpNorm_mul_prod_one
      (μ := μ) (ν := ν) (f := fun _ : ℝ => (1:ℝ)) (g := fun p => d p+a p)
      measurable_const (hdm.add ham)
  calc
    _ ≤ eLpNorm (fun z : ℝ × P => d z.2+a z.2) 1 (μ.prod ν) :=
      eLpNorm_mono_ae_real hbound
    _ = _ := hprod
    _ ≤ _ := mul_le_mul' le_rfl ((eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)).trans (add_le_add le_rfl ha))

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Integrating a nonnegative characteristic comparison on a finite time window -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {P : Type*} [MeasurableSpace P] {ν : Measure P} [SFinite ν]

theorem prefixComparison_ae_eLpNorm_le {T : ℝ} (hT : 0 ≤ T)
    {F e : ℝ × P → ℝ} {d : P → ℝ}
    (hFm : Measurable F) (hem : Measurable e) (hdm : Measurable d)
    (he0 : ∀ z, 0 ≤ e z)
    (hei : Integrable e ((volume.restrict (Icc 0 T)).prod ν))
    (hb : ∀ᵐ p ∂ν, ∀ t ∈ Icc 0 T, |F (t,p)| ≤ d p+∫ s in 0..t, e (s,p)) :
    eLpNorm F 1 ((volume.restrict (Icc 0 T)).prod ν) ≤
      eLpNorm (fun _ : ℝ => (1:ℝ)) 1 (volume.restrict (Icc 0 T))*
        (eLpNorm d 1 ν+eLpNorm e 1 ((volume.restrict (Icc 0 T)).prod ν)) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let a : P → ℝ := fun p => ∫ s, e (s,p) ∂μ
  have ham : Measurable a := hem.stronglyMeasurable.integral_prod_left'.measurable
  have ha0 p : 0 ≤ a p := integral_nonneg (fun s => he0 (s,p))
  have ha : eLpNorm a 1 ν ≤ eLpNorm e 1 (μ.prod ν) := by
    have h := eLpNorm_integral_le (μ := ν) (ν := μ) (hem.comp measurable_swap)
    exact h.trans_eq (eLpNorm_comp_measurePreserving hem.aestronglyMeasurable
      (Measure.measurePreserving_swap (μ := ν) (ν := μ)))
  have hbound : ∀ᵐ z ∂μ.prod ν, ‖F z‖ ≤ d z.2+a z.2 := by
    have ht : ∀ᵐ z ∂μ.prod ν, z.1 ∈ Icc 0 T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    have hi : ∀ᵐ z ∂μ.prod ν, Integrable (fun s => e (s,z.2)) μ :=
      Measure.quasiMeasurePreserving_snd.ae hei.prod_left_ae
    filter_upwards [ht,hi,Measure.quasiMeasurePreserving_snd.ae hb] with z hz hzi hzb
    have hint : IntervalIntegrable (fun s => e (s,z.2)) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hzi
    have hm := intervalIntegral.integral_mono_interval (a := (0:ℝ)) (b := z.1)
      (c := (0:ℝ)) (d := T) le_rfl hz.1 hz.2
      (ae_of_all _ (fun s => he0 (s,z.2))) hint
    have heq : (∫ s in 0..T, e (s,z.2)) = a z.2 := by
      rw [intervalIntegral.integral_of_le hT,← integral_Icc_eq_integral_Ioc]
    rw [heq] at hm
    have hb' : ‖F z‖ ≤ d z.2+∫ s in 0..z.1, e (s,z.2) := by
      simpa only [Real.norm_eq_abs] using hzb z.1 hz
    exact hb'.trans (add_le_add le_rfl hm)
  have hprod : eLpNorm (fun z : ℝ × P => d z.2+a z.2) 1 (μ.prod ν) =
      eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ*eLpNorm (fun p => d p+a p) 1 ν := by
    simpa only [one_mul,Pi.add_apply] using eLpNorm_mul_prod_one
      (μ := μ) (ν := ν) (f := fun _ : ℝ => (1:ℝ)) (g := fun p => d p+a p)
      measurable_const (hdm.add ham)
  calc
    _ ≤ eLpNorm (fun z : ℝ × P => d z.2+a z.2) 1 (μ.prod ν) :=
      eLpNorm_mono_ae_real hbound
    _ = _ := hprod
    _ ≤ _ := mul_le_mul' le_rfl ((eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)).trans (add_le_add le_rfl ha))

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Vanishing initial and source errors imply vanishing characteristic comparisons -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {P : Type*} [MeasurableSpace P] {ν : Measure P} [SFinite ν]

theorem prefixComparison_ae_strongL1 {T : ℝ} (hT : 0 ≤ T)
    {F e : ℕ → ℝ × P → ℝ} {d : ℕ → P → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hem : ∀ n, Measurable (e n))
    (hdm : ∀ n, Measurable (d n)) (he0 : ∀ n z, 0 ≤ e n z)
    (hb : ∀ n, ∀ᵐ p ∂ν, ∀ t ∈ Icc 0 T, |F n (t,p)| ≤ d n p+∫ s in 0..t, e n (s,p))
    (hdt : Tendsto (fun n => eLpNorm (d n) 1 ν) atTop (𝓝 0))
    (het : Tendsto (fun n => eLpNorm (e n) 1 ((volume.restrict (Icc 0 T)).prod ν))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 1 ((volume.restrict (Icc 0 T)).prod ν)) atTop (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hfinite : eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ ≠ ∞ :=
    (memLp_one_iff_integrable.mpr (integrable_const (1:ℝ))).eLpNorm_ne_top
  have ht := ENNReal.Tendsto.const_mul (a := eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ)
    (hdt.add het) (Or.inr hfinite)
  simp only [zero_add,mul_zero] at ht
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp ht ε hε,
    ENNReal.tendsto_nhds_zero.mp het 1 (by norm_num)] with n hn hne
  have hi : Integrable (e n) (μ.prod ν) := memLp_one_iff_integrable.mp
    (show MemLp (e n) 1 (μ.prod ν) from ⟨(hem n).aestronglyMeasurable, hne.trans_lt (by simp)⟩)
  exact (prefixComparison_ae_eLpNorm_le hT (hFm n) (hem n) (hdm n) (he0 n) hi (hb n)).trans hn

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Vanishing initial and source errors imply vanishing characteristic comparisons -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {P : Type*} [MeasurableSpace P] {ν : Measure P} [SFinite ν]

theorem prefixComparison_strongL1 {T : ℝ} (hT : 0 ≤ T)
    {F e : ℕ → ℝ × P → ℝ} {d : ℕ → P → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hem : ∀ n, Measurable (e n))
    (hdm : ∀ n, Measurable (d n)) (he0 : ∀ n z, 0 ≤ e n z)
    (hb : ∀ n t, t ∈ Icc 0 T → ∀ p, |F n (t,p)| ≤ d n p+∫ s in 0..t, e n (s,p))
    (hdt : Tendsto (fun n => eLpNorm (d n) 1 ν) atTop (𝓝 0))
    (het : Tendsto (fun n => eLpNorm (e n) 1 ((volume.restrict (Icc 0 T)).prod ν))
      atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 1 ((volume.restrict (Icc 0 T)).prod ν)) atTop (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hfinite : eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ ≠ ∞ :=
    (memLp_one_iff_integrable.mpr (integrable_const (1:ℝ))).eLpNorm_ne_top
  have ht := ENNReal.Tendsto.const_mul (a := eLpNorm (fun _ : ℝ => (1:ℝ)) 1 μ)
    (hdt.add het) (Or.inr hfinite)
  simp only [zero_add,mul_zero] at ht
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [ENNReal.tendsto_nhds_zero.mp ht ε hε,
    ENNReal.tendsto_nhds_zero.mp het 1 (by norm_num)] with n hn hne
  have hi : Integrable (e n) (μ.prod ν) := memLp_one_iff_integrable.mp
    (show MemLp (e n) 1 (μ.prod ν) from ⟨(hem n).aestronglyMeasurable, hne.trans_lt (by simp)⟩)
  exact (prefixComparison_eLpNorm_le hT (hFm n) (hem n) (hdm n) (he0 n) hi (hb n)).trans hn

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicDensityStrong
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The nonnegative collision error is the actual characteristic comparison error -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness TransportPrimitive

theorem BoundedCutoffSolution.collisionComparisonError_along
    {N M H K : ℝ} {f₀ g₀ : Density}
    (S : BoundedCutoffSolution N H f₀) (P : BoundedCutoffSolution M K g₀)
    (hN : 0 < N) (hM : 0 < M) (r : ℝ) (p : Phase) :
    TorusFlight.along (TorusFlight.regroup
      (collisionComparisonError N M S.kineticProfile P.kineticProfile)) (r,p) =
      |S.characteristicGain (r,p)-P.characteristicGain (r,p)|/
        (1+S.density (r,TorusFlight.flight r p)+P.density (r,TorusFlight.flight r p))+
      S.characteristicLossDefect (r,p)/(1+S.density (r,TorusFlight.flight r p))+
      P.characteristicLossDefect (r,p)/(1+P.density (r,TorusFlight.flight r p))+
      |physicalCharacteristicFrequency S.kineticProfile (r,p)-
        physicalCharacteristicFrequency P.kineticProfile (r,p)| := by
  change |(S.characteristicGain (r,p)-P.characteristicGain (r,p))/
      (1+S.density (r,TorusFlight.flight r p)+P.density (r,TorusFlight.flight r p))|+
    |S.characteristicLossDefect (r,p)/(1+S.density (r,TorusFlight.flight r p))|+
    |P.characteristicLossDefect (r,p)/(1+P.density (r,TorusFlight.flight r p))|+_ = _
  rw [abs_div,abs_of_pos (show 0 < 1+S.density (r,TorusFlight.flight r p)+
    P.density (r,TorusFlight.flight r p) by
      have := S.nonnegative (r,TorusFlight.flight r p)
      have := P.nonnegative (r,TorusFlight.flight r p)
      positivity)]
  rw [abs_of_nonneg (div_nonneg (S.characteristicLossDefect_nonneg hN (r,p)) (by
    have := S.nonnegative (r,TorusFlight.flight r p); positivity))]
  rw [abs_of_nonneg (div_nonneg (P.characteristicLossDefect_nonneg hM (r,p)) (by
    have := P.nonnegative (r,TorusFlight.flight r p); positivity))]
  rfl

theorem BoundedCutoffSolution.positive_comparison_error
    {N M H K : ℝ} {f₀ g₀ : Density}
    (S : BoundedCutoffSolution N H f₀) (P : BoundedCutoffSolution M K g₀)
    (hN : 0 < N) (hM : 0 < M) {t : ℝ} (ht : t ∈ Icc 0 H) (ht' : t ≤ K) (p : Phase) :
    |positiveDifference (S.density (t,TorusFlight.flight t p))
      (P.density (t,TorusFlight.flight t p))| ≤ |positiveDifference (f₀ p) (g₀ p)|+
      ∫ r in 0..t, TorusFlight.along (TorusFlight.regroup
        (collisionComparisonError N M S.kineticProfile P.kineticProfile)) (r,p) := by
  have he := S.positive_comparison P hN hM ht ht' p
  simpa only [S.collisionComparisonError_along P hN hM] using he

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The positive-difference metric of actual approximation subsequences vanishes -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness TransportPrimitive

theorem GlobalCollisionLimit.positive_difference_L1 {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (i j : ℕ → ℕ) (hit : Tendsto i atTop atTop) (hjt : Tendsto j atTop atTop) :
    let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
    let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
    Tendsto (fun n => eLpNorm (fun z : ℝ × Phase => positiveDifference
      ((approximatingSolution f hfm (I n)).density (z.1,TorusFlight.flight z.1 z.2))
      ((approximatingSolution f hfm (J n)).density (z.1,TorusFlight.flight z.1 z.2))) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
  let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
  let S n := approximatingSolution f hfm (I n)
  let P n := approximatingSolution f hfm (J n)
  let U n (z : ℝ × Phase) := (S n).density (z.1,TorusFlight.flight z.1 z.2)
  let V n (z : ℝ × Phase) := (P n).density (z.1,TorusFlight.flight z.1 z.2)
  let d n (p : Phase) := |positiveDifference (initialApproximation ((I n:ℝ)+1) f p)
    (initialApproximation ((J n:ℝ)+1) f p)|
  let E n := TorusFlight.along (TorusFlight.regroup
    (collisionComparisonError ((I n:ℝ)+1) ((J n:ℝ)+1) (S n).kineticProfile (P n).kineticProfile))
  have hUm n : Measurable (U n) := (S n).measurable.comp
    (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hVm n : Measurable (V n) := (P n).measurable.comp
    (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hEm n : Measurable (E n) := (collisionComparisonError_measurable
    (S n).kineticProfile_measurable (P n).kineticProfile_measurable).comp
      ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)
  have hdm n : Measurable (d n) :=
    (((initialApproximation_measurable _ hfm).sub (initialApproximation_measurable _ hfm)).div
      ((measurable_const.add (initialApproximation_measurable _ hfm)).add
        (initialApproximation_measurable _ hfm))).abs
  have hi' : Tendsto I atTop atTop := G.weakLimit.increasing.tendsto_atTop.comp
    ((tendsto_add_atTop_nat (Nat.ceil T)).comp hit)
  have hj' : Tendsto J atTop atTop := G.weakLimit.increasing.tendsto_atTop.comp
    ((tendsto_add_atTop_nat (Nat.ceil T)).comp hjt)
  have hν : (volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) ≤ (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hdt := initialApproximation_comparison_L1 hfm hf (integrable_of_entropyGauge hfm hf hi)
    hi' hj' hν
  have het := G.characteristic_error_L1_q80 hf hi hT hR i j hit hjt
  apply prefixComparison_strongL1 hT
    (fun n => ((hUm n).sub (hVm n)).div ((measurable_const.add (hUm n)).add (hVm n)))
    hEm hdm (fun n z => collisionComparisonError_nonneg _ _ _ _ _) _ hdt het
  intro n t ht p
  have hI : Nat.ceil T ≤ I n :=
    (Nat.le_add_left (Nat.ceil T) (i n)).trans (G.weakLimit.increasing.id_le _)
  have hJ : Nat.ceil T ≤ J n :=
    (Nat.le_add_left (Nat.ceil T) (j n)).trans (G.weakLimit.increasing.id_le _)
  have hIT : T ≤ (I n:ℝ)+1 := by
    have hc : T ≤ (Nat.ceil T:ℝ) := Nat.le_ceil T
    have hn : (Nat.ceil T:ℝ) ≤ (I n:ℝ) := by exact_mod_cast hI
    linarith
  have hJT : T ≤ (J n:ℝ)+1 := by
    have hc : T ≤ (Nat.ceil T:ℝ) := Nat.le_ceil T
    have hn : (Nat.ceil T:ℝ) ≤ (J n:ℝ) := by exact_mod_cast hJ
    linarith
  exact (S n).positive_comparison_error (P n) (by positivity) (by positivity)
    ⟨ht.1,ht.2.trans hIT⟩ (ht.2.trans hJT) p

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Any two late actual density subsequences approach each other in local L1 -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness TransportPrimitive

theorem GlobalCollisionLimit.density_pair_L1 {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (i j : ℕ → ℕ) (hit : Tendsto i atTop atTop) (hjt : Tendsto j atTop atTop) :
    let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
    let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
    Tendsto (fun n => eLpNorm (fun z =>
      (approximatingSolution f hfm (I n)).kineticProfile z-
      (approximatingSolution f hfm (J n)).kineticProfile z) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let I := fun n => G.weakLimit.indices (i n+Nat.ceil T)
  let J := fun n => G.weakLimit.indices (j n+Nat.ceil T)
  let U n := (approximatingSolution f hfm (I n)).kineticProfile
  let V n := (approximatingSolution f hfm (J n)).kineticProfile
  have hUm n : Measurable (U n) := (approximatingSolution f hfm (I n)).kineticProfile_measurable
  have hVm n : Measurable (V n) := (approximatingSolution f hfm (J n)).kineticProfile_measurable
  have hUn n z : 0 ≤ U n z := (approximatingSolution f hfm (I n)).nonnegative _
  have hVn n z : 0 ≤ V n z := (approximatingSolution f hfm (J n)).nonnegative _
  have hbase := (approximatingSolution_compactness_hypotheses f hfm hf hi
    (volume.restrict (Icc 0 T))).1
  have hUi := uniformIntegrable_restrict (uniformIntegrable_comp hbase I)
    (univ ×ˢ Metric.closedBall (0:Velocity) R)
  have hVi := uniformIntegrable_restrict (uniformIntegrable_comp hbase J)
    (univ ×ˢ Metric.closedBall (0:Velocity) R)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hUi hVi
  apply positiveDifference_L1 hUm hVm hUn hVn hUi hVi
  have hd := G.positive_difference_L1 hf hi hT hR i j hit hjt
  apply hd.congr'
  apply Eventually.of_forall
  intro n
  have hm : Measurable (fun z => positiveDifference (U n z) (V n z)) :=
    ((hUm n).sub (hVm n)).div ((measurable_const.add (hUm n)).add (hVm n))
  have h := eLpNorm_comp_measurePreserving (p := 1) hm.aestronglyMeasurable
    (TorusFlight.alongRegroup_measurePreserving (volume.restrict (Icc 0 T))
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))
  refine Eq.trans ?_ h
  congr 1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual global collision subsequence converges strongly in local L1 -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.density_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (fun z =>
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile z-
      G.weakLimit.kineticProfile z) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let ν : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let F n := (approximatingSolution f hfm (G.weakLimit.indices (n+Nat.ceil T))).kineticProfile
  have hUI := (approximatingSolution_compactness_hypotheses f hfm hf hi
    (volume.restrict (Icc 0 T))).1
  have hfi n : Integrable (F n) (μ.prod ν) := by
    have h := memLp_one_iff_integrable.mp (hUI.memLp (G.weakLimit.indices (n+Nat.ceil T)))
    exact h.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hw := ((G.weakLimit.kinetic_weak_on_window hT).comp
    (tendsto_add_atTop_nat (Nat.ceil T))).restrict
      (s := univ ×ˢ Metric.closedBall (0:Velocity) R)
      (MeasurableSet.univ.prod measurableSet_closedBall)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hw
  have hp : ∀ i j : ℕ → ℕ, Tendsto i atTop atTop → Tendsto j atTop atTop →
      Tendsto (fun n => eLpNorm (fun z => F (i n) z-F (j n) z) 1 (μ.prod ν)) atTop (𝓝 0) :=
    fun i j hit hjt => G.density_pair_L1 hf hi hT hR i j hit hjt
  have hs := strongL1_of_pairwise_subsequences hfi hw hp
  exact (tendsto_add_atTop_iff_nat (Nat.ceil T)).mp hs

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalLinearContinuous
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A common full-measure set of flights with locally integrable gain and frequency -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.frequency_path_integrable_full {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ p ∂(volume : Measure Phase),
      Integrable (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 T)) := by
  rw [Measure.volume_eq_prod]
  exact ae_prod_of_velocity_windows (fun n =>
    (G.characteristic_frequency_integrable hf hi hT (Nat.cast_nonneg n)).2.prod_left_ae)

theorem GlobalCollisionLimit.flight_integrable_locally {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ T : ℝ, 0 ≤ T →
      Integrable (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 T)) ∧
      Integrable (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 T)) := by
  have hg : ∀ᵐ p ∂(volume : Measure Phase), ∀ n : ℕ,
      Integrable (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 (n:ℝ))) ∧
      Integrable (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
        (volume.restrict (Icc 0 (n:ℝ))) := by
    rw [ae_all_iff]
    intro n
    exact (G.gain_path_integrable_full_q80 hf hi (Nat.cast_nonneg n)).and
      (G.frequency_path_integrable_full hf hi (Nat.cast_nonneg n))
  filter_upwards [hg] with p hp
  intro T _hT
  obtain ⟨n,hn⟩ := exists_nat_ge T
  have hm : (volume : Measure ℝ).restrict (Icc 0 T) ≤ volume.restrict (Icc 0 (n:ℝ)) :=
    Measure.restrict_mono (Icc_subset_Icc le_rfl hn) le_rfl
  exact ⟨(hp n).1.mono_measure hm,(hp n).2.mono_measure hm⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual linear characteristic profile is a lower solution for the weak limit -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalLinearProfile_initial (f₀ : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (p : Phase) : physicalLinearProfile f₀ F (0,p) = f₀ p :=
  TransportPrimitive.linearSolution_initial _ _ _

theorem GlobalCollisionLimit.linear_profile_absolutelyContinuous
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ T : ℝ, 0 ≤ T →
      AbsolutelyContinuousOnInterval
        (fun t => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) 0 T := by
  filter_upwards [G.flight_integrable_locally hf hi] with p hp
  intro T hT
  have hk : IntervalIntegrable (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
      volume 0 T := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).2
  have hg : IntervalIntegrable (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))
      volume 0 T := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).1
  change AbsolutelyContinuousOnInterval
    (TransportPrimitive.linearSolution (f p)
      (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
      (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))) 0 T
  exact TransportPrimitive.linearSolution_absolutelyContinuous (f p) hk hg

theorem GlobalCollisionLimit.linear_profile_eq_source {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T L : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))),
      physicalLinearProfile f G.weakLimit.kineticProfile z =
        survivingInitial T f G.weakLimit.kineticProfile z+
          physicalFullPositiveSource T G.weakLimit.kineticProfile z := by
  have hfreq := (G.characteristic_frequency_integrable hf hi hT hL).2.prod_left_ae
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hfreq,
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz ht
  exact Published.linearSolution_eq_survival ht (f z.2)
    (physicalCharacteristicFrequency_nonneg (fun _ => G.weakLimit.nonnegative _)) _ z.2
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hz)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The linear characteristic lower profile has the physical forcing and loss -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalLinearProfile_nonneg {f : Density} (hf : ∀ p, 0 ≤ f p)
    {F : (ℝ × Position) × Velocity → ℝ} (hF : ∀ p, 0 ≤ F p)
    {t : ℝ} (ht : 0 ≤ t) (p : Phase) : 0 ≤ physicalLinearProfile f F (t,p) := by
  unfold physicalLinearProfile TransportPrimitive.linearSolution
  apply mul_nonneg (Real.exp_pos _).le
  apply add_nonneg (hf p)
  exact intervalIntegral.integral_nonneg ht (fun s _ =>
    mul_nonneg (Real.exp_pos _).le (physicalCharacteristicGain_nonneg hF _))

theorem GlobalCollisionLimit.linear_profile_hasDerivAt_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ T : ℝ, 0 ≤ T →
      ∀ᵐ t ∂volume, t ∈ Icc 0 T →
        HasDerivAt (fun s => physicalLinearProfile f G.weakLimit.kineticProfile (s,p))
          (physicalCharacteristicGain G.weakLimit.kineticProfile (t,p)-
            physicalCharacteristicFrequency G.weakLimit.kineticProfile (t,p)*
              physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) t := by
  filter_upwards [G.flight_integrable_locally hf hi] with p hp
  intro T hT
  have hk : IntervalIntegrable (fun s => physicalCharacteristicFrequency G.weakLimit.kineticProfile (s,p))
      volume 0 T := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).2
  have hg : IntervalIntegrable (fun s => physicalCharacteristicGain G.weakLimit.kineticProfile (s,p))
      volume 0 T := (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hp T hT).1
  simpa only [physicalLinearProfile] using
    TransportPrimitive.linearSolution_hasDerivAt_ae hT (f p) hk hg

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual linear lower profile is measurable and integrable on finite windows -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalFullPositiveSource_measurable (T : ℝ) {F : (ℝ × Position) × Velocity → ℝ}
    (hF : Measurable F) : Measurable (physicalFullPositiveSource T F) :=
  Published.survivalVolterra_measurable
    (Published.twoTimeSurvival_measurable (physicalCharacteristicFrequency_measurable hF))
    (physicalCharacteristicGain_measurable hF)

theorem GlobalCollisionLimit.linear_profile_eq_source_full {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    physicalLinearProfile f G.weakLimit.kineticProfile =ᵐ[(volume.restrict (Icc 0 T)).prod
      (volume : Measure Phase)] fun z => survivingInitial T f G.weakLimit.kineticProfile z+
        physicalFullPositiveSource T G.weakLimit.kineticProfile z :=
  ae_timePhase_of_velocity_windows (fun n => G.linear_profile_eq_source hf hi hT (Nat.cast_nonneg n))

theorem GlobalCollisionLimit.linear_profile_integrable {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (physicalLinearProfile f G.weakLimit.kineticProfile)
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hm : Measurable (fun z => survivingInitial T f G.weakLimit.kineticProfile z+
      physicalFullPositiveSource T G.weakLimit.kineticProfile z) :=
    ((Published.timeSurvival_measurable (physicalCharacteristicFrequency_measurable
      G.weakLimit.kineticProfile_measurable)).mul (hfm.comp measurable_snd)).add
        (physicalFullPositiveSource_measurable T G.weakLimit.kineticProfile_measurable)
  have hU : AEStronglyMeasurable (physicalLinearProfile f G.weakLimit.kineticProfile)
      (μ.prod (volume : Measure Phase)) :=
    hm.aestronglyMeasurable.congr (G.linear_profile_eq_source_full hf hi hT).symm
  have hdi := (G.weakLimit.weak_on_window hT).2.1
  have hflight : Integrable (fun z : ℝ × Phase => G.weakLimit.density
      (z.1,TorusFlight.flight z.1 z.2)) (μ.prod (volume : Measure Phase)) := by
    rw [Measure.volume_eq_prod] at hdi ⊢
    exact (TorusFlight.along_measurePreserving_velocity μ (volume : Measure Velocity)).integrable_comp_of_integrable hdi
  apply hflight.mono' hU
  filter_upwards [G.linear_profile_le_full_q80 hf hi hT,
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz ht
  have hn : 0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile z :=
    physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht.1 z.2
  rw [Real.norm_of_nonneg hn]
  exact hz

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Joint measurability of the actual linear characteristic profile -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalLinearProfile_measurable {f : Density} (hfm : Measurable f)
    {F : (ℝ × Position) × Velocity → ℝ} (hFm : Measurable F) :
    Measurable (physicalLinearProfile f F) := by
  have hk := physicalCharacteristicFrequency_measurable hFm
  have hg := physicalCharacteristicGain_measurable hFm
  have hK := TransportPrimitive.measurable_interval_primitive hk
  have hA := TransportPrimitive.measurable_interval_primitive (hK.exp.mul hg)
  exact hK.neg.exp.mul ((hfm.comp measurable_snd).add hA)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicLinearApproximation
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Comparing each positive approximation to the actual linear limit profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open TransportPrimitive

theorem linearComparisonError_measurable {N H : ℝ} {f₀ f : Density}
    (S : BoundedCutoffSolution N H f₀) (hfm : Measurable f)
    {F : (ℝ × Position) × Velocity → ℝ} (hFm : Measurable F) :
    Measurable (linearComparisonError S f F) := by
  have hum := S.measurable.comp (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hvm := (measurable_const (a := (0:ℝ))).max (physicalLinearProfile_measurable hfm hFm)
  exact ((((S.characteristicGain_measurable.sub (physicalCharacteristicGain_measurable hFm)).div
    ((measurable_const.add hum).add hvm)).abs).add
      ((S.characteristicLossDefect_measurable.div (measurable_const.add hum)).abs)).add
        (((physicalCharacteristicFrequency_measurable S.kineticProfile_measurable).sub
          (physicalCharacteristicFrequency_measurable hFm)).abs)

theorem linearComparisonError_nonneg {N H : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N H f₀) (f : Density)
    (F : (ℝ × Position) × Velocity → ℝ) (z : ℝ × Phase) :
    0 ≤ linearComparisonError S f F z :=
  add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)

theorem GlobalCollisionLimit.positive_linear_comparison
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {N H : ℝ} {f₀ : Density} (S : BoundedCutoffSolution N H f₀) (hN : 0 < N) :
    ∀ᵐ p ∂(volume : Measure Phase), ∀ t ∈ Icc 0 H,
      |positiveDifference (S.density (t,TorusFlight.flight t p))
        (physicalLinearProfile f G.weakLimit.kineticProfile (t,p))| ≤
      |positiveDifference (f₀ p) (f p)|+
        ∫ r in 0..t, linearComparisonError S f G.weakLimit.kineticProfile (r,p) := by
  filter_upwards [G.flight_integrable_locally hf hi,
    G.linear_profile_absolutelyContinuous hf hi,G.linear_profile_hasDerivAt_ae hf hi]
    with p hp hac hd
  intro t ht
  let U := fun r => physicalLinearProfile f G.weakLimit.kineticProfile (r,p)
  have hs r (hr : r ∈ Icc 0 t) : S.dampedPath p r = S.density (r,TorusFlight.flight r p) :=
    S.dampedPath_eq ⟨hr.1,hr.2.trans ht.2⟩ p
  have hsu r (hr : r ∈ Icc 0 t) : 0 ≤ S.dampedPath p r := by rw [hs r hr]; exact S.nonnegative _
  have hu r (hr : r ∈ Icc 0 t) : 0 ≤ U r :=
    physicalLinearProfile_nonneg hf (fun _ => G.weakLimit.nonnegative _) hr.1 p
  have hgi := (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr (hp t ht.1).1
  have hki := (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr (hp t ht.1).2
  have hdu : ∀ᵐ r, r ∈ Icc 0 t → HasDerivAt U
      (physicalCharacteristicGain G.weakLimit.kineticProfile (r,p)-
        physicalCharacteristicFrequency G.weakLimit.kineticProfile (r,p)*U r+0) r := by
    simpa only [add_zero] using hd t ht.1
  have hh := positiveDifference_error_bound ht.1
    (S.dampedPath_absolutelyContinuous hN p t) (hac t ht.1) hsu hu
    (fun r _ => (gain_bounds hN S.kineticProfile_measurable (fun _ => S.nonnegative _) _).1)
    (fun r _ => physicalCharacteristicGain_nonneg (fun _ => G.weakLimit.nonnegative _) (r,p))
    (fun r _ => physicalCharacteristicFrequency_nonneg (fun _ => S.nonnegative _) (r,p))
    (fun r _ => physicalCharacteristicFrequency_nonneg (fun _ => G.weakLimit.nonnegative _) (r,p))
    (fun r _ => S.characteristicLossDefect_nonneg hN (r,p))
    (fun _ _ => le_refl 0)
    (S.gain_path_integrable hN p t) hgi (S.frequency_path_integrable hN.le p t) hki
    (S.lossDefect_path_integrable hN p t) intervalIntegrable_const
    (S.dampedPath_physical_derivative hN ht p) hdu
  rw [hs t ⟨ht.1,le_rfl⟩,S.dampedPath_initial,physicalLinearProfile_initial] at hh
  apply hh.trans_eq
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hr' : r ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hr
  dsimp only [linearComparisonError]
  rw [hs r hr',max_eq_right (hu r hr'),abs_div,
    abs_of_pos (show 0 < 1+S.density (r,TorusFlight.flight r p)+U r by
      have := S.nonnegative (r,TorusFlight.flight r p); have := hu r hr'; positivity)]
  rw [abs_of_nonneg (div_nonneg (S.characteristicLossDefect_nonneg hN (r,p)) (by
    have := S.nonnegative (r,TorusFlight.flight r p); positivity))]
  simp only [zero_div,add_zero]
  rfl

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The approximations approach the linear profile in the positive metric -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness TransportPrimitive

theorem GlobalCollisionLimit.linear_positive_difference_L1
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    let I := fun n => G.weakLimit.indices (n+Nat.ceil T)
    Tendsto (fun n => eLpNorm (fun z : ℝ × Phase => positiveDifference
      ((approximatingSolution f hfm (I n)).density (z.1,TorusFlight.flight z.1 z.2))
      (max 0 (physicalLinearProfile f G.weakLimit.kineticProfile z))) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  let I := fun n => G.weakLimit.indices (n+Nat.ceil T)
  let S := fun n => approximatingSolution f hfm (I n)
  let u n (z : ℝ × Phase) := (S n).density (z.1,TorusFlight.flight z.1 z.2)
  let v := fun z => max 0 (physicalLinearProfile f G.weakLimit.kineticProfile z)
  let E n := linearComparisonError (S n) f G.weakLimit.kineticProfile
  let d n (p : Phase) := |positiveDifference (initialApproximation ((I n:ℝ)+1) f p) (f p)|
  have hum n : Measurable (u n) := (S n).measurable.comp
    (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hvm : Measurable v := measurable_const.max
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable)
  have hdm n : Measurable (d n) :=
    (((initialApproximation_measurable _ hfm).sub hfm).div
      ((measurable_const.add (initialApproximation_measurable _ hfm)).add hfm)).abs
  have hν : (volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)) ≤ (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  have hdt := initialApproximation_linear_comparison_L1 hfm hf
    (integrable_of_entropyGauge hfm hf hi)
    (G.weakLimit.increasing.tendsto_atTop.comp (tendsto_add_atTop_nat (Nat.ceil T))) hν
  apply prefixComparison_ae_strongL1 hT
    (fun n => ((hum n).sub hvm).div ((measurable_const.add (hum n)).add hvm))
    (fun n => linearComparisonError_measurable (S n) hfm G.weakLimit.kineticProfile_measurable)
    hdm (fun n z => linearComparisonError_nonneg (S n) f G.weakLimit.kineticProfile z)
    _ hdt (G.linear_comparison_error_L1_q80 hf hi hT hR)
  intro n
  have hp := (G.positive_linear_comparison hf hi (S n) (by positivity)).filter_mono (ae_mono hν)
  filter_upwards [hp] with p hp
  intro t ht
  have hIc : Nat.ceil T ≤ I n :=
    (Nat.le_add_left (Nat.ceil T) n).trans (G.weakLimit.increasing.id_le _)
  have hIT : T ≤ (I n:ℝ)+1 := by
    have hc := Nat.le_ceil T
    have hn : (Nat.ceil T:ℝ) ≤ (I n:ℝ) := by exact_mod_cast hIc
    linarith
  have hv : 0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile (t,p) :=
    physicalLinearProfile_nonneg hf (fun _ => G.weakLimit.nonnegative _) ht.1 p
  change |positiveDifference _ (max 0 (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)))| ≤ _
  rw [max_eq_right hv]
  exact hp t ⟨ht.1,ht.2.trans hIT⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong approximation of the physical linear characteristic profile -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.linear_profile_approximation_L1
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    let I := fun n => G.weakLimit.indices (n+Nat.ceil T)
    Tendsto (fun n => eLpNorm (fun z : ℝ × Phase =>
      (approximatingSolution f hfm (I n)).density (z.1,TorusFlight.flight z.1 z.2)-
        max 0 (physicalLinearProfile f G.weakLimit.kineticProfile z)) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  let I := fun n => G.weakLimit.indices (n+Nat.ceil T)
  let S := fun n => approximatingSolution f hfm (I n)
  let u n (z : ℝ × Phase) := (S n).density (z.1,TorusFlight.flight z.1 z.2)
  let v := fun z => max 0 (physicalLinearProfile f G.weakLimit.kineticProfile z)
  let μ : Measure (ℝ × Phase) := (volume.restrict (Icc 0 T)).prod
    ((volume : Measure Position).prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))
  have hum n : Measurable (u n) := (S n).measurable.comp
    (measurable_fst.prodMk TorusFlight.measurable_flight)
  have hvm : Measurable v := measurable_const.max
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable)
  have hbase := uniformIntegrable_restrict
    (uniformIntegrable_comp (approximatingSolution_compactness_hypotheses f hfm hf hi
      (volume.restrict (Icc 0 T))).1 I) (univ ×ˢ Metric.closedBall (0:Velocity) R)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hbase
  have hui0 := TorusFlight.uniformIntegrable_along_regroup_local
      (μ := volume.restrict (Icc 0 T))
      (ν := (volume : Measure Velocity).restrict (Metric.closedBall 0 R))
      (f := fun n => (S n).kineticProfile)
      (fun n => (S n).kineticProfile_measurable) hbase
  have he : (fun n => TorusFlight.along (TorusFlight.regroup (S n).kineticProfile)) = u := by
    funext n z
    rfl
  rw [he] at hui0
  have hui : UniformIntegrable u 1 μ := hui0
  have hμ : μ ≤ (volume.restrict (Icc 0 T)).prod (volume : Measure Phase) := by
    rw [Measure.volume_eq_prod]
    exact Measure.prod_mono le_rfl (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hvInt : Integrable v μ := by
    apply ((G.linear_profile_integrable hf hi hT).mono_measure hμ).congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z hz
    exact (max_eq_right (physicalLinearProfile_nonneg hf
      (fun _ => G.weakLimit.nonnegative _) hz.1 z.2)).symm
  have hvi : UniformIntegrable (fun _ : ℕ => v) 1 μ :=
    uniformIntegrable_const (by norm_num) (by norm_num) (memLp_one_iff_integrable.mpr hvInt)
  exact positiveDifference_L1 hum (fun _ => hvm)
    (fun n z => (S n).nonnegative _) (fun _ z => le_max_left _ _) hui hvi
    (G.linear_positive_difference_L1 hf hi hT hR)

theorem GlobalCollisionLimit.characteristic_density_strong
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (fun z : ℝ × Phase =>
      (approximatingSolution f hfm (G.weakLimit.indices n)).density (z.1,TorusFlight.flight z.1 z.2)-
        G.weakLimit.density (z.1,TorusFlight.flight z.1 z.2)) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) := by
  have hh := TorusFlight.strong_along_regroup
    (μ := volume.restrict (Icc 0 T))
    (ν := (volume : Measure Velocity).restrict (Metric.closedBall 0 R))
    (f := fun n => (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
    (g := G.weakLimit.kineticProfile)
    (fun n => (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    G.weakLimit.kineticProfile_measurable (G.density_strong hf hi hT hR)
  apply hh.congr'
  exact Eventually.of_forall (fun n => rfl)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalEvolution
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual global density equals its nonlinear characteristic profile -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_profile_eq_density_local
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))),
      physicalLinearProfile f G.weakLimit.kineticProfile z =
        G.weakLimit.density (z.1,TorusFlight.flight z.1 z.2) := by
  have hU := tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
    (by norm_num : (1:ℝ≥0∞) ≠ 0) (by norm_num : (1:ℝ≥0∞) ≠ ∞)
    (fun n => by exact ((approximatingSolution f hfm _).measurable.comp (measurable_fst.prodMk TorusFlight.measurable_flight)).aestronglyMeasurable)
    (by exact (measurable_const.max (physicalLinearProfile_measurable hfm
      G.weakLimit.kineticProfile_measurable)).aestronglyMeasurable)
    (G.linear_profile_approximation_L1 hf hi hT hR)
  have hF := tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
    (by norm_num : (1:ℝ≥0∞) ≠ 0) (by norm_num : (1:ℝ≥0∞) ≠ ∞)
    (fun n => by exact ((approximatingSolution f hfm _).measurable.comp (measurable_fst.prodMk TorusFlight.measurable_flight)).aestronglyMeasurable)
    (by exact (G.weakLimit.measurable.comp (measurable_fst.prodMk TorusFlight.measurable_flight)).aestronglyMeasurable)
    ((G.characteristic_density_strong hf hi hT hR).comp (tendsto_add_atTop_nat (Nat.ceil T)))
  have he := tendstoInMeasure_ae_unique hU hF
  filter_upwards [he,Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem measurableSet_Icc)] with z hz ht
  have hpos : 0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile z :=
    physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht.1 z.2
  rw [max_eq_right hpos] at hz
  exact hz

theorem GlobalCollisionLimit.linear_profile_eq_density_q80_oai
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase),
      physicalLinearProfile f G.weakLimit.kineticProfile z =
        G.weakLimit.density (z.1,TorusFlight.flight z.1 z.2) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hall : ∀ᵐ z ∂(μ.prod (volume : Measure Position)).prod (volume : Measure Velocity),
      physicalLinearProfile f G.weakLimit.kineticProfile (z.1.1,(z.1.2,z.2)) =
        G.weakLimit.density (z.1.1,TorusFlight.flight z.1.1 (z.1.2,z.2)) := by
    apply ae_prod_of_velocity_windows
    intro n
    exact (measurePreserving_prodAssoc μ (volume : Measure Position)
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 (n:ℝ)))).quasiMeasurePreserving.ae
      (G.linear_profile_eq_density_local hf hi hT (Nat.cast_nonneg n))
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_prodAssoc μ (volume : Measure Position)
    (volume : Measure Velocity)).symm.quasiMeasurePreserving.ae hall

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_profile_eq_density_q80_oai := @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.linear_profile_eq_density_q80_oai
