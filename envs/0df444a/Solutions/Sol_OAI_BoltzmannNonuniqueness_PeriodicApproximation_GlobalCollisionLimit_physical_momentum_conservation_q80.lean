-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_momentum_conservation_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:21:07.645509+00:00
-- url     : https://prove2.me/submissions/923cf635-c403-42c5-8d3f-75745be9351f

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_GlobalCollisionLimit_gain_path_integrable_full_q80
import Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_GlobalCollisionLimit_linear_profile_eq_density_q80

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

theorem unifTight_iff_mathlib : UnifTight f p μ ↔ MeasureTheory.UnifTight f p μ :=
  (MeasureTheory.unifTight_iff_ennreal f p μ).symm

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

end UnifIntegrable

/-! ### `UniformIntegrable` -/

theorem uniformIntegrable_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : MemLp g p μ) :
    UniformIntegrable (fun _ : ι => g) p μ :=
  uniformIntegrable_iff_mathlib.2 (MeasureTheory.uniformIntegrable_const hp hp_ne_top hg)


/-! ### `UnifTight` -/

namespace UnifTight

theorem toMathlib (hf : UnifTight f p μ) : MeasureTheory.UnifTight f p μ :=
  unifTight_iff_mathlib.1 hf

end UnifTight

theorem tendsto_Lp_of_tendsto_ae (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (haef : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg' : MemLp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) p μ) atTop (𝓝 0) :=
  MeasureTheory.tendsto_Lp_of_tendsto_ae hp hp' haef hg' hui.1 hut.toMathlib hfg

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

/-! # A vanishing L1 norm error preserves the same weak limit -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.of_eLpNorm_sub
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f h : ℕ → X → ℝ} {g : X → ℝ}
    (hg : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ)
    (hh : ∀ n, Integrable (h n) μ)
    (herr : Tendsto (fun n => eLpNorm (fun x => h n x-f n x) 1 μ) atTop (𝓝 0)) :
    WeakL1Converges μ h g := by
  apply hg.of_integral_abs_sub hf hh
  have he n : (∫ x, |h n x-f n x| ∂μ) =
      (eLpNorm (fun x => h n x-f n x) 1 μ).toReal := by
    change (∫ x, ‖(h n-f n) x‖ ∂μ) = (eLpNorm (h n-f n) 1 μ).toReal
    rw [eLpNorm_one_eq_lintegral_enorm,
      integral_norm_eq_lintegral_enorm ((hh n).sub (hf n)).aestronglyMeasurable]
  simp only [he]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp herr

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak velocity-average limits and their identification with strong limits -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private theorem integral_test_marginal {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {u k : X × Y → ℝ} (hu : Integrable u (μ.prod ν))
    (hk : Measurable k) (C : ℝ) (hC : ∀ z, |k z| ≤ C)
    {ψ : X → ℝ} (hψ : Measurable ψ) (D : ℝ) (hD : ∀ x, |ψ x| ≤ D) :
    (∫ x, ψ x*(∫ y, k (x,y)*u (x,y) ∂ν) ∂μ) =
      ∫ z, (ψ z.1*k z)*u z ∂μ.prod ν := by
  have hku := hu.bdd_mul hk.aestronglyMeasurable (ae_of_all _ hC)
  have hi := hku.bdd_mul (hψ.comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => hD z.1))
  change Integrable (fun z : X × Y => ψ z.1*(k z*u z)) (μ.prod ν) at hi
  calc
    _ = ∫ z, ψ z.1*(k z*u z) ∂μ.prod ν := by
      rw [integral_prod _ hi]
      simp_rw [integral_const_mul]
    _ = _ := by congr 1; ext z; ring

theorem WeakL1Converges.marginal {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (h : WeakL1Converges (μ.prod ν) f g) (hf : ∀ n, Integrable (f n) (μ.prod ν))
    {k : X × Y → ℝ} (hk : Measurable k) (C : ℝ) (hC : ∀ z, |k z| ≤ C) :
    WeakL1Converges μ (fun n x => ∫ y, k (x,y)*f n (x,y) ∂ν)
      (fun x => ∫ y, k (x,y)*g (x,y) ∂ν) := by
  have hkg := h.2.1.bdd_mul hk.aestronglyMeasurable (ae_of_all _ hC)
  refine ⟨(hk.mul h.1).stronglyMeasurable.integral_prod_right'.measurable,
    hkg.integral_prod_left,?_⟩
  intro ψ hψ hB
  obtain ⟨D,hD⟩ := hB
  have htest : Measurable (fun z : X × Y => ψ z.1*k z) :=
    (hψ.comp measurable_fst).mul hk
  have htestB : ∃ B : ℝ, ∀ z : X × Y, |ψ z.1*k z| ≤ B := by
    refine ⟨|D| * |C|,fun z => ?_⟩
    rw [abs_mul]
    exact mul_le_mul ((hD z.1).trans (le_abs_self D)) ((hC z).trans (le_abs_self C))
      (abs_nonneg _) (abs_nonneg _)
  have ht := h.2.2 _ htest htestB
  simpa only [← integral_test_marginal (hf _) hk C hC hψ D hD,
    ← integral_test_marginal h.2.1 hk C hC hψ D hD] using ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Bounded multipliers and uniqueness for weak L¹ limits -/

noncomputable section

open MeasureTheory Filter Set

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.bounded_mul {μ : Measure X} {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) {a : X → ℝ} (ha : Measurable a)
    (C : ℝ) (hC : ∀ x, |a x| ≤ C) :
    WeakL1Converges μ (fun n x => a x*f n x) (fun x => a x*g x) := by
  refine ⟨ha.mul h.1,h.2.1.bdd_mul ha.aestronglyMeasurable (ae_of_all _ hC),?_⟩
  intro ψ hψ hB
  obtain ⟨D,hD⟩ := hB
  have hm := hψ.mul ha
  have hb : ∃ B : ℝ, ∀ x, |ψ x*a x| ≤ B := by
    refine ⟨|D| * |C|,fun x => ?_⟩
    rw [abs_mul]
    exact mul_le_mul ((hD x).trans (le_abs_self D)) ((hC x).trans (le_abs_self C))
      (abs_nonneg _) (abs_nonneg _)
  simpa only [mul_assoc] using h.2.2 (fun x => ψ x*a x) hm hb

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

/-! # Linear operations on weak L¹ limits -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.congr_sequence {μ : Measure X} {f k : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (he : ∀ n, f n =ᵐ[μ] k n) :
    WeakL1Converges μ k g := by
  refine ⟨h.1,h.2.1,?_⟩
  intro ψ hψ hB
  have ht := h.2.2 ψ hψ hB
  have hi n : (∫ x, ψ x*f n x ∂μ) = ∫ x, ψ x*k n x ∂μ :=
    integral_congr_ae ((he n).mono (fun x hx => congrArg (fun y => ψ x*y) hx))
  simpa only [hi] using ht

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

theorem WeakL1Converges.restrict_base {Y : Type*} [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (h : WeakL1Converges (μ.prod ν) f g) {s : Set X} (hs : MeasurableSet s) :
    WeakL1Converges ((μ.restrict s).prod ν) f g := by
  have ht := h.restrict (hs.prod MeasurableSet.univ)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at ht
  exact ht

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_VaryingBoundedMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Multiplication by a varying uniformly bounded function preserves L1 smallness -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

theorem tendsto_L1_bounded_mul_zero
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f a : ℕ → X → ℝ} (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (ham : ∀ n, AEStronglyMeasurable (a n) μ)
    (hf : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0))
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, |a n x| ≤ C) :
    Tendsto (fun n => eLpNorm (fun x => a n x*f n x) 1 μ) atTop (𝓝 0) := by
  have hscale : Tendsto (fun n => eLpNorm (fun x => C*f n x) 1 μ) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ) hf
      (Or.inr (by simp : ‖C‖ₑ ≠ ⊤))
    simpa only [← eLpNorm_const_smul,Pi.smul_def,smul_eq_mul,mul_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hscale
    (Filter.Eventually.of_forall (fun _ => bot_le)) ?_
  filter_upwards [ha] with n hn
  apply eLpNorm_mono_ae
  filter_upwards [hn] with x hx
  change |a n x*f n x| ≤ |C*f n x|
  rw [abs_mul,abs_mul,abs_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

end BoltzmannNonuniqueness.Compactness

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

/-! # Bounded measurable multipliers preserve uniform integrability -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_of_bounded_multiplier
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℝ}
    (hf : UniformIntegrable f 1 μ) {a : X → ℝ} (ha : Measurable a)
    (C : ℝ≥0) (hC : ∀ x, |a x| ≤ C) :
    UniformIntegrable (fun n x => a x*f n x) 1 μ := by
  let D : ℝ≥0 := C+1
  have hD : (0 : ℝ≥0∞) < D := by simp [D]
  have hb (n : ℕ) (ν : Measure X) (hν : ν ≤ μ) :
      eLpNorm (fun x => a x*f n x) 1 ν ≤ (D : ℝ≥0∞)*eLpNorm (f n) 1 ν := by
    apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    filter_upwards [] with x
    apply NNReal.coe_le_coe.mp
    change ‖a x*f n x‖ ≤ (D:ℝ)*‖f n x‖
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_mul]
    exact mul_le_mul_of_nonneg_right ((hC x).trans (by dsimp [D] <;> norm_num)) (abs_nonneg _)
  constructor
  · apply OAI.UnifIntegrable.of_enn
    intro ε hε
    obtain ⟨δ,hδ,hδsmall⟩ := OAI.UnifIntegrable.enn_spec hf.1 (ε/(D:ℝ≥0∞))
      (ENNReal.div_pos hε.ne' ENNReal.coe_ne_top)
    refine ⟨δ,hδ,fun n s hs => ?_⟩
    calc
      _ ≤ (D:ℝ≥0∞)*eLpNorm (f n) 1 (μ.restrict s) := hb n _ Measure.restrict_le_self
      _ ≤ (D:ℝ≥0∞)*(ε/(D:ℝ≥0∞)) := mul_le_mul' le_rfl (hδsmall n s hs)
      _ = ε := ENNReal.mul_div_cancel hD.ne' ENNReal.coe_ne_top
    exact fun n => ha.aestronglyMeasurable.mul (hf.aestronglyMeasurable n)
  · obtain ⟨B,hB⟩ := hf.2
    refine ⟨D*B,fun n => ?_⟩
    exact (hb n μ le_rfl).trans (by simpa only [ENNReal.coe_mul] using mul_le_mul' le_rfl (hB n))

end BoltzmannNonuniqueness.Compactness

end

end

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

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedKernelAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Conditional tensor products controlled by a single mass marginal -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem normalizedTensor_measurable {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hf : Measurable f) (hg : Measurable g) :
    Measurable (normalizedTensor d f g) := by
  unfold normalizedTensor
  fun_prop

omit [MeasurableSpace X] in
theorem normalizedTensor_fiber_integral {d : X → ℝ} {f g : X × Y → ℝ} (x : X) :
    (∫ y, normalizedTensor d f g (x,y) ∂ν.prod ν) =
      (∫ v, f (x,v) ∂ν)*(∫ w, g (x,w) ∂ν)/(1+d x) := by
  simp only [normalizedTensor,integral_div]
  rw [integral_prod_mul (fun v => f (x,v)) (fun w => g (x,w))]

theorem normalizedTensor_integrable {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (hfi : Integrable f (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (hfd : ∀ᵐ x ∂μ, (∫ v, f (x,v) ∂ν) ≤ d x) :
    Integrable (normalizedTensor d f g) (μ.prod (ν.prod ν)) := by
  have hnon (z : X × (Y × Y)) : 0 ≤ normalizedTensor d f g z :=
    div_nonneg (mul_nonneg (hf _) (hg _)) (by linarith [hd0 z.1])
  have hnorm x : (∫ y, ‖normalizedTensor d f g (x,y)‖ ∂ν.prod ν) =
      (∫ v, f (x,v) ∂ν)*(∫ w, g (x,w) ∂ν)/(1+d x) := by
    simp only [Real.norm_of_nonneg (hnon _)]
    exact normalizedTensor_fiber_integral x
  apply (integrable_prod_iff (normalizedTensor_measurable hd hfm hgm).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hfi.prod_right_ae,hgi.prod_right_ae] with x hfx hgx
    exact (hfx.mul_prod hgx).div_const (1+d x)
  · apply hgi.integral_prod_left.mono'
      ((normalizedTensor_measurable hd hfm hgm).norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    filter_upwards [hfd] with x hx
    rw [hnorm,Real.norm_of_nonneg (div_nonneg
      (mul_nonneg (integral_nonneg (μ := ν) (f := fun v => f (x,v)) (fun v => hf (x,v))) (integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v))))
      (by linarith [hd0 x]))]
    apply (div_le_iff₀ (by linarith [hd0 x] : 0 < 1+d x)).mpr
    nlinarith [integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v)),
      mul_le_mul_of_nonneg_right hx (integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v)))]

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Truncating a mass-normalized velocity pair costs only its L1 tail -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem fiberMass_measurable {f : X × Y → ℝ} (hf : Measurable f) :
    Measurable (fiberMass ν f) := hf.stronglyMeasurable.integral_prod_right'.measurable

theorem normalizedPair_integrable {f : X × Y → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) (hfi : Integrable f (μ.prod ν)) :
    Integrable (normalizedPair ν f) (μ.prod (ν.prod ν)) :=
  normalizedTensor_integrable (fiberMass_measurable hfm)
    (fun x => integral_nonneg (fun v => hf (x,v))) hfm hfm hf hf hfi hfi
    (ae_of_all _ (fun _ => le_rfl))

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

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_r5d6542_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
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

end BoltzmannNonuniqueness.CollisionCompactness

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

/-! # The mass, momentum, and energy collision invariants -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem collisionJump_momentum (i : Fin 3) (z : (X × (Velocity × Velocity)) × Sphere) :
    collisionJump (fun p : X × Velocity => p.2 i) z = 0 := by
  have h := congrArg (fun v : Velocity => v i) (scatter_momentum z.1.2.1 z.1.2.2 z.2)
  change (scatterLeft z.1.2.1 z.1.2.2 z.2) i+
    (scatterRight z.1.2.1 z.1.2.2 z.2) i = z.1.2.1 i+z.1.2.2 i at h
  change (scatterLeft z.1.2.1 z.1.2.2 z.2) i+
    (scatterRight z.1.2.1 z.1.2.2 z.2) i-z.1.2.1 i-z.1.2.2 i = 0
  linarith

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteDepthKernelOrder
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Recovering the finite absolute-entropy datum class from relative entropy -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

theorem FiniteEntropyDatum.of_relativeEntropy_integrable {f : Density}
    (hn : ∀ᵐ z, 0 ≤ f z) (hf : Integrable f)
    (hE : Integrable (fun z => ‖z.2‖^2*f z))
    (hH : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z))) :
    FiniteEntropyDatum f := by
  have hlog : Integrable (fun z => f z*Real.log (f z)) := by
    have h := ((hH.add (hf.const_mul (1-(3/2:ℝ)*Real.log (2*Real.pi)))).sub
      (hE.const_mul (1/2:ℝ))).sub integrable_maxwellian_phase
    apply h.congr
    filter_upwards [] with z
    simp only [Pi.sub_apply,Pi.add_apply,scalarRelativeEntropy,log_maxwellian]
    ring
  refine ⟨hn,hf.aestronglyMeasurable,?_⟩
  apply ((hf.add hE).add hlog.norm).congr
  filter_upwards [hn] with z hz
  simp only [Pi.add_apply,Real.norm_eq_abs,abs_mul,abs_of_nonneg hz,entropyMoment]
  ring

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

theorem entropyGauge_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (entropyGauge f) :=
  hf.mul ((measurable_const.add (measurable_snd.norm.pow_const 2)).add hf.log.abs)

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

/-! # Free transport preserves strong L1 continuity of an integrable curve -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.TorusFlight

theorem strong_curve_flight {T : ℝ} {C : ℝ → Density}
    (hC : ∀ s ∈ Icc 0 T, Integrable (C s)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hc : Tendsto (fun s => eLpNorm (fun p => C s p-C t p) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0)) :
    Tendsto (fun s => eLpNorm (fun p => C s (flight (-s) p)-C t (flight (-t) p)) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hneg : Tendsto (fun s : ℝ => -s) (𝓝[Icc 0 T] t) (𝓝 (-t)) :=
    continuous_neg.continuousAt.tendsto.mono_left inf_le_left
  have hfixed := (tendsto_flight_L1 (hC t ht) (-t)).comp hneg
  have hu := hc.add hfixed
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Filter.Eventually.of_forall (fun _ => zero_le))
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hdiff : Integrable (fun p => C s p-C t p) := (hC s hs).sub (hC t ht)
  have hi := eLpNorm_comp_measurePreserving hdiff.aestronglyMeasurable
    (flight_measurePreserving (-s)) (p := 1)
  have he : (fun p => C s (flight (-s) p)-C t (flight (-t) p)) =
      (fun p => C s (flight (-s) p)-C t (flight (-s) p))+
        (fun p => C t (flight (-s) p)-C t (flight (-t) p)) := by
    funext p
    simp only [Pi.add_apply]
    ring
  rw [he]
  apply (eLpNorm_add_le
    (hf := hdiff.aestronglyMeasurable.comp_measurePreserving (flight_measurePreserving (-s)))
    (hg := ((hC t ht).1.comp_measurePreserving (flight_measurePreserving (-s))).sub
      ((hC t ht).1.comp_measurePreserving (flight_measurePreserving (-t)))) (by norm_num : (1:ℝ≥0∞) ≤ 1)).trans
  exact add_le_add hi.le le_rfl

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # Entropy moments under free transport on the torus -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness

theorem FiniteEntropyDatum.comp_flight {f : Density} (hf : FiniteEntropyDatum f) (t : ℝ) :
    FiniteEntropyDatum (fun p => f (TorusFlight.flight t p)) := by
  have hmp := TorusFlight.flight_measurePreserving t
  refine ⟨hmp.quasiMeasurePreserving.ae hf.1,
    hf.2.1.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving,?_⟩
  have he : entropyMoment (fun p => f (TorusFlight.flight t p)) =
      (entropyMoment f) ∘ TorusFlight.flight t := rfl
  rw [he]
  exact hmp.integrable_comp_of_integrable hf.2.2

theorem TorusFlight.entropyMoment_integral_comp {f : Density} (hfm : Measurable f) (t : ℝ) :
    (∫ p, entropyMoment (fun q => f (TorusFlight.flight t q)) p) = ∫ p, entropyMoment f p := by
  exact Published.integral_comp_measurePreserving (TorusFlight.flight_measurePreserving t)
    (PeriodicApproximation.entropyGauge_measurable hfm)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_VelocityCutoffEntropyError
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

theorem velocityLinearCut_measurable (R : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (velocityLinearCut R f) := (linearMoment_measurable hf).ite
      (measurableSet_le measurable_snd.norm measurable_const) measurable_const

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

omit [MeasurableSpace X] in
theorem velocityLinearCut_error {R : ℝ} (hR : 0 < R) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    |linearMoment f p-velocityLinearCut R f p| ≤ 2*entropyGauge f p/R := by
  by_cases hp : ‖p.2‖ ≤ R
  · simp only [velocityLinearCut,ite_eq_left hp,sub_self,abs_zero]
    exact div_nonneg (mul_nonneg (by norm_num) (entropyGauge_nonneg hf p)) hR.le
  · have hr : R ≤ ‖p.2‖ := (lt_of_not_ge hp).le
    simp only [velocityLinearCut,ite_eq_right hp,sub_zero,linearMoment]
    rw [abs_of_nonneg (mul_nonneg (by positivity) (hf p))]
    apply (le_div_iff₀ hR).mpr
    have hcoeff : (1+‖p.2‖)*R ≤ 2*(1+‖p.2‖^2+|Real.log (f p)|) := by
      have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1+‖p.2‖ by positivity)
      nlinarith [sq_nonneg (‖p.2‖-1),abs_nonneg (Real.log (f p))]
    simpa only [entropyGauge,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_right hcoeff (hf p)

theorem velocityLinearCut_integrable {μ : Measure (X × Velocity)} (R : ℝ)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) μ) : Integrable (velocityLinearCut R f) μ := by
  apply (linearMoment_integrable hfm hf hi).mono'
    (velocityLinearCut_measurable R hfm).aestronglyMeasurable
  filter_upwards [] with p
  have hn : 0 ≤ linearMoment f p := mul_nonneg (by positivity) (hf p)
  by_cases hp : ‖p.2‖ ≤ R
  · rw [velocityLinearCut,ite_eq_left hp,Real.norm_of_nonneg hn]
  · rw [velocityLinearCut,ite_eq_right hp,norm_zero]
    exact hn

theorem velocityLinearCut_L1_error {μ : Measure (X × Velocity)} {R C : ℝ} (hR : 0 < R)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) μ) (hb : (∫ p, entropyGauge f p ∂μ) ≤ C) :
    eLpNorm (fun p => linearMoment f p-velocityLinearCut R f p) 1 μ ≤ ENNReal.ofReal (2*C/R) := by
  have he := (linearMoment_integrable hfm hf hi).sub (velocityLinearCut_integrable R hfm hf hi)
  change Integrable (fun p => linearMoment f p-velocityLinearCut R f p) μ at he
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm he]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∫ p, 2*entropyGauge f p/R ∂μ :=
      integral_mono he.norm ((hi.const_mul 2).div_const R) (fun p => by
        simpa only [Real.norm_eq_abs] using velocityLinearCut_error hR hf p)
    _ = 2*(∫ p, entropyGauge f p ∂μ)/R := by rw [integral_div,integral_const_mul]
    _ ≤ 2*C/R := div_le_div_of_nonneg_right (by linarith) hR.le

theorem linearMoment_uniformIntegrable {μ : Measure X} [IsFiniteMeasure μ]
    {f : ℕ → X × Velocity → ℝ} {C : ℝ} (hfm : ∀ n, Measurable (f n))
    (hf : ∀ n p, 0 ≤ f n p) (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n => linearMoment (f n)) 1 (μ.prod volume) := by
  have hui := uniformIntegrable_of_entropyGauge hfm hf hi hb
  apply Compactness.uniformIntegrable_of_approximation (g := fun j n => velocityLinearCut ((j:ℝ)+1) (f n))
  · intro j
    let a : X × Velocity → ℝ := fun p => if ‖p.2‖ ≤ (j:ℝ)+1 then 1+‖p.2‖ else 0
    have ha : Measurable a := (measurable_const.add measurable_snd.norm).ite
      (measurableSet_le measurable_snd.norm measurable_const) measurable_const
    let D : ℝ≥0 := ⟨(j:ℝ)+2,by positivity⟩
    have hD (p : X × Velocity) : |a p| ≤ D := by
      change |if ‖p.2‖ ≤ (j:ℝ)+1 then 1+‖p.2‖ else 0| ≤ (j:ℝ)+2
      split_ifs with hp
      · rw [abs_of_nonneg (by positivity)]
        linarith
      · simp only [abs_zero]
        positivity
    change UniformIntegrable (fun n p => if ‖p.2‖ ≤ (j:ℝ)+1 then
      (1+‖p.2‖)*f n p else 0) 1 (μ.prod volume)
    simpa only [a,ite_mul,zero_mul] using
      Compactness.uniformIntegrable_of_bounded_multiplier hui ha D hD
  · intro ε hε
    obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (2*C) hε
    exact ⟨j,fun n => (velocityLinearCut_L1_error (by positivity) (hfm n) (hf n) (hi n) (hb n)).trans hj⟩
  · exact fun n => (linearMoment_measurable (hfm n)).aestronglyMeasurable

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_L1TruncationCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Limits of the truncations and their uniform L¹ distance bounds -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℝ}

theorem integral_abs_le_of_eLpNorm_le {v : X → ℝ} (hv : Integrable v μ)
    {B : ℝ} (hB : 0 ≤ B) (he : eLpNorm v 1 μ ≤ ENNReal.ofReal B) :
    ∫ x, |v x| ∂μ ≤ B := by
  have hh : ENNReal.ofReal (∫ x, |v x| ∂μ) = eLpNorm v 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    simpa only [Real.norm_eq_abs] using ofReal_integral_norm_eq_lintegral_enorm hv
  rw [← hh] at he
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp he

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedL1Tests
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuity and norm bounds for bounded measurable L¹ tests -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem abs_integral_bounded_mul (v : X → ℝ) (hv : Integrable v μ)
    (ψ : X → ℝ) (hψ : Measurable ψ) (C : ℝ≥0) (hC : ∀ x, ‖ψ x‖ ≤ C) :
    |∫ x, ψ x*v x ∂μ| ≤ C * ∫ x, |v x| ∂μ := by
  have hi := hv.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  calc
    |∫ x, ψ x*v x ∂μ| ≤ ∫ x, |ψ x*v x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => ψ x*v x)
    _ ≤ ∫ x, (C : ℝ)*|v x| ∂μ := by
      apply integral_mono hi.abs (hv.abs.const_mul C)
      intro x
      change |ψ x*v x| ≤ (C : ℝ)*|v x|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
    _ = C * ∫ x, |v x| ∂μ := integral_const_mul _ _

theorem abs_bounded_test_difference (v w : X → ℝ) (hv : Integrable v μ)
    (hw : Integrable w μ) (ψ : X → ℝ) (hψ : Measurable ψ) (C : ℝ≥0)
    (hC : ∀ x, ‖ψ x‖ ≤ C) :
    |(∫ x, ψ x*v x ∂μ)-(∫ x, ψ x*w x ∂μ)| ≤ C * ∫ x, |v x-w x| ∂μ := by
  have hiv := hv.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have hiw := hw.bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
  have he : (∫ x, ψ x*v x ∂μ)-(∫ x, ψ x*w x ∂μ) =
      ∫ x, ψ x*(v x-w x) ∂μ := by
    rw [← integral_sub hiv hiw]
    congr 1
    funext x
    ring
  rw [he]
  exact abs_integral_bounded_mul (v-w) (hv.sub hw) ψ hψ C hC

theorem scalar_tendsto_of_uniform_approximations
    (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (c : ℕ → ℝ) (z : ℝ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (herr : ∀ m n, |a n-b m n| ≤ δ m)
    (hb : ∀ m, Tendsto (b m) atTop (𝓝 (c m)))
    (hc : Tendsto c atTop (𝓝 z)) : Tendsto a atTop (𝓝 z) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hd := hδ.eventually (gt_mem_nhds (show 0 < ε/3 by positivity))
  have hz := (Metric.tendsto_atTop.mp hc (ε/3) (by positivity))
  obtain ⟨M,hM⟩ := hz
  obtain ⟨m,hm,hmδ⟩ := ((eventually_ge_atTop M).and hd).exists
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (hb m) (ε/3) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hb' := hN n hn
  have hc' := hM m hm
  rw [Real.dist_eq] at hb' hc' ⊢
  have htriangle := (abs_sub_le (a n) (b m n) z).trans
    (add_le_add_right (abs_sub_le (b m n) (c m) z) _)
  linarith [herr m n]

end BoltzmannNonuniqueness.Published

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakLinearMomentLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Passing weak L1 convergence through uniform L1 approximations -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Published
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem WeakL1Converges.of_L1_approximations
    {f : ℕ → X → ℝ} {g : X → ℝ}
    (hfi : ∀ n, Integrable (f n) μ) (hgm : Measurable g) (hgi : Integrable g μ)
    {u : ℕ → ℕ → X → ℝ} {v : ℕ → X → ℝ}
    (hui : ∀ j n, Integrable (u j n) μ) (hw : ∀ j, WeakL1Converges μ (u j) (v j))
    {δ : ℕ → ℝ} (hδ0 : ∀ j, 0 ≤ δ j) (hδ : Tendsto δ atTop (𝓝 0))
    (he : ∀ j n, eLpNorm (fun x => f n x-u j n x) 1 μ ≤ ENNReal.ofReal (δ j))
    (hg : ∀ j, eLpNorm (fun x => v j x-g x) 1 μ ≤ ENNReal.ofReal (δ j)) :
    WeakL1Converges μ f g := by
  refine ⟨hgm,hgi,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  let D : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  have hD x : ‖ψ x‖ ≤ D := (hC x).trans (le_max_left _ _)
  have herr j n : |(∫ x, ψ x*f n x ∂μ)-(∫ x, ψ x*u j n x ∂μ)| ≤ D*δ j := by
    exact (abs_bounded_test_difference _ _ (hfi n) (hui j n) ψ hψ D hD).trans
      (mul_le_mul_of_nonneg_left
        (integral_abs_le_of_eLpNorm_le ((hfi n).sub (hui j n)) (hδ0 j) (he j n)) D.coe_nonneg)
  have hlast j : |(∫ x, ψ x*v j x ∂μ)-(∫ x, ψ x*g x ∂μ)| ≤ D*δ j := by
    exact (abs_bounded_test_difference _ _ (hw j).2.1 hgi ψ hψ D hD).trans
      (mul_le_mul_of_nonneg_left
        (integral_abs_le_of_eLpNorm_le ((hw j).2.1.sub hgi) (hδ0 j) (hg j)) D.coe_nonneg)
  have ht : Tendsto (fun j => (D:ℝ)*δ j) atTop (𝓝 0) := by
    simpa only [mul_zero] using hδ.const_mul (D:ℝ)
  apply scalar_tendsto_of_uniform_approximations _ _ _ _ _ ht herr
    (fun j => (hw j).2.2 ψ hψ ⟨C,hC⟩)
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact squeeze_zero (fun _ => dist_nonneg) (fun j => by simpa only [Real.dist_eq] using hlast j) ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Entropy tails preserve weak convergence with the first velocity moment -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure (X × Velocity)}

theorem weak_linearMoment {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hfi : ∀ n, Integrable (entropyGauge (f n)) μ)
    (hfb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ) ≤ C)
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p)
    (hgi : Integrable (entropyGauge g) μ) (hgb : (∫ p, entropyGauge g p ∂μ) ≤ C)
    (hw : Published.WeakL1Converges μ f g) :
    Published.WeakL1Converges μ (fun n => linearMoment (f n)) (linearMoment g) := by
  let R : ℕ → ℝ := fun j => (j:ℝ)+1
  have hR j : 0 < R j := by dsimp [R] <;> positivity
  have hC : 0 ≤ C := (integral_nonneg (entropyGauge_nonneg hg)).trans hgb
  let a : ℕ → X × Velocity → ℝ := fun j p => if ‖p.2‖ ≤ R j then 1+‖p.2‖ else 0
  have ham j : Measurable (a j) := (measurable_const.add measurable_snd.norm).ite
    (measurableSet_le measurable_snd.norm measurable_const) measurable_const
  have hab j p : |a j p| ≤ 1+R j := by
    dsimp only [a]
    split_ifs with hp
    · rw [abs_of_nonneg (by positivity)]
      linarith
    · simp only [abs_zero]
      linarith [hR j]
  have he j (u : X × Velocity → ℝ) :
      (fun p => a j p*u p) = velocityLinearCut (R j) u := by
    ext p
    dsimp only [a,velocityLinearCut,linearMoment]
    split_ifs <;> simp only [zero_mul]
  have hc j : Published.WeakL1Converges μ
      (fun n => velocityLinearCut (R j) (f n)) (velocityLinearCut (R j) g) := by
    have h := hw.bounded_mul (ham j) (1+R j) (hab j)
    rw [show (fun n p => a j p*f n p) = (fun n => velocityLinearCut (R j) (f n)) from
      funext (fun n => he j (f n)),he j g] at h
    exact h
  apply Published.WeakL1Converges.of_L1_approximations
    (fun n => linearMoment_integrable (hfm n) (hf n) (hfi n))
    (linearMoment_measurable hgm) (linearMoment_integrable hgm hg hgi)
    (fun j n => velocityLinearCut_integrable (R j) (hfm n) (hf n) (hfi n)) hc
    (δ := fun j => 2*C/R j) (fun j => by positivity)
  · exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  · exact fun j n => velocityLinearCut_L1_error (hR j) (hfm n) (hf n) (hfi n) (hfb n)
  · intro j
    change eLpNorm (velocityLinearCut (R j) g-linearMoment g) 1 μ ≤ _
    rw [eLpNorm_sub_comm]
    exact velocityLinearCut_L1_error (hR j) hgm hg hgi hgb

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedPairUniformIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded weighted averaging is Lipschitz in L1 -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

theorem weighted_average_difference_le {f g w : X × Y → ℝ} {C : ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (hwm : Measurable w)
    (hfi : Integrable f (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (hb : ∀ p, |w p| ≤ C) :
    eLpNorm (fun x => (∫ y, w (x,y)*f (x,y) ∂ν)-(∫ y, w (x,y)*g (x,y) ∂ν)) 1 μ ≤
      ENNReal.ofReal C*eLpNorm (f-g) 1 (μ.prod ν) := by
  have hw : ∀ᵐ p ∂μ.prod ν, ‖w p‖ ≤ C :=
    Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using hb p)
  have hi₁ := hfi.bdd_mul hwm.aestronglyMeasurable hw
  have hi₂ := hgi.bdd_mul hwm.aestronglyMeasurable hw
  have he : (fun x => (∫ y, w (x,y)*f (x,y) ∂ν)-(∫ y, w (x,y)*g (x,y) ∂ν)) =ᵐ[μ]
      (fun x => ∫ y, w (x,y)*(f (x,y)-g (x,y)) ∂ν) := by
    filter_upwards [hi₁.prod_right_ae,hi₂.prod_right_ae] with x hx hy
    rw [← integral_sub hx hy]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => (mul_sub _ _ _).symm)
  rw [eLpNorm_congr_ae he]
  apply (eLpNorm_integral_le (hwm.mul (hfm.sub hgm))).trans
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  filter_upwards [] with p
  change ‖w p*(f p-g p)‖ ≤ C*‖f p-g p‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hb p) (norm_nonneg _)

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_StrongPairMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded families of strong L1 fibers converge on the product -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [IsFiniteMeasure ν]

theorem strongL1_of_strong_fibers {u : ℕ → X × Y → ℝ}
    (hm : ∀ n, Measurable (u n)) {B : ℝ≥0∞} (hB : B ≠ ∞)
    (hb : ∀ n, ∀ᵐ y ∂ν, eLpNorm (fun x => u n (x,y)) 1 μ ≤ B)
    (ht : ∀ᵐ y ∂ν, Tendsto (fun n => eLpNorm (fun x => u n (x,y)) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n) 1 (μ.prod ν)) atTop (𝓝 0) := by
  have he n y : eLpNorm (fun x => u n (x,y)) 1 μ = ∫⁻ x, ‖u n (x,y)‖ₑ ∂μ :=
    eLpNorm_one_eq_lintegral_enorm
  have hme n : Measurable (fun y => eLpNorm (fun x => u n (x,y)) 1 μ) := by
    simp_rw [he]
    exact (hm n).enorm.lintegral_prod_left'
  have hi : (∫⁻ _ : Y, B ∂ν) ≠ ∞ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top hB (measure_ne_top _ _)
  have h := tendsto_lintegral_of_dominated_convergence (fun _ : Y => B) hme hb hi ht
  simp only [lintegral_zero] at h
  have hp n : eLpNorm (u n) 1 (μ.prod ν) =
      ∫⁻ y, eLpNorm (fun x => u n (x,y)) 1 μ ∂ν := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      lintegral_prod_symm _ (hm n).enorm.aemeasurable]
    simp_rw [he]
  simpa only [hp] using h

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Strong velocity averages extend to bounded measurable kernel families -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
variable {μ : Measure X} {ν : Measure Y} {τ : Measure Z}
variable [SFinite μ] [SFinite ν] [IsFiniteMeasure τ]

theorem strong_bounded_kernel_averages
    {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hb : ∀ n, eLpNorm (f n) 1 (μ.prod ν) ≤ B)
    {k : Z × Y → ℝ} (hk : Measurable k) {C : ℝ} (hC : ∀ p, |k p| ≤ C)
    (ha : ∀ z, Tendsto (fun n => eLpNorm (fun x =>
      (∫ y, k (z,y)*f n (x,y) ∂ν)-(∫ y, k (z,y)*g (x,y) ∂ν)) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun p : X × Z =>
      (∫ y, k (p.2,y)*f n (p.1,y) ∂ν)-(∫ y, k (p.2,y)*g (p.1,y) ∂ν))
      1 (μ.prod τ)) atTop (𝓝 0) := by
  have hm (u : X × Y → ℝ) (hu : Measurable u) :
      Measurable (fun p : X × Z => ∫ y, k (p.2,y)*u (p.1,y) ∂ν) := by
    have hh : Measurable (fun p : (X × Z) × Y => k (p.1.2,p.2)*u (p.1.1,p.2)) := by
      fun_prop
    exact hh.stronglyMeasurable.integral_prod_right'.measurable
  apply strongL1_of_strong_fibers (fun n => (hm _ (hfm n)).sub (hm _ hgm))
    (B := ENNReal.ofReal C*(B+eLpNorm g 1 (μ.prod ν)))
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨hB,(memLp_one_iff_integrable.mpr hgi).eLpNorm_ne_top⟩)
  · intro n
    apply ae_of_all
    intro z
    apply (weighted_average_difference_le (hfm n) hgm
      (hk.comp (measurable_const.prodMk measurable_snd)) (hfi n) hgi (fun p => hC (z,p.2))).trans
    apply mul_le_mul' le_rfl
    exact (eLpNorm_sub_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)).trans (add_le_add (hb n) le_rfl)
  · exact ae_of_all _ ha

end BoltzmannNonuniqueness.Compactness

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedPairCompactness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Factorization of mass-normalized pair moments -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

omit [MeasurableSpace X] in
theorem normalizedPair_moment_identity {f : X × Y → ℝ} {k l : X × Y → ℝ} (x : X) :
    (∫ y : Y × Y, (k (x,y.1)*l (x,y.2))*normalizedPair ν f (x,y) ∂ν.prod ν) =
      (∫ v, k (x,v)*f (x,v) ∂ν)*(∫ w, l (x,w)*f (x,w) ∂ν)/(1+fiberMass ν f x) := by
  have he : (fun y : Y × Y => (k (x,y.1)*l (x,y.2))*normalizedPair ν f (x,y)) =
      (fun y : Y × Y => ((k (x,y.1)*f (x,y.1))*(l (x,y.2)*f (x,y.2)))/(1+fiberMass ν f x)) := by
    funext y
    dsimp only [normalizedPair,normalizedTensor]
    ring
  rw [he,integral_div,integral_prod_mul (fun v => k (x,v)*f (x,v)) (fun w => l (x,w)*f (x,w))]

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Normalized collision pairs determine the weighted squares of velocity averages -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

omit [MeasurableSpace X] in
private theorem square_identity (ψ : Y → ℝ) (f : X × Y → ℝ) (x : X) :
    (∫ y : Y × Y, (ψ y.1*ψ y.2)*normalizedPair ν f (x,y) ∂ν.prod ν) =
      (∫ v, ψ v*f (x,v) ∂ν)^2/(1+fiberMass ν f x) := by
  simpa only [pow_two] using
    normalizedPair_moment_identity (ν := ν) (f := f)
      (k := fun p => ψ p.2) (l := fun p => ψ p.2) x

theorem normalized_average_square_integrable {f : X × Y → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfi : Integrable f (μ.prod ν))
    {ψ : Y → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ y, |ψ y| ≤ C) :
    Integrable (fun x => (∫ v, ψ v*f (x,v) ∂ν)^2/(1+fiberMass ν f x)) μ := by
  have hkm : Measurable (fun z : X × (Y × Y) => ψ z.2.1*ψ z.2.2) :=
    (hψ.comp measurable_snd.fst).mul (hψ.comp measurable_snd.snd)
  have hkb (z : X × (Y × Y)) : |ψ z.2.1*ψ z.2.2| ≤ |C| * |C| := by
    rw [abs_mul]
    exact mul_le_mul ((hC _).trans (le_abs_self C)) ((hC _).trans (le_abs_self C))
      (abs_nonneg _) (abs_nonneg _)
  have hi := ((normalizedPair_integrable hfm hf hfi).bdd_mul
    hkm.aestronglyMeasurable (ae_of_all _ hkb)).integral_prod_left
  simpa only [square_identity ψ] using hi

theorem weak_normalized_average_squares
    {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν))
    (hp : Published.WeakL1Converges (μ.prod (ν.prod ν))
      (fun n => normalizedPair ν (f n)) (normalizedPair ν g))
    {ψ : Y → ℝ} (hψ : Measurable ψ) {C : ℝ} (hC : ∀ y, |ψ y| ≤ C) :
    Published.WeakL1Converges μ
      (fun n x => (∫ v, ψ v*f n (x,v) ∂ν)^2/(1+fiberMass ν (f n) x))
      (fun x => (∫ v, ψ v*g (x,v) ∂ν)^2/(1+fiberMass ν g x)) := by
  have hkm : Measurable (fun z : X × (Y × Y) => ψ z.2.1*ψ z.2.2) :=
    (hψ.comp measurable_snd.fst).mul (hψ.comp measurable_snd.snd)
  have hkb (z : X × (Y × Y)) : |ψ z.2.1*ψ z.2.2| ≤ |C| * |C| := by
    rw [abs_mul]
    exact mul_le_mul ((hC _).trans (le_abs_self C)) ((hC _).trans (le_abs_self C))
      (abs_nonneg _) (abs_nonneg _)
  have h := hp.marginal (fun n => normalizedPair_integrable (hfm n) (hf n) (hfi n))
    hkm (|C| * |C|) hkb
  simpa only [square_identity ψ] using h

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

theorem finiteEntropy_of_relativeEntropy_integrable {f : Density}
    (hfm : Measurable f) (hfn : ∀ z, 0 ≤ f z)
    (hH : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (f z))) :
    FiniteEntropyDatum f := by
  have hmajor : Integrable (fun z : Phase =>
      4*(scalarRelativeEntropy (maxwellian z.2) (f z)+entropyGaussian z.2)) :=
    (hH.add (entropyGaussian_integrable.comp_snd volume)).const_mul 4
  have hweight : Integrable (fun z : Phase => (1+‖z.2‖^2)*f z) := by
    apply hmajor.mono' ((measurable_const.add (measurable_snd.norm.pow_const 2)).mul hfm).aestronglyMeasurable
    filter_upwards [] with z
    change ‖(1+‖z.2‖^2)*f z‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (hfn z))]
    exact entropy_controls_mass_energy (hfn z) z.2
  have hfi : Integrable f := by
    apply hweight.mono' hfm.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (hfn z)]
    nlinarith [sq_nonneg ‖z.2‖,hfn z]
  have hEi : Integrable (fun z : Phase => ‖z.2‖^2*f z) := by
    apply hweight.mono' ((measurable_snd.norm.pow_const 2).mul hfm).aestronglyMeasurable
    filter_upwards [] with z
    change ‖‖z.2‖^2*f z‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hfn z))]
    nlinarith [hfn z]
  exact FiniteEntropyDatum.of_relativeEntropy_integrable (Filter.Eventually.of_forall hfn) hfi hEi hH

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

end BoltzmannNonuniqueness.TransportPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_LinearCharacteristicBalance
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
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

end BoltzmannNonuniqueness.TransportPrimitive

end

end

section

/-! # Integrability of the linear velocity tests used for conserved moments -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem linearVelocityTest_integrable {μ : Measure (X × Velocity)}
    {F : X × Velocity → ℝ} (hF : Measurable F) (hFn : ∀ p, 0 ≤ F p)
    (hFi : Integrable (entropyGauge F) μ) {ψ : Velocity → ℝ}
    (hψ : Measurable ψ) (D : ℝ≥0) (hD : ∀ v, |ψ v| ≤ D*(1+‖v‖)) :
    Integrable (fun p => ψ p.2*F p) μ := by
  apply ((linearMoment_integrable hF hFn hFi).const_mul (D:ℝ)).mono'
    ((hψ.comp measurable_snd).mul hF).aestronglyMeasurable
  filter_upwards [] with p
  change ‖ψ p.2*F p‖ ≤ (D:ℝ)*linearMoment F p
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hFn p)]
  simpa only [linearMoment,mul_assoc] using
    mul_le_mul_of_nonneg_right (hD p.2) (hFn p)

end BoltzmannNonuniqueness.PeriodicApproximation

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

theorem timeWeight_pos (t : ℝ) : 0 < timeWeight t := Real.exp_pos _

instance finiteTimeMeasure_finite : IsFiniteMeasure finiteTimeMeasure := by
  apply isFiniteMeasure_withDensity
  have hi : Integrable timeWeight := by
    change Integrable (fun t : ℝ => Real.exp (-(t^2)))
    simpa using (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ)<1))
  exact ((hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun t => (timeWeight_pos t).le))).mp hi.2).ne

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

/-! # Strong L1 convergence implies convergence against bounded measurable tests -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published

theorem weakL1_of_strong {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hgm : Measurable g)
    (hgi : Integrable g μ) (hfi : ∀ n, Integrable (f n) μ)
    (h : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 1 μ) atTop (𝓝 0)) :
    WeakL1Converges μ f g := by
  have hc : WeakL1Converges μ (fun _ : ℕ => g) g :=
    ⟨hgm,hgi,fun _ _ _ => tendsto_const_nhds⟩
  exact hc.of_eLpNorm_sub (fun _ => hgi) hfi h

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedHotRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Vanishing weighted variance gives strong L1 convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness

lemma abs_le_mass_add_variance {u r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    |u| ≤ δ*r+(u^2/r)/δ := by
  have hpos : 0 < δ*r := mul_pos hδ hr
  have hnum : |u| *(δ*r) ≤ (δ*r)^2+u^2 := by
    nlinarith [sq_nonneg (|u|-δ*r),sq_abs u,sq_nonneg u]
  calc
    |u| ≤ ((δ*r)^2+u^2)/(δ*r) := (le_div_iff₀ hpos).mpr hnum
    _ = δ*r+(u^2/r)/δ := by field_simp

theorem strongL1_of_weighted_variance
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u r : ℕ → X → ℝ} {B : ℝ} (hB : 0 < B)
    (hui : ∀ n, Integrable (u n) μ) (hri : ∀ n, Integrable (r n) μ)
    (hr : ∀ n x, 0 < r n x) (hbound : ∀ n, (∫ x, r n x ∂μ) ≤ B)
    (hvi : ∀ n, Integrable (fun x => (u n x)^2/r n x) μ)
    (hv : Tendsto (fun n => ∫ x, (u n x)^2/r n x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (u n) 1 μ) atTop (𝓝 0) := by
  have habs : Tendsto (fun n => ∫ x, |u n x| ∂μ) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun n => ha.trans_le (integral_nonneg (fun x => abs_nonneg (u n x))))
    · intro ε hε
      let δ := ε/(2*B)
      have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hB)
      have ht : Tendsto (fun n => (∫ x, (u n x)^2/r n x ∂μ)/δ) atTop (𝓝 0) := by
        simpa only [zero_div] using hv.div_const δ
      filter_upwards [ht.eventually (gt_mem_nhds (show (0:ℝ) < ε/2 by positivity))] with n hn
      have he : (∫ x, |u n x| ∂μ) ≤ δ*(∫ x, r n x ∂μ)+
          (∫ x, (u n x)^2/r n x ∂μ)/δ := by
        have hh := integral_mono (hui n).abs ((hri n).const_mul δ |>.add ((hvi n).div_const δ))
          (fun x => abs_le_mass_add_variance (hr n x) hδ)
        simp only [Pi.add_apply] at hh
        rw [integral_add ((hri n).const_mul δ) ((hvi n).div_const δ),
          integral_const_mul,integral_div] at hh
        exact hh
      have hδB : δ*B = ε/2 := by dsimp only [δ]; field_simp
      have hb := mul_le_mul_of_nonneg_left (hbound n) hδ.le
      linarith
  have he n : eLpNorm (u n) 1 μ = ENNReal.ofReal (∫ x, |u n x| ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hui n)]
    simp only [Real.norm_eq_abs]
  simpa only [he,ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal habs

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Weak first and second moments identify a vanishing weighted variance -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma weighted_variance_identity {a r b : ℝ} (hr : r ≠ 0) :
    (a-r*b)^2/r = a^2/r-2*(b*a)+(b*b)*r := by
  field_simp
  ring

theorem weighted_variance_moments
    {a r : ℕ → X → ℝ} {A R b : X → ℝ}
    (ha : Published.WeakL1Converges μ a A) (hr : Published.WeakL1Converges μ r R)
    (hai : ∀ n, Integrable (a n) μ) (hri : ∀ n, Integrable (r n) μ)
    (hrp : ∀ n x, 0 < r n x)
    (hsi : ∀ n, Integrable (fun x => (a n x)^2/r n x) μ)
    (hbm : Measurable b) (C : ℝ≥0) (hb : ∀ x, |b x| ≤ C)
    (hA : A =ᵐ[μ] fun x => R x*b x)
    (hsecond : Tendsto (fun n => ∫ x, (a n x)^2/r n x ∂μ)
      atTop (𝓝 (∫ x, (b x*b x)*R x ∂μ))) :
    (∀ n, Integrable (fun x => (a n x-r n x*b x)^2/r n x) μ) ∧
    Tendsto (fun n => ∫ x, (a n x-r n x*b x)^2/r n x ∂μ) atTop (𝓝 0) := by
  have hbb x : |b x*b x| ≤ (C:ℝ)*C := by
    rw [abs_mul]
    exact mul_le_mul (hb x) (hb x) (abs_nonneg _) C.coe_nonneg
  have hcross n : Integrable (fun x => b x*a n x) μ :=
    (hai n).bdd_mul hbm.aestronglyMeasurable (ae_of_all _ hb)
  have hlast n : Integrable (fun x => (b x*b x)*r n x) μ :=
    (hri n).bdd_mul (hbm.mul hbm).aestronglyMeasurable (ae_of_all _ hbb)
  have he n : (fun x => (a n x-r n x*b x)^2/r n x) =
      (fun x => (a n x)^2/r n x)- (fun x => 2*(b x*a n x))+
        (fun x => (b x*b x)*r n x) := by
    funext x
    exact weighted_variance_identity (hrp n x).ne'
  have hv n : Integrable (fun x => (a n x-r n x*b x)^2/r n x) μ := by
    rw [he]
    exact ((hsi n).sub ((hcross n).const_mul 2)).add (hlast n)
  have hei n : (∫ x, (a n x-r n x*b x)^2/r n x ∂μ) =
      (∫ x, (a n x)^2/r n x ∂μ)-2*(∫ x, b x*a n x ∂μ)+
        (∫ x, (b x*b x)*r n x ∂μ) := by
    rw [he]
    have heq := integral_add ((hsi n).sub ((hcross n).const_mul 2)) (hlast n)
    simp only [Pi.sub_apply] at heq
    rw [integral_sub (hsi n) ((hcross n).const_mul 2),integral_const_mul] at heq
    exact heq
  have hlim := (hsecond.sub ((ha.2.2 b hbm ⟨C,hb⟩).const_mul 2)).add
    (hr.2.2 (fun x => b x*b x) (hbm.mul hbm) ⟨(C:ℝ)*C,hbb⟩)
  have hz : (∫ x, b x*A x ∂μ) = ∫ x, (b x*b x)*R x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hA] with x hx
    rw [hx]
    ring
  rw [hz,show (∫ x, (b x*b x)*R x ∂μ)-2*(∫ x, (b x*b x)*R x ∂μ)+
    (∫ x, (b x*b x)*R x ∂μ) = 0 by ring] at hlim
  exact ⟨hv,by simpa only [hei] using hlim⟩

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Strong first moments from matched weighted second moments -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem weighted_moments_strong
    {a r : ℕ → X → ℝ} {A R b : X → ℝ}
    (ha : Published.WeakL1Converges μ a A) (hr : Published.WeakL1Converges μ r R)
    (hai : ∀ n, Integrable (a n) μ) (hri : ∀ n, Integrable (r n) μ)
    (hrp : ∀ n x, 0 < r n x) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ n, (∫ x, r n x ∂μ) ≤ B)
    (hsi : ∀ n, Integrable (fun x => (a n x)^2/r n x) μ)
    (hbm : Measurable b) (C : ℝ≥0) (hb : ∀ x, |b x| ≤ C)
    (hA : A =ᵐ[μ] fun x => R x*b x)
    (hsecond : Tendsto (fun n => ∫ x, (a n x)^2/r n x ∂μ)
      atTop (𝓝 (∫ x, (b x*b x)*R x ∂μ)))
    (hstrong : Tendsto (fun n => eLpNorm (fun x => r n x-R x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x-A x) 1 μ) atTop (𝓝 0) := by
  obtain ⟨hvi,hv⟩ := weighted_variance_moments ha hr hai hri hrp hsi hbm C hb hA hsecond
  have hmul n : Integrable (fun x => r n x*b x) μ := by
    simpa only [mul_comm] using (hri n).bdd_mul hbm.aestronglyMeasurable (ae_of_all _ hb)
  have hui n : Integrable (fun x => a n x-r n x*b x) μ := (hai n).sub (hmul n)
  have hu := strongL1_of_weighted_variance hB hui hri hrp hbound hvi hv
  have he := tendsto_L1_bounded_mul_zero
    (fun n => ((hri n).sub hr.2.1).aestronglyMeasurable)
    (fun _ => hbm.aestronglyMeasurable) hstrong C.coe_nonneg
    (Eventually.of_forall (fun _ => ae_of_all μ hb))
  have ht := hu.add he
  simp only [add_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  have hid : (fun x => a n x-A x) =ᵐ[μ]
      (fun x => (a n x-r n x*b x)+b x*(r n x-R x)) := by
    filter_upwards [hA] with x hx
    rw [hx]
    ring
  change eLpNorm (fun x => a n x-A x) 1 μ ≤
    eLpNorm (fun x => a n x-r n x*b x) 1 μ+eLpNorm (fun x => b x*(r n x-R x)) 1 μ
  rw [eLpNorm_congr_ae hid]
  exact eLpNorm_add_le (hf := (hai n).1.sub ((hri n).1.mul hbm.aestronglyMeasurable))
    (hg := hbm.aestronglyMeasurable.mul ((hri n).1.sub hr.1.aestronglyMeasurable)) (by norm_num)

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

variable {X : Type*}

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

theorem regularized_collision_invariant {μ : Measure X} [SFinite μ] (b : ℝ)
    (f ψ : X × Velocity → ℝ)
    (hpre : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hpost : Integrable (fun z => ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (hψ : ∀ z, collisionJump ψ z = 0) :
    (∫ z, ψ (z.1.1,z.1.2.1)*regularizedPostRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
    ∫ z, ψ (z.1.1,z.1.2.1)*regularizedPreRate b f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea := by
  have h := regularized_weak_identity b f ψ hpre hpost
  simp only [hψ,zero_mul,integral_zero,mul_zero,sub_eq_zero] at h
  exact h


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

theorem regularized_test_invariant {N C : ℝ} (hN : 0 < N)
    {μ : Measure X} [IsFiniteMeasure μ] {f ψ : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hψm : Measurable ψ)
    (hψ : ∀ p, ‖p.2‖ ≤ N → |ψ p| ≤ C) (hj : ∀ z, collisionJump ψ z = 0) :
    (∫ p, ψ p*gain N f p ∂μ.prod volume) = ∫ p, ψ p*loss N f p ∂μ.prod volume := by
  obtain ⟨_,_,hp,hl⟩ := regularized_test_marginals (μ := μ) hN hfm hf hψm hψ
  rw [hp,hl]
  exact regularized_collision_invariant N f ψ
    (regularizedPreRate_test_integrable hN hfm hf hψm hψ)
    (regularizedPostRate_test_integrable hN hfm hf hψm hψ) hj

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

section

/-! # Initial mass and momentum pass through the actual truncations -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialApproximation_linear_moment_tendsto {f : Density}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (D : ℝ≥0)
    (hD : ∀ v, |ψ v| ≤ D*(1+‖v‖)) :
    Tendsto (fun n : ℕ => ∫ p : Phase, ψ p.2*initialApproximation ((n:ℝ)+1) f p)
      atTop (𝓝 (∫ p : Phase, ψ p.2*f p)) := by
  have hli : Integrable (linearMoment f) := linearMoment_integrable hfm hf hi
  apply tendsto_integral_of_dominated_convergence
    (fun p => (D:ℝ)*linearMoment f p)
    (fun n => ((hψ.comp measurable_snd).mul
      (initialApproximation_measurable ((n:ℝ)+1) hfm)).aestronglyMeasurable)
    (hli.const_mul (D:ℝ))
  · intro n
    filter_upwards [] with p
    change ‖ψ p.2*initialApproximation ((n:ℝ)+1) f p‖ ≤ (D:ℝ)*linearMoment f p
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg
      ((initialApproximation_bounds (by positivity : 0 ≤ (n:ℝ)+1) f p).1)]
    calc
      _ ≤ |ψ p.2| *f p := mul_le_mul_of_nonneg_left (initialApproximation_le hf p) (abs_nonneg _)
      _ ≤ (D:ℝ)*(1+‖p.2‖)*f p := mul_le_mul_of_nonneg_right (hD p.2) (hf p)
      _ = _ := by simp only [linearMoment, mul_assoc]
  · filter_upwards [] with p
    apply tendsto_const_nhds.congr'
    filter_upwards [initialApproximation_sequence_eventually_eq hf p] with n hn
    change ψ p.2*f p = ψ p.2*initialApproximation ((n:ℝ)+1) f p
    rw [hn]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Relative entropy of the actual initial truncations converges to the datum -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem initialApproximation_relativeEntropy_tendsto {f : Density}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    Tendsto (fun n : ℕ => relativeEntropy (initialApproximation ((n:ℝ)+1) f))
      atTop (𝓝 (relativeEntropy f)) := by
  have hm : Measurable (fun p : Phase => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hmajor := (hi.const_mul initialEntropyCoefficient).add integrable_maxwellian_phase
  have h := tendsto_integral_of_dominated_convergence
    (F := fun n p => scalarRelativeEntropy (maxwellian p.2) (initialApproximation ((n:ℝ)+1) f p))
    (f := fun p => scalarRelativeEntropy (maxwellian p.2) (f p))
    (fun p => initialEntropyCoefficient*entropyMoment f p+maxwellian p.2)
    (fun n => (scalarRelativeEntropy_measurable hm (initialApproximation_measurable ((n:ℝ)+1) hfm)).aestronglyMeasurable)
    hmajor (fun n => by
      filter_upwards [] with p
      have hn : 1 ≤ (n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      have hfn := fun p => (initialApproximation_bounds (zero_le_one.trans hn) f p).1
      rw [Real.norm_of_nonneg (scalarRelativeEntropy_nonneg (maxwellian_pos p.2) (hfn p))]
      exact (relativeEntropy_density_bound hfn p).trans
        (add_le_add (mul_le_mul_of_nonneg_left (initialApproximation_entropy_le hn hf p)
          initialEntropyCoefficient_nonneg) le_rfl)) (by
      filter_upwards [] with p
      apply tendsto_const_nhds.congr'
      filter_upwards [initialApproximation_sequence_eventually_eq hf p] with n hn
      rw [hn])
  simpa only [relativeEntropy,scalarRelativeEntropy_eq (maxwellian_pos _)] using h

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

end BoltzmannNonuniqueness.TorusFlight

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_BoundedAverageProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A bounded representative of a density divided by its positive mass -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem boundedQuotient_measurable (C : ℝ≥0) {A R : X → ℝ}
    (hA : Measurable A) (hR : Measurable R) : Measurable (boundedQuotient C A R) :=
  measurable_const.max (measurable_const.min (hA.div hR))

omit [MeasurableSpace X] in
theorem boundedQuotient_bound (C : ℝ≥0) (A R : X → ℝ) (x : X) :
    |boundedQuotient C A R x| ≤ C := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _,max_le (by linarith [C.coe_nonneg]) (min_le_left _ _)⟩

theorem boundedQuotient_eq_ae (C : ℝ≥0) {A R : X → ℝ}
    (hR : ∀ x, 0 < R x) (hA : ∀ᵐ x ∂μ, |A x| ≤ C*R x) :
    A =ᵐ[μ] fun x => R x*boundedQuotient C A R x := by
  filter_upwards [hA] with x hx
  have hq : |A x/R x| ≤ C := by
    rw [abs_div,abs_of_pos (hR x)]
    exact (div_le_iff₀ (hR x)).mpr hx
  have hq' := abs_le.mp hq
  simp only [boundedQuotient,min_eq_right hq'.2,max_eq_right hq'.1]
  field_simp [(hR x).ne']

end BoltzmannNonuniqueness.Compactness

end

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

theorem BoundedCutoffSolution.collision_measurable (S : BoundedCutoffSolution N T f₀) :
    Measurable S.collision := S.source_measurable.sub (measurable_const.mul S.measurable)

theorem BoundedCutoffSolution.collision_support (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (z : ℝ × Phase) (hz : N < ‖z.2.2‖) : S.collision z = 0 := by
  rw [S.collision_eq,gain_zero_of_velocity hN _ z.2 hz,loss_zero_of_velocity hN _ z.2 hz,sub_self]

theorem BoundedCutoffSolution.collision_bounded (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z, |S.collision z| ≤ D := by
  obtain ⟨C,hC,hCb⟩ := S.source_bounded hN
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  have hL : 0 ≤ lossBound N := by unfold lossBound; positivity
  refine ⟨C+lossBound N*B,by positivity,?_⟩
  intro z
  calc
    _ ≤ |S.source z|+|lossBound N*S.density z| := abs_sub _ _
    _ = |S.source z|+lossBound N*S.density z := by
      rw [abs_of_nonneg (mul_nonneg hL (S.nonnegative z))]
    _ ≤ C+lossBound N*B := by
      gcongr
      · exact hCb z
      · exact hB z

theorem BoundedCutoffSolution.weighted_collision_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C) :
    Integrable (fun z : ℝ × Phase => ψ z.2.2*S.collision z)
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  obtain ⟨D,hD,hDb⟩ := S.collision_bounded hN
  have hC : 0 ≤ C := (abs_nonneg (ψ 0)).trans (hψ 0 (by simpa using hN.le))
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let g : (ℝ × Position) × Velocity → ℝ := fun p => ψ p.2*S.collision (p.1.1,(p.1.2,p.2))
  have hgm : Measurable g :=
    (hψm.comp measurable_snd).mul (S.collision_measurable.comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hgb (p : (ℝ × Position) × Velocity) : |g p| ≤ C*D := by
    dsimp only [g]
    by_cases hp : N < ‖p.2‖
    · rw [S.collision_support hN.le (p.1.1,(p.1.2,p.2)) hp,mul_zero,abs_zero]
      positivity
    · rw [abs_mul]
      exact mul_le_mul (hψ p.2 (le_of_not_gt hp)) (hDb (p.1.1,(p.1.2,p.2))) (abs_nonneg _) hC
  have hgs (p : (ℝ × Position) × Velocity) (hp : N < ‖p.2‖) : g p = 0 := by
    dsimp only [g]
    rw [S.collision_support hN.le (p.1.1,(p.1.2,p.2)) hp,mul_zero]
  have hg : Integrable g (μ.prod volume) := bounded_velocity_integrable (μ := μ) (N := N) hgm hgb hgs
  have hr := (measurePreserving_prodAssoc (volume.restrict (Icc 0 T))
    (volume : Measure Position) (volume : Measure Velocity)).symm.integrable_comp_of_integrable hg
  change Integrable (fun z : ℝ × Phase => ψ z.2.2*S.collision z)
    ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod (volume : Measure Velocity))) at hr
  simpa only [Measure.volume_eq_prod] using hr

theorem BoundedCutoffSolution.characteristicSource_measurable (S : BoundedCutoffSolution N T f₀) :
    Measurable S.characteristicSource := S.collision_measurable.comp
      (measurable_fst.prodMk TorusFlight.measurable_flight)

theorem BoundedCutoffSolution.weighted_characteristic_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C) :
    Integrable (fun z : ℝ × Phase => ψ z.2.2*S.characteristicSource z)
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) :=
  (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable
    (S.weighted_collision_integrable hN ψ hψm hψ)

theorem BoundedCutoffSolution.eulerianProfile_eq (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    TorusFlight.eulerianProfile (volume.restrict (Icc 0 T)) f₀ S.characteristicSource t p =
      S.density (t,p) := by
  unfold TorusFlight.eulerianProfile TorusFlight.characteristicProfile
  rw [Published.timePrimitive_eq_interval ht]
  have he := S.characteristic_integral hN ht (TorusFlight.flight (-t) p)
  rw [TorusFlight.neg_flight] at he
  exact he.symm

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Every-time moment conservation of the constructed supported approximants -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.weighted_density_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C) (t : ℝ) :
    Integrable (fun p : Phase => ψ p.2*S.density (t,p)) := by
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  have hC : 0 ≤ C := (abs_nonneg (ψ 0)).trans (hψ 0 (by simpa using hN))
  rw [Measure.volume_eq_prod]
  apply bounded_velocity_integrable (A := C*B)
  · exact (hψm.comp measurable_snd).mul (S.measurable.comp (measurable_const.prodMk measurable_id))
  · intro p
    by_cases hp : N < ‖p.2‖
    · rw [S.support (t,p) hp,mul_zero,abs_zero]
      positivity
    · rw [abs_mul,abs_of_nonneg (S.nonnegative (t,p))]
      exact mul_le_mul (hψ _ (le_of_not_gt hp)) (hB (t,p)) (S.nonnegative (t,p)) hC
  · intro p hp
    rw [S.support (t,p) hp,mul_zero]

theorem BoundedCutoffSolution.weighted_collision_zero (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C)
    (hj : ∀ z : (Position × (Velocity × Velocity)) × Sphere,
      collisionJump (fun p : Phase => ψ p.2) z = 0) (t : ℝ) :
    (∫ p : Phase, ψ p.2*S.collision (t,p)) = 0 := by
  have hm : Measurable (fun p : Phase => S.density (t,p)) :=
    S.measurable.comp (measurable_const.prodMk measurable_id)
  have hn (p : Phase) : 0 ≤ S.density (t,p) := S.nonnegative (t,p)
  have hw (p : Phase) (hp : ‖p.2‖ ≤ N) : |ψ p.2| ≤ C := hψ p.2 hp
  have hi := regularized_test_marginals (μ := (volume : Measure Position)) hN hm hn
    (hψm.comp measurable_snd) hw
  have he := regularized_test_invariant (μ := (volume : Measure Position)) hN hm hn
    (hψm.comp measurable_snd) hw hj
  dsimp only [Function.comp_def] at hi he
  simp_rw [S.collision_eq,mul_sub]
  rw [Measure.volume_eq_prod,integral_sub hi.1 hi.2.1,he,sub_self]

theorem BoundedCutoffSolution.weighted_characteristic_zero (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C)
    (hj : ∀ z : (Position × (Velocity × Velocity)) × Sphere,
      collisionJump (fun p : Phase => ψ p.2) z = 0) (t : ℝ) :
    (∫ p : Phase, ψ p.2*S.characteristicSource (t,p)) = 0 :=
  (TorusFlight.integral_flight (fun p : Phase => ψ p.2*S.collision (t,p)) t).trans
    (S.weighted_collision_zero hN ψ hψm hψ hj t)

theorem BoundedCutoffSolution.moment_conservation (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C)
    (hj : ∀ z : (Position × (Velocity × Velocity)) × Sphere,
      collisionJump (fun p : Phase => ψ p.2) z = 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p : Phase, ψ p.2*S.density (t,p)) = ∫ p : Phase, ψ p.2*f₀ p := by
  have hm : Measurable (fun z : ℝ × Phase => ψ z.2.2*S.characteristicSource z) :=
    (hψm.comp measurable_snd.snd).mul S.characteristicSource_measurable
  have hfi := S.weighted_density_integrable hN.le ψ hψm hψ 0
  have he : (fun p => ψ p.2*S.density (0,p)) = (fun p => ψ p.2*f₀ p) := by
    funext p
    rw [S.initial hT]
  rw [he] at hfi
  have h := TorusFlight.velocity_weighted_profile_balance f₀ S.characteristicSource ψ hm
    (S.weighted_characteristic_integrable hN ψ hψm hψ) hfi t
  have hz : (∫ s, if s ≤ t then ∫ p : Phase, ψ p.2*S.characteristicSource (s,p) else 0
      ∂volume.restrict (Icc 0 T)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with s
    rw [S.weighted_characteristic_zero hN ψ hψm hψ hj s]
    split_ifs <;> rfl
  rw [hz,add_zero] at h
  calc
    _ = ∫ p : Phase, ψ p.2*TorusFlight.eulerianProfile (volume.restrict (Icc 0 T))
        f₀ S.characteristicSource t p := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [S.eulerianProfile_eq hN ht]
    _ = _ := h

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

section

/-! # Conserved mass, energy, and momentum coordinates of each actual approximation -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.momentum_coordinate_conservation (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (i : Fin 3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p : Phase, (p.2 i)*S.density (t,p)) = ∫ p : Phase, (p.2 i)*f₀ p := by
  apply S.moment_conservation hN (ht.1.trans ht.2) (fun v => v i)
    (by fun_prop) (C := N) _ (collisionJump_momentum i) ht
  intro v hv
  have h : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  exact h.trans hv

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong L¹ limits preserve the entropy bound at every time -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem weakL1_of_eLpNorm_sub {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hgm : Measurable g) (hg : Integrable g μ)
    (ht : Tendsto (fun n => eLpNorm (fun x => f n x-g x) 1 μ) atTop (𝓝 0)) :
    WeakL1Converges μ f g := by
  apply weakL1_of_integral_norm_sub hf hgm hg
  have he n : (∫ x, ‖f n x-g x‖ ∂μ) =
      (eLpNorm (fun x => f n x-g x) 1 μ).toReal := by
    change (∫ x, ‖(f n-g) x‖ ∂μ) = (eLpNorm (f n-g) 1 μ).toReal
    rw [eLpNorm_one_eq_lintegral_enorm,
      integral_norm_eq_lintegral_enorm ((hf n).sub hg).aestronglyMeasurable]
  simp only [he]
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Strong L1 convergence with uniformly small errors on both sides -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strongL1_of_two_sided_approximations
    {f : ℕ → X → ℝ} {g : X → ℝ} {u : ℕ → ℕ → X → ℝ} {v : ℕ → X → ℝ}
    {δ : ℕ → ℝ≥0∞} (hδ : Tendsto δ atTop (𝓝 0))
    (hf : ∀ j n, eLpNorm (f n-u j n) 1 μ ≤ δ j)
    (hg : ∀ j, eLpNorm (v j-g) 1 μ ≤ δ j)
    (hu : ∀ j, Tendsto (fun n => eLpNorm (u j n-v j) 1 μ) atTop (𝓝 0))
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hum : ∀ j n, AEStronglyMeasurable (u j n) μ)
    (hvm : ∀ j, AEStronglyMeasurable (v j) μ) (hgm : AEStronglyMeasurable g μ) :
    Tendsto (fun n => eLpNorm (f n-g) 1 μ) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hε4 : 0 < ε/4 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨j,hj⟩ := (ENNReal.tendsto_nhds_zero.mp hδ (ε/4) hε4).exists
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hu j) (ε/4) hε4] with n hn
  have htri (a b c : X → ℝ) (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ)
      (hc : AEStronglyMeasurable c μ) : eLpNorm (a-c) 1 μ ≤ eLpNorm (a-b) 1 μ+eLpNorm (b-c) 1 μ := by
    have he : a-c = (a-b)+(b-c) := by ext x; simp
    rw [he]
    exact eLpNorm_add_le (hf := ha.sub hb) (hg := hb.sub hc) (by norm_num)
  calc
    _ ≤ eLpNorm (f n-u j n) 1 μ+eLpNorm (u j n-g) 1 μ := htri _ _ _ (hfm n) (hum j n) hgm
    _ ≤ δ j+(eLpNorm (u j n-v j) 1 μ+δ j) :=
      add_le_add (hf j n) ((htri _ _ _ (hum j n) (hvm j) hgm).trans (add_le_add le_rfl (hg j)))
    _ ≤ ε/4+(ε/4+ε/4) := add_le_add hj (add_le_add hn hj)
    _ ≤ ε := by
      calc
        ε/4+(ε/4+ε/4) ≤ ε/4+(ε/4+(ε/4+ε/4)) := by gcongr; exact le_self_add
        _ = 4*(ε/4) := by ring
        _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Strong velocity averages retain the first moment under a common entropy bound -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem strong_linearMoment_averages
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hfi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hfb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p)
    (hgi : Integrable (entropyGauge g) (μ.prod volume))
    (hgb : (∫ p, entropyGauge g p ∂μ.prod volume) ≤ C)
    (ha : ∀ (ψ : Velocity → ℝ), Measurable ψ → ∀ D : ℝ≥0, (∀ v, |ψ v| ≤ D) →
      Tendsto (fun n => eLpNorm (fun x => (∫ v, ψ v*f n (x,v))-
        (∫ v, ψ v*g (x,v))) 1 μ) atTop (𝓝 0))
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (D : ℝ≥0) (hD : ∀ v, |ψ v| ≤ D) :
    Tendsto (fun n => eLpNorm (fun x => (∫ v, ψ v*linearMoment (f n) (x,v))-
      (∫ v, ψ v*linearMoment g (x,v))) 1 μ) atTop (𝓝 0) := by
  let R : ℕ → ℝ := fun j => (j:ℝ)+1
  have hR j : 0 < R j := by dsimp [R] <;> positivity
  let b : ℕ → Velocity → ℝ := fun j v => if ‖v‖ ≤ R j then ψ v*(1+‖v‖) else 0
  have hbm j : Measurable (b j) := (hψ.mul (measurable_const.add measurable_id.norm)).ite
    (measurableSet_le measurable_id.norm measurable_const) measurable_const
  have hb j v : |b j v| ≤ (D:ℝ)*(1+R j) := by
    dsimp only [b]
    split_ifs with hv
    · rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1+‖v‖)]
      exact mul_le_mul (hD v) (by linarith) (by positivity) D.coe_nonneg
    · simp only [abs_zero]
      positivity
  let A (u : X × Velocity → ℝ) x := ∫ v, ψ v*linearMoment u (x,v)
  let U j (u : X × Velocity → ℝ) x := ∫ v, ψ v*velocityLinearCut (R j) u (x,v)
  have he j (u : X × Velocity → ℝ) x : U j u x = ∫ v, b j v*u (x,v) := by
    apply integral_congr_ae
    apply ae_of_all
    intro v
    dsimp only [b,U,velocityLinearCut,linearMoment]
    split_ifs <;> ring
  have hc j : Tendsto (fun n => eLpNorm (U j (f n)-U j g) 1 μ) atTop (𝓝 0) := by
    change Tendsto (fun n => eLpNorm (fun x => U j (f n) x-U j g x) 1 μ) atTop (𝓝 0)
    simp_rw [he]
    exact ha (b j) (hbm j) ⟨(D:ℝ)*(1+R j),by positivity⟩ (hb j)
  have herr (u : X × Velocity → ℝ) (hum : Measurable u) (hun : ∀ p, 0 ≤ u p)
      (hui : Integrable (entropyGauge u) (μ.prod volume))
      (hub : (∫ p, entropyGauge u p ∂μ.prod volume) ≤ C) j :
      eLpNorm (A u-U j u) 1 μ ≤ ENNReal.ofReal ((D:ℝ)*(2*C/R j)) := by
    apply (weighted_average_difference_le (linearMoment_measurable hum)
      (velocityLinearCut_measurable (R j) hum) (hψ.comp measurable_snd)
      (linearMoment_integrable hum hun hui) (velocityLinearCut_integrable (R j) hum hun hui)
      (fun p => hD p.2)).trans
    rw [ENNReal.ofReal_mul D.coe_nonneg]
    exact mul_le_mul' le_rfl (velocityLinearCut_L1_error (hR j) hum hun hui hub)
  have hδ : Tendsto (fun j => ENNReal.ofReal ((D:ℝ)*(2*C/R j))) atTop (𝓝 0) := by
    have ht : Tendsto (fun j => 2*C/R j) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (ht.const_mul (D:ℝ))
  exact strongL1_of_two_sided_approximations hδ
    (fun j n => herr (f n) (hfm n) (hf n) (hfi n) (hfb n) j)
    (fun j => by rw [eLpNorm_sub_comm]; exact herr g hgm hg hgi hgb j) hc
    (fun n => ((hψ.comp measurable_snd).mul (linearMoment_measurable (hfm n))).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)
    (fun j n => ((hψ.comp measurable_snd).mul
      (velocityLinearCut_measurable (R j) (hfm n))).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)
    (fun j => ((hψ.comp measurable_snd).mul
      (velocityLinearCut_measurable (R j) hgm)).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable)
    ((hψ.comp measurable_snd).mul (linearMoment_measurable hgm)).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Matched mass-normalized second moments give strong scalar averages -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strong_of_normalized_second_moments
    {a r : ℕ → X → ℝ} {A R : X → ℝ}
    (ha : Published.WeakL1Converges μ a A) (hr : Published.WeakL1Converges μ r R)
    (hai : ∀ n, Integrable (a n) μ) (hri : ∀ n, Integrable (r n) μ)
    (hrp : ∀ n x, 0 < r n x) (hRp : ∀ x, 0 < R x)
    {B : ℝ} (hB : 0 < B) (hbound : ∀ n, (∫ x, r n x ∂μ) ≤ B)
    (hsi : ∀ n, Integrable (fun x => (a n x)^2/r n x) μ)
    (C : ℝ≥0) (hA : ∀ᵐ x ∂μ, |A x| ≤ C*R x)
    (hsecond : Tendsto (fun n => ∫ x, (a n x)^2/r n x ∂μ)
      atTop (𝓝 (∫ x, (A x)^2/R x ∂μ)))
    (hstrong : Tendsto (fun n => eLpNorm (fun x => r n x-R x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => a n x-A x) 1 μ) atTop (𝓝 0) := by
  let b := boundedQuotient C A R
  have hbm : Measurable b := boundedQuotient_measurable C ha.1 hr.1
  have hb x : |b x| ≤ C := boundedQuotient_bound C A R x
  have hAe : A =ᵐ[μ] fun x => R x*b x := boundedQuotient_eq_ae C hRp hA
  have he : (∫ x, (A x)^2/R x ∂μ) = ∫ x, (b x*b x)*R x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hAe] with x hx
    rw [hx]
    field_simp [(hRp x).ne']
  rw [he] at hsecond
  exact weighted_moments_strong ha hr hai hri hrp hB hbound hsi hbm C hb hAe hsecond hstrong

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Identified normalized pairs force strong convergence of bounded velocity averages -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

theorem strong_average_of_normalized_pairs
    {f : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hw : Published.WeakL1Converges (μ.prod ν) f g)
    (hp : Published.WeakL1Converges (μ.prod (ν.prod ν))
      (fun n => normalizedPair ν (f n)) (normalizedPair ν g))
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p) (hg : ∀ p, 0 ≤ g p)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν))
    (hm : Tendsto (fun n => eLpNorm (fun x => fiberMass ν (f n) x-fiberMass ν g x) 1 μ)
      atTop (𝓝 0))
    {B : ℝ} (hB : 0 < B) (hbound : ∀ n, (∫ x, 1+fiberMass ν (f n) x ∂μ) ≤ B)
    {ψ : Y → ℝ} (hψ : Measurable ψ) (C : ℝ≥0) (hC : ∀ y, |ψ y| ≤ C) :
    Tendsto (fun n => eLpNorm (fun x =>
      (∫ v, ψ v*f n (x,v) ∂ν)-(∫ v, ψ v*g (x,v) ∂ν)) 1 μ) atTop (𝓝 0) := by
  let a n x := ∫ v, ψ v*f n (x,v) ∂ν
  let A x := ∫ v, ψ v*g (x,v) ∂ν
  let r n x := 1+fiberMass ν (f n) x
  let R x := 1+fiberMass ν g x
  have hrp n x : 0 < r n x := by
    have h : 0 ≤ fiberMass ν (f n) x := integral_nonneg (fun v => hf n (x,v))
    dsimp only [r]
    linarith
  have hRp x : 0 < R x := by
    have h : 0 ≤ fiberMass ν g x := integral_nonneg (fun v => hg (x,v))
    dsimp only [R]
    linarith
  have ha : Published.WeakL1Converges μ a A :=
    hw.marginal hfi (hψ.comp measurable_snd) C (fun z => hC z.2)
  have hai n : Integrable (a n) μ :=
    ((hfi n).bdd_mul (hψ.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ (fun z => hC z.2))).integral_prod_left
  have hri n : Integrable (r n) μ := (integrable_const 1).add (hfi n).integral_prod_left
  have hRi : Integrable R μ := (integrable_const 1).add hw.2.1.integral_prod_left
  have hRm : Measurable R := measurable_const.add (fiberMass_measurable hw.1)
  have hrc : Published.WeakL1Converges μ (fun _ : ℕ => R) R :=
    ⟨hRm,hRi,fun _ _ _ => tendsto_const_nhds⟩
  have hstrong : Tendsto (fun n => eLpNorm (fun x => r n x-R x) 1 μ) atTop (𝓝 0) := by
    simpa only [r,R,add_sub_add_left_eq_sub] using hm
  have hr := hrc.of_eLpNorm_sub (fun _ => hRi) hri hstrong
  have hsi n : Integrable (fun x => (a n x)^2/r n x) μ :=
    normalized_average_square_integrable (hfm n) (hf n) (hfi n) hψ hC
  have hs := (weak_normalized_average_squares hfm hf hfi hp hψ hC).2.2
    (fun _ => 1) measurable_const ⟨1,fun _ => by norm_num⟩
  simp only [one_mul] at hs
  have hAb : ∀ᵐ x ∂μ, |A x| ≤ C*R x := by
    filter_upwards [hw.2.1.prod_right_ae] with x hx
    have he := norm_integral_le_of_norm_le (hx.const_mul (C:ℝ))
      (ae_of_all ν (fun v => show ‖ψ v*g (x,v)‖ ≤ C*g (x,v) from by
        rw [norm_mul,Real.norm_eq_abs,Real.norm_of_nonneg (hg (x,v))]
        exact mul_le_mul_of_nonneg_right (hC v) (hg (x,v))))
    have hb : |A x| ≤ C*fiberMass ν g x := by
      simpa only [A,Real.norm_eq_abs,integral_const_mul,fiberMass] using he
    exact hb.trans (by dsimp only [R] <;> nlinarith [C.coe_nonneg])
  exact strong_of_normalized_second_moments ha hr hai hri hrp hRp hB hbound hsi C hAb hs hstrong

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakConservedMarginal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A conserved integral passes through strong convergence of its density -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem conserved_marginal_of_strong {μ : Measure X} [IsFiniteMeasure μ]
    {ν : Measure Y} [SFinite ν] {F : ℕ → X × Y → ℝ} {g : X × Y → ℝ}
    (hFi : ∀ n, Integrable (F n) (μ.prod ν)) (hgm : Measurable g)
    (hgi : Integrable g (μ.prod ν))
    (hs : Tendsto (fun n => eLpNorm (fun p => F n p-g p) 1 (μ.prod ν)) atTop (𝓝 0))
    {c : ℕ → ℝ} {a : ℝ} (hc : Tendsto c atTop (𝓝 a))
    (he : ∀ n, (fun x => ∫ y, F n (x,y) ∂ν) =ᵐ[μ] fun _ => c n) :
    (fun x => ∫ y, g (x,y) ∂ν) =ᵐ[μ] fun _ => a := by
  have hw := (weakL1_of_eLpNorm_sub hFi hgm hgi hs).marginal hFi
    (k := fun _ => (1:ℝ)) measurable_const 1 (fun _ => by norm_num)
  simp only [one_mul] at hw
  have hconst : WeakL1Converges μ (fun n _ => c n) (fun _ => a) := by
    refine ⟨measurable_const,integrable_const a,?_⟩
    intro ψ _ _
    simp only [integral_mul_const]
    exact tendsto_const_nhds.mul hc
  exact (hw.congr_sequence he).unique hconst

end BoltzmannNonuniqueness.Published

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_CharacteristicCutoffGeometry
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Relative entropy is invariant under torus characteristics -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness

theorem relativeEntropy_eq_lintegral {f : Density} (hf : FiniteEntropyDatum f) :
    ENNReal.ofReal (relativeEntropy f) =
      ∫⁻ p, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (f p)) := by
  have hi := hf.integrable_relativeEntropy
  have he : (fun p => f p*Real.log (f p/maxwellian p.2)-f p+maxwellian p.2) =
      (fun p => scalarRelativeEntropy (maxwellian p.2) (f p)) := by
    funext p
    exact (scalarRelativeEntropy_eq (maxwellian_pos p.2) (f p)).symm
  change ENNReal.ofReal (∫ p, _) = _
  rw [he]
  exact ofReal_integral_eq_lintegral_ofReal (he ▸ hi)
    (hf.1.mono (fun p hp => scalarRelativeEntropy_nonneg (maxwellian_pos p.2) hp))

theorem TorusFlight.scalar_entropy_lintegral_comp {f : Density} (hfm : Measurable f) (t : ℝ) :
    (∫⁻ p : Phase, ENNReal.ofReal
      (scalarRelativeEntropy (maxwellian p.2) (f (TorusFlight.flight t p)))) =
    ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (f p)) := by
  have hmm : Measurable (fun p : Phase => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hm : Measurable (fun p : Phase => scalarRelativeEntropy (maxwellian p.2) (f p)) := by
    unfold scalarRelativeEntropy
    exact ((hfm.mul hfm.log).sub (hfm.mul (measurable_const.add hmm.log))).add hmm
  exact (TorusFlight.flight_measurePreserving t).lintegral_comp hm.ennreal_ofReal

end BoltzmannNonuniqueness

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

end BoltzmannNonuniqueness.TorusFlight

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveRestrictedChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A positive integral budget passes through almost-everywhere convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lintegral_of_ae_tendsto_le {g : ℕ → X → ℝ} {f : X → ℝ} {C : ℝ≥0∞}
    (hgm : ∀ n, Measurable (g n))
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (f x)))
    (hb : ∀ n, (∫⁻ x, ENNReal.ofReal (g n x) ∂μ) ≤ C) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ C := by
  calc
    _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with x hx
      exact (ENNReal.tendsto_ofReal hx).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) atTop :=
      lintegral_liminf_le (fun n => (hgm n).ennreal_ofReal)
    _ ≤ C := liminf_le_of_frequently_le (Eventually.of_forall hb).frequently

end BoltzmannNonuniqueness

end

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

section

/-! # The original datum controls entropy in the global weak limit -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {f : Density} {hfm : Measurable f}

theorem relativeEntropy_of_weak_approximation_sharp
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {μ : Measure ℝ} [IsFiniteMeasure μ] {φ : ℕ → ℕ} {g : ℝ × Phase → ℝ}
    (hφ : StrictMono φ)
    (hg : Published.WeakL1Converges (μ.prod volume)
      (fun n => (approximatingSolution f hfm (φ n)).density) g)
    (hgn : ∀ z, 0 ≤ g z) :
    (∫ z, spacetimeRelativeEntropy g z ∂μ.prod volume) ≤ μ.real univ*relativeEntropy f := by
  have hE n := approximatingSolution_spacetimeEntropy_integrable f hfm hf hi (φ n) μ
  have hH n := approximatingSolution_spacetimeRelativeEntropy f hfm hf hi (φ n) μ
  have hbound n : (∫ z, spacetimeRelativeEntropy (approximatingSolution f hfm (φ n)).density z ∂μ.prod volume) ≤
      μ.real univ*relativeEntropy (initialApproximation ((φ n:ℝ)+1) f) :=
    spacetimeRelativeEntropy_integral_le (hH n).1
      ((approximatingSolution f hfm (φ n)).relativeEntropy_all_times (by positivity) (by positivity))
  have ht := ((initialApproximation_relativeEntropy_tendsto hfm hf hi).comp hφ.tendsto_atTop).const_mul (μ.real univ)
  have hC : 0 ≤ μ.real univ*relativeEntropy f :=
    mul_nonneg (by positivity) (relativeEntropy_nonneg ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩)
  apply le_of_forall_pos_le_add
  intro ε hε
  have he := ht.eventually (gt_mem_nhds (show μ.real univ*relativeEntropy f < μ.real univ*relativeEntropy f+ε by linarith))
  have hcut := hg.entropy_bound
    (fun n => density_integrable_of_spacetimeEntropy
      (approximatingSolution f hfm (φ n)).measurable (approximatingSolution f hfm (φ n)).nonnegative (hE n))
    (fun n => ae_of_all _ (approximatingSolution f hfm (φ n)).nonnegative)
    (ae_of_all _ hgn) (by unfold maxwellian; fun_prop)
    (integrable_maxwellian_phase.comp_snd μ) (ae_of_all _ (fun z => maxwellian_pos z.2.2))
    (fun n => (hH n).1) (add_nonneg hC hε.le) (he.mono (fun n hn => (hbound n).trans hn.le))
  exact hcut.2

theorem GlobalWeakLimit.entropy_ae (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂finiteTimeMeasure, relativeEntropy (fun p => G.density (t,p)) ≤ relativeEntropy f := by
  have hI := (relativeEntropy_of_weak_approximation hf hi G.weighted_weak G.nonnegative).1
  apply ae_le_of_forall_setIntegral_le
    (f := fun t => relativeEntropy (fun p => G.density (t,p)))
    (g := fun _ => relativeEntropy f) ?_ (integrable_const _) ?_
  · convert hI.integral_prod_left using 1
    all_goals try with_reducible_and_instances rfl
    funext t
    apply integral_congr_ae
    exact ae_of_all _ (fun p => (scalarRelativeEntropy_eq (maxwellian_pos p.2) _).symm)
  · intro s hs _hsfin
    have hw := G.weighted_weak.restrict_base hs
    have hh := relativeEntropy_of_weak_approximation_sharp hf hi G.increasing hw G.nonnegative
    have hIs := (relativeEntropy_of_weak_approximation hf hi hw G.nonnegative).1
    rw [integral_prod _ hIs] at hh
    have he (t : ℝ) : (∫ p, spacetimeRelativeEntropy G.density (t,p)) =
        relativeEntropy (fun p => G.density (t,p)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)
    simpa only [he,integral_const,smul_eq_mul] using hh

theorem GlobalWeakLimit.finiteEntropy_ae_volume (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, FiniteEntropyDatum (fun p => G.density (t,p)) ∧
      relativeEntropy (fun p => G.density (t,p)) ≤ relativeEntropy f := by
  have hI := spacetimeEntropy_integrable_of_relativeEntropy G.measurable G.nonnegative
    (relativeEntropy_of_weak_approximation hf hi G.weighted_weak G.nonnegative).1
  have htime : ∀ᵐ t ∂finiteTimeMeasure, FiniteEntropyDatum (fun p => G.density (t,p)) ∧
      relativeEntropy (fun p => G.density (t,p)) ≤ relativeEntropy f := by
    filter_upwards [hI.prod_right_ae,G.entropy_ae hf hi] with t ht hH
    exact ⟨⟨ae_of_all _ (fun p => G.nonnegative (t,p)),
      (G.measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,ht⟩,hH⟩
  have hac : (volume : Measure ℝ) ≪ finiteTimeMeasure :=
    withDensity_absolutelyContinuous' timeWeight_measurable.ennreal_ofReal.aemeasurable
      (ae_of_all _ (fun t => (ENNReal.ofReal_pos.mpr (timeWeight_pos t)).ne'))
  exact hac.ae_le htime

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RightAverageBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Approaching a time from a prescribed full-measure set on its right -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness

theorem exists_right_good_sequence {P : ℝ → Prop} (hP : ∀ᵐ t ∂volume, P t) (t : ℝ) :
    ∃ s : ℕ → ℝ, (∀ n, t < s n ∧ s n < t+1/((n:ℝ)+1) ∧ P (s n)) ∧
      Tendsto s atTop (𝓝 t) := by
  have hx (n : ℕ) : ∃ s, t < s ∧ s < t+1/((n:ℝ)+1) ∧ P s := by
    have hδ : 0 < 1/((n:ℝ)+1) := by positivity
    have hm : (volume : Measure ℝ) (Ioo t (t+1/((n:ℝ)+1))) ≠ 0 := by
      rw [Real.volume_Ioo]
      exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
    obtain ⟨s,hs,hsp⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm (ae_restrict_of_ae hP)
    exact ⟨s,hs.1,hs.2,hsp⟩
  choose s hs using hx
  refine ⟨s,hs,?_⟩
  have hlim : Tendsto (fun n : ℕ => t+1/((n:ℝ)+1)) atTop (𝓝 t) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => (hs n).1.le) (fun n => (hs n).2.1.le)

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_ScalarEntropyJointTrace
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The scalar entropy budget survives almost-everywhere slice convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness

theorem scalarEntropy_trace_bound {U : ℝ × Phase → ℝ} (hUm : Measurable U)
    {s : ℕ → ℝ} {t : ℝ} {C : ℝ≥0∞}
    (hc : ∀ᵐ p ∂(volume : Measure Phase), Tendsto (fun n => U (s n,p)) atTop (𝓝 (U (t,p))))
    (hb : ∀ n, (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (s n,p)))) ≤ C) :
    (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (t,p)))) ≤ C := by
  have hmm : Measurable (fun p : Phase => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hum n : Measurable (fun p : Phase => U (s n,p)) :=
    hUm.comp (measurable_const.prodMk measurable_id)
  have hgm n : Measurable (fun p : Phase => scalarRelativeEntropy (maxwellian p.2) (U (s n,p))) :=
    (((hum n).mul (hum n).log).sub ((hum n).mul (measurable_const.add hmm.log))).add hmm
  apply lintegral_of_ae_tendsto_le hgm _ hb
  filter_upwards [hc] with p hp
  exact ((scalarRelativeEntropy_continuous (maxwellian p.2)).tendsto _).comp hp

end BoltzmannNonuniqueness

end

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

/-! # Strong bounded velocity averages for the actual global collision limit -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.velocity_average_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) {ψ : Velocity → ℝ} (hψ : Measurable ψ)
    (C : ℝ≥0) (hC : ∀ v, |ψ v| ≤ C) :
    Tendsto (fun n => eLpNorm (fun z =>
      (∫ v, ψ v*(approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (z,v))-
      (∫ v, ψ v*G.weakLimit.kineticProfile (z,v)))
      1 ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let K := (volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n p : 0 ≤ F n p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  have hEi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hEb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤ K :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hFi n : Integrable (F n) (μ.prod volume) :=
    integrable_of_entropyGauge (hFm n) (hFn n) (hEi n)
  have hFb n : (∫ p, F n p ∂μ.prod volume) ≤ K :=
    (integral_mono (hFi n) (hEi n) (entropyGauge_ge_density (hFn n))).trans (hEb n)
  have hB : 0 < μ.real univ+|K|+1 := by positivity
  have hbound n : (∫ z, 1+fiberMass volume (F n) z ∂μ) ≤ μ.real univ+|K|+1 := by
    unfold fiberMass
    rw [integral_add (integrable_const 1) (hFi n).integral_prod_left, integral_const]
    simp only [smul_eq_mul,mul_one]
    rw [← integral_prod _ (hFi n)]
    linarith [hFb n,le_abs_self K]
  exact strong_average_of_normalized_pairs (G.weakLimit.kinetic_weak_on_window hT)
    (G.normalized_pairs T hT) hFm hFn (fun p => G.weakLimit.nonnegative _)
    hFi (G.mass_strong T hT) hB hbound hψ C hC

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual strong kernel averages with linear growth in incoming velocity -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem GlobalCollisionLimit.linear_kernel_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) {Z : Type*} [MeasurableSpace Z]
    (τ : Measure Z) [IsFiniteMeasure τ] {k : Z × Velocity → ℝ}
    (hk : Measurable k) (D : ℝ≥0) (hD : ∀ p, |k p| ≤ D*(1+‖p.2‖)) :
    Tendsto (fun n => eLpNorm (fun p : (ℝ × Position) × Z =>
      (∫ v, k (p.2,v)*(approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (p.1,v))-
      (∫ v, k (p.2,v)*G.weakLimit.kineticProfile (p.1,v)))
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod τ)) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let g := G.weakLimit.kineticProfile
  let K := (volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f
  let C := max K (∫ p, entropyGauge g p ∂μ.prod volume)
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n p : 0 ≤ F n p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  have hEi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hEb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤ C := by
    apply le_trans _ (le_max_left _ _)
    exact (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hgm : Measurable g := G.weakLimit.kineticProfile_measurable
  have hgn p : 0 ≤ g p := G.weakLimit.nonnegative _
  have hgi : Integrable (entropyGauge g) (μ.prod volume) := G.weakLimit.kinetic_entropy_on_window hf hi hT
  let b : Z × Velocity → ℝ := fun p => k p/(1+‖p.2‖)
  have hbm : Measurable b := hk.div (measurable_const.add measurable_snd.norm)
  have hb p : |b p| ≤ D := by
    rw [show b p = k p/(1+‖p.2‖) from rfl,abs_div,abs_of_pos (by positivity : 0 < 1+‖p.2‖)]
    exact (div_le_iff₀ (by positivity : 0 < 1+‖p.2‖)).mpr (hD p)
  have he (u : (ℝ × Position) × Velocity → ℝ) (p : (ℝ × Position) × Z) :
      (∫ v, b (p.2,v)*linearMoment u (p.1,v)) = ∫ v, k (p.2,v)*u (p.1,v) := by
    apply integral_congr_ae
    apply ae_of_all
    intro v
    dsimp only [b,linearMoment]
    field_simp [show (1+‖v‖:ℝ) ≠ 0 by positivity]
  obtain ⟨B,hB⟩ := (linearMoment_uniformIntegrable hFm hFn hEi hEb).2
  have h := strong_bounded_kernel_averages (fun n => linearMoment_measurable (hFm n))
    (linearMoment_measurable hgm) (fun n => linearMoment_integrable (hFm n) (hFn n) (hEi n))
    (linearMoment_integrable hgm hgn hgi) (B := B) ENNReal.coe_ne_top hB hbm hb
    (fun z => strong_linearMoment_averages hFm hFn hEi hEb hgm hgn hgi (le_max_right _ _)
      (fun ψ hψ E hE => G.velocity_average_strong hf hi hT hψ E hE)
      (hbm.comp (measurable_const.prodMk measurable_id)) D (fun v => hb (z,v)))
    (τ := τ)
  simpa only [he] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

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

/-! # Scalar physical velocity averages retain their linear growth -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_velocity_average_strong
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) {T : ℝ} (hT : 0 ≤ T)
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (D : ℝ≥0) (hD : ∀ v, |ψ v| ≤ D*(1+‖v‖)) :
    Tendsto (fun n => eLpNorm (fun z : ℝ × Position =>
      (∫ v, ψ v*(approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (z,v))-
      (∫ v, ψ v*G.weakLimit.kineticProfile (z,v))) 1
        ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let τ : Measure Unit := Measure.dirac ()
  let A n z := ∫ v, ψ v*(approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile (z,v)
  let B z := ∫ v, ψ v*G.weakLimit.kineticProfile (z,v)
  have hAm n : Measurable (A n) :=
    ((hψ.comp measurable_snd).mul
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable).stronglyMeasurable.integral_prod_right'.measurable
  have hBm : Measurable B := ((hψ.comp measurable_snd).mul
    G.weakLimit.kineticProfile_measurable).stronglyMeasurable.integral_prod_right'.measurable
  have ht := G.linear_kernel_strong hf hi hT τ
    (k := fun p : Unit × Velocity => ψ p.2) (hψ.comp measurable_snd) D (fun p => hD p.2)
  have he n : eLpNorm ((A n-B) ∘ Prod.fst) 1 (μ.prod τ) = eLpNorm (A n-B) 1 μ :=
    eLpNorm_comp_measurePreserving ((hAm n).sub hBm).aestronglyMeasurable measurePreserving_fst
  change Tendsto (fun n => eLpNorm ((A n-B) ∘ Prod.fst) 1 (μ.prod τ)) atTop (𝓝 0) at ht
  have he' n : (A n-B) = (fun z => A n z-B z) := by ext z; rfl
  change Tendsto (fun n => eLpNorm (fun z => A n z-B z) 1 μ) atTop (𝓝 0)
  simp only [he] at ht
  simpa only [he'] using ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Conserved linear moments of the same global collision limit -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.conserved_linear_moment_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (D : ℝ≥0)
    (hD : ∀ v, |ψ v| ≤ D*(1+‖v‖))
    (hc : ∀ n t, (∫ p : Phase, ψ p.2*(approximatingSolution f hfm n).density (t,p)) =
      ∫ p : Phase, ψ p.2*initialApproximation ((n:ℝ)+1) f p)
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫ p : Phase, ψ p.2*G.weakLimit.density (t,p)) = ∫ p : Phase, ψ p.2*f p := by
  let μ := volume.restrict (Icc 0 T)
  let S n := approximatingSolution f hfm (G.weakLimit.indices n)
  let A n (z : ℝ × Position) := ∫ v, ψ v*(S n).kineticProfile (z,v)
  let B (z : ℝ × Position) := ∫ v, ψ v*G.weakLimit.kineticProfile (z,v)
  have hEi n : Integrable (entropyGauge (S n).kineticProfile) ((μ.prod volume).prod volume) :=
    (S n).kinetic_entropy_integrable (μ := μ) (by positivity)
      (approximatingSolution_entropy f hfm hf hi _)
  have hAi n : Integrable (A n) (μ.prod volume) :=
    (linearVelocityTest_integrable (S n).kineticProfile_measurable
      (fun p => (S n).nonnegative _) (hEi n) hψ D hD).integral_prod_left
  have hBi : Integrable B (μ.prod volume) :=
    (linearVelocityTest_integrable G.weakLimit.kineticProfile_measurable
      (fun p => G.weakLimit.nonnegative _) (G.weakLimit.kinetic_entropy_on_window hf hi hT)
      hψ D hD).integral_prod_left
  have hBm : Measurable B := ((hψ.comp measurable_snd).mul
    G.weakLimit.kineticProfile_measurable).stronglyMeasurable.integral_prod_right'.measurable
  have ha n t : (∫ x, A n (t,x)) =
      ∫ p : Phase, ψ p.2*initialApproximation (((G.weakLimit.indices n):ℝ)+1) f p := by
    have hsi := linearVelocityTest_integrable
      ((S n).measurable.comp (measurable_const.prodMk measurable_id))
      (fun p => (S n).nonnegative _) ((S n).finiteEntropy (by positivity) t).2.2 hψ D hD
    have he := integral_prod (fun p : Phase => ψ p.2*(S n).density (t,p)) hsi
    exact he.symm.trans (hc _ t)
  have hout := Published.conserved_marginal_of_strong hAi hBm hBi
    (G.linear_velocity_average_strong hf hi hT hψ D hD)
    ((initialApproximation_linear_moment_tendsto hfm hf hi hψ D hD).comp
      G.weakLimit.increasing.tendsto_atTop)
    (fun n => ae_of_all μ (ha n))
  filter_upwards [hout, (G.weakLimit.finiteEntropy_ae_volume hf hi).filter_mono
    (ae_mono Measure.restrict_le_self)] with t ht hfinite
  have hti := linearVelocityTest_integrable
    (G.weakLimit.measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => G.weakLimit.nonnegative _) hfinite.1.2.2 hψ D hD
  exact (integral_prod (fun p : Phase => ψ p.2*G.weakLimit.density (t,p)) hti).trans ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Mass and total momentum of the actual global limit -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.conserved_linear_moment_ae_nonneg
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {ψ : Velocity → ℝ} (hψ : Measurable ψ) (D : ℝ≥0)
    (hD : ∀ v, |ψ v| ≤ D*(1+‖v‖))
    (hc : ∀ n t, (∫ p : Phase, ψ p.2*(approximatingSolution f hfm n).density (t,p)) =
      ∫ p : Phase, ψ p.2*initialApproximation ((n:ℝ)+1) f p) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      (∫ p : Phase, ψ p.2*G.weakLimit.density (t,p)) = ∫ p : Phase, ψ p.2*f p := by
  have hh n := G.conserved_linear_moment_ae hf hi hψ D hD hc (Nat.cast_nonneg n)
  simp only [ae_restrict_iff' measurableSet_Icc] at hh
  filter_upwards [ae_all_iff.mpr hh] with t ht
  intro ht0
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact ht n ⟨ht0,hn⟩

theorem GlobalCollisionLimit.momentum_conservation_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (i : Fin 3) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      (∫ p : Phase, (p.2 i)*G.weakLimit.density (t,p)) = ∫ p : Phase, (p.2 i)*f p := by
  have hc n t : (∫ p : Phase, (p.2 i)*(approximatingSolution f hfm n).density (t,p)) =
      ∫ p : Phase, (p.2 i)*initialApproximation ((n:ℝ)+1) f p := by
    let S := approximatingSolution f hfm n
    calc
      _ = ∫ p : Phase, (p.2 i)*S.density (PositiveIntegral.time ((n:ℝ)+1) t,p) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun p => congrArg (fun a => (p.2 i)*a) (S.density_clipped (by positivity) t p))
      _ = _ := S.momentum_coordinate_conservation (by positivity) i (PositiveIntegral.time_bounds (by positivity) t)
  apply G.conserved_linear_moment_ae_nonneg hf hi (ψ := fun v => v i) (by fun_prop) 1 _ hc
  intro v
  have hv : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  simpa only [NNReal.coe_one,one_mul] using hv.trans (by linarith : ‖v‖ ≤ 1+‖v‖)

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

section

/-! # Slice convergence of the actual characteristic profile -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_profile_slice_tendsto
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc 0 T) (hst : Tendsto s atTop (𝓝 t)) :
    ∀ᵐ p ∂(volume : Measure Phase),
      Tendsto (fun n => physicalLinearProfile f G.weakLimit.kineticProfile (s n,p))
        atTop (𝓝 (physicalLinearProfile f G.weakLimit.kineticProfile (t,p))) := by
  filter_upwards [G.linear_profile_absolutelyContinuous hf hi] with p hp
  have hc : ContinuousOn (fun r => physicalLinearProfile f G.weakLimit.kineticProfile (r,p))
      (Icc 0 T) := by
    simpa only [uIcc_of_le hT] using (hp T hT).continuousOn
  exact (hc.continuousWithinAt ht).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hst,Eventually.of_forall hs⟩)

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

/-! # The original entropy budget holds almost everywhere along the linear profile -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_entropy_bound_ae_on_window
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
        (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)))) ≤
      ENNReal.ofReal (relativeEntropy f) := by
  filter_upwards [Measure.ae_ae_of_ae_prod (G.linear_profile_eq_density_q80 hf hi hT),
    ae_restrict_of_ae (G.weakLimit.finiteEntropy_ae_volume hf hi)] with t he hdata
  calc
    _ = ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
        (G.weakLimit.density (t,TorusFlight.flight t p))) :=
      lintegral_congr_ae (he.mono (fun p hp => by rw [hp]))
    _ = ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
        (G.weakLimit.density (t,p))) :=
      TorusFlight.scalar_entropy_lintegral_comp
        (G.weakLimit.measurable.comp (measurable_const.prodMk measurable_id)) t
    _ = ENNReal.ofReal (relativeEntropy (fun p => G.weakLimit.density (t,p))) :=
      (relativeEntropy_eq_lintegral hdata.1).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hdata.2

theorem GlobalCollisionLimit.linear_entropy_bound_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
        (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)))) ≤
      ENNReal.ofReal (relativeEntropy f) := by
  have hh n := G.linear_entropy_bound_ae_on_window hf hi (Nat.cast_nonneg n)
  simp only [ae_restrict_iff' measurableSet_Icc] at hh
  filter_upwards [ae_all_iff.mpr hh] with t ht
  intro ht0
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact ht n ⟨ht0,hn⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The entropy bound and finite entropy at every characteristic time -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_entropy_bound
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
      (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)))) ≤
      ENNReal.ofReal (relativeEntropy f) := by
  obtain ⟨s,hs,hst⟩ := exists_right_good_sequence (G.linear_entropy_bound_ae hf hi) t
  have hsm n : s n ∈ Icc 0 (t+1) := by
    have hδ : 1/((n:ℝ)+1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨ht.trans (hs n).1.le,(hs n).2.1.le.trans (add_le_add le_rfl hδ)⟩
  have hc := G.linear_profile_slice_tendsto hf hi (show 0 ≤ t+1 by linarith)
    (show t ∈ Icc 0 (t+1) from ⟨ht,by linarith⟩) hsm hst
  exact scalarEntropy_trace_bound
    (U := physicalLinearProfile f G.weakLimit.kineticProfile)
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable)
    hc (fun n => (hs n).2.2 (ht.trans (hs n).1.le))

theorem GlobalCollisionLimit.linear_finiteEntropy
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteEntropyDatum (fun p : Phase => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) := by
  have hum : Measurable (fun p : Phase => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) :=
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      (measurable_const.prodMk measurable_id)
  have hun p : 0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile (t,p) :=
    physicalLinearProfile_nonneg hf (fun _ => G.weakLimit.nonnegative _) ht p
  have hmm : Measurable (fun p : Phase => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hH : Integrable (fun p : Phase => scalarRelativeEntropy (maxwellian p.2)
      (physicalLinearProfile f G.weakLimit.kineticProfile (t,p))) := by
    refine ⟨?_,(hasFiniteIntegral_iff_ofReal ?_).mpr
      ((G.linear_entropy_bound hf hi ht).trans_lt ENNReal.ofReal_lt_top)⟩
    · exact (((hum.mul hum.log).sub (hum.mul (measurable_const.add hmm.log))).add hmm).aestronglyMeasurable
    · exact ae_of_all _ (fun p => scalarRelativeEntropy_nonneg (maxwellian_pos p.2) (hun p))
  exact finiteEntropy_of_relativeEntropy_integrable hum hun hH

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # A common entropy-moment budget for every characteristic time -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_relativeEntropy_le
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    relativeEntropy (fun p => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) ≤
      relativeEntropy f := by
  have hb := G.linear_entropy_bound hf hi ht
  rw [← relativeEntropy_eq_lintegral (G.linear_finiteEntropy hf hi ht)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (relativeEntropy_nonneg
    (show FiniteEntropyDatum f from ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩))).mp hb

theorem GlobalCollisionLimit.linear_entropyMoment_le
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ p, entropyMoment (fun p => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) p) ≤
      physicalEntropyBudget f := by
  have hb := entropyMoment_integral_control (G.linear_finiteEntropy hf hi ht)
  apply hb.trans
  dsimp only [physicalEntropyBudget]
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left (G.linear_relativeEntropy_le hf hi ht)
  have := entropyMomentCoefficient_nonneg
  positivity

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong L1 time continuity of the nonlinear characteristic profile -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_profile_strong_seq
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc 0 T) (hst : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun n => eLpNorm (fun p : Phase =>
      physicalLinearProfile f G.weakLimit.kineticProfile (s n,p)-
        physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) 1 volume) atTop (𝓝 0) := by
  let U (r : ℝ) (p : Phase) := physicalLinearProfile f G.weakLimit.kineticProfile (r,p)
  have hum n : Measurable (U (s n)) :=
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      (measurable_const.prodMk measurable_id)
  have hun n p : 0 ≤ U (s n) p :=
    physicalLinearProfile_nonneg hf (fun _ => G.weakLimit.nonnegative _) (hs n).1 p
  have hui n : Integrable (entropyGauge (U (s n))) := (G.linear_finiteEntropy hf hi (hs n).1).2.2
  have hub n : (∫ p, entropyGauge (U (s n)) p) ≤ physicalEntropyBudget f :=
    G.linear_entropyMoment_le hf hi (hs n).1
  have hUI := uniformIntegrable_of_entropyGauge (μ := (volume : Measure Position)) hum hun hui hub
  have hUT := unifTight_of_entropyGauge (μ := (volume : Measure Position)) hum hun hui hub
  have hmem := memLp_one_iff_integrable.mpr (G.linear_finiteEntropy hf hi ht.1).integrable
  exact tendsto_Lp_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => (hum n).aestronglyMeasurable) hmem hUI.1 hUT
    (G.linear_profile_slice_tendsto hf hi hT ht hs hst)

theorem GlobalCollisionLimit.linear_profile_strong_continuous
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => eLpNorm (fun p : Phase =>
      physicalLinearProfile f G.weakLimit.kineticProfile (s,p)-
        physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro s hs
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_mem_of_tendsto_nhdsWithin hs)
  have hst := (tendsto_nhds_of_tendsto_nhdsWithin hs).comp (tendsto_add_atTop_nat N)
  have hh := G.linear_profile_strong_seq hf hi hT ht
    (fun n => hN (n+N) (Nat.le_add_left N n)) hst
  exact (tendsto_add_atTop_iff_nat N).mp hh

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The measurable nonnegative evolution defined by the characteristic profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalEvolution_measurable {f : Density} (hfm : Measurable f)
    {F : (ℝ × Position) × Velocity → ℝ} (hFm : Measurable F) :
    Measurable (fun z : ℝ × Phase => physicalEvolution f F z.1 z.2) := by
  apply measurable_const.max
  exact (physicalLinearProfile_measurable hfm hFm).comp
    (measurable_fst.prodMk (TorusFlight.measurable_flight.comp
      (measurable_fst.neg.prodMk measurable_snd)))

theorem physicalEvolution_nonneg (f : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (t : ℝ) (p : Phase) : 0 ≤ physicalEvolution f F t p := le_max_left _ _

theorem GlobalCollisionLimit.physicalEvolution_eq_density
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase),
      physicalEvolution f G.weakLimit.kineticProfile z.1 z.2 = G.weakLimit.density z := by
  have he := (TorusFlight.back_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae
    (G.linear_profile_eq_density_q80 hf hi hT)
  have ht : ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase), z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [he,ht] with z hz hzt
  change max 0 (physicalLinearProfile f G.weakLimit.kineticProfile
    (z.1,TorusFlight.flight (-z.1) z.2)) = _
  have hpos : 0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile
      (z.1,TorusFlight.flight (-z.1) z.2) :=
    physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) hzt.1 _
  rw [max_eq_right hpos]
  simpa only [TorusFlight.neg_flight,Prod.eta] using hz

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Every-time finite entropy and strong L1 traces in physical coordinates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalEvolution_eq {f : Density} (hf : ∀ p, 0 ≤ f p)
    {F : (ℝ × Position) × Velocity → ℝ} (hF : ∀ p, 0 ≤ F p)
    {t : ℝ} (ht : 0 ≤ t) (p : Phase) :
    physicalEvolution f F t p = physicalLinearProfile f F (t,TorusFlight.flight (-t) p) :=
  max_eq_right (physicalLinearProfile_nonneg hf hF ht _)

theorem GlobalCollisionLimit.physical_finiteEntropy
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) : FiniteEntropyDatum (physicalEvolution f G.weakLimit.kineticProfile t) := by
  let U := fun p : Phase => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)
  have he : physicalEvolution f G.weakLimit.kineticProfile t =
      (fun p => U (TorusFlight.flight (-t) p)) :=
    funext (physicalEvolution_eq (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht)
  rw [he]
  exact (G.linear_finiteEntropy hf hi ht).comp_flight (-t)

theorem GlobalCollisionLimit.physical_entropyMoment_le
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ p, entropyMoment (physicalEvolution f G.weakLimit.kineticProfile t) p) ≤ physicalEntropyBudget f := by
  have hUm : Measurable (fun p : Phase => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) :=
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable).comp
    ((measurable_const (a := t)).prodMk measurable_id)
  have heq : physicalEvolution f G.weakLimit.kineticProfile t =
      (fun p => physicalLinearProfile f G.weakLimit.kineticProfile
        (t,TorusFlight.flight (-t) p)) :=
    funext (physicalEvolution_eq (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht)
  rw [heq,TorusFlight.entropyMoment_integral_comp hUm (-t)]
  exact G.linear_entropyMoment_le hf hi ht

theorem GlobalCollisionLimit.physical_strong_continuous
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => eLpNorm (fun p : Phase =>
      physicalEvolution f G.weakLimit.kineticProfile s p-
        physicalEvolution f G.weakLimit.kineticProfile t p) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hh := TorusFlight.strong_curve_flight
    (C := fun r p => physicalLinearProfile f G.weakLimit.kineticProfile (r,p))
    (fun r hr => (G.linear_finiteEntropy hf hi hr.1).integrable) ht
    (G.linear_profile_strong_continuous hf hi hT ht)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  apply congrArg (fun g : Phase → ℝ => eLpNorm g 1 volume)
  funext p
  rw [physicalEvolution_eq (F := G.weakLimit.kineticProfile) hf (fun _ => G.weakLimit.nonnegative _) hs.1,
    physicalEvolution_eq (F := G.weakLimit.kineticProfile) hf (fun _ => G.weakLimit.nonnegative _) ht.1]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Bounded and linear-velocity tests of the physical time traces -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_weak_seq
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc 0 T) (hst : Tendsto s atTop (𝓝 t)) :
    Published.WeakL1Converges volume
      (fun n => physicalEvolution f G.weakLimit.kineticProfile (s n))
      (physicalEvolution f G.weakLimit.kineticProfile t) := by
  apply Published.weakL1_of_strong
    ((physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      (measurable_const.prodMk measurable_id))
    (G.physical_finiteEntropy hf hi ht.1).integrable
    (fun n => (G.physical_finiteEntropy hf hi (hs n).1).integrable)
  exact (G.physical_strong_continuous hf hi hT ht).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hst,Eventually.of_forall hs⟩)

theorem GlobalCollisionLimit.physical_linearMoment_weak_seq
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc 0 T) (hst : Tendsto s atTop (𝓝 t)) :
    Published.WeakL1Converges volume
      (fun n => linearMoment (physicalEvolution f G.weakLimit.kineticProfile (s n)))
      (linearMoment (physicalEvolution f G.weakLimit.kineticProfile t)) := by
  apply weak_linearMoment
    (fun n => (physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      (measurable_const.prodMk measurable_id))
    (fun _ _ => physicalEvolution_nonneg _ _ _ _)
    (fun n => (G.physical_finiteEntropy hf hi (hs n).1).2.2)
    (fun n => G.physical_entropyMoment_le hf hi (hs n).1)
    ((physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      (measurable_const.prodMk measurable_id))
    (fun _ => physicalEvolution_nonneg _ _ _ _)
    (G.physical_finiteEntropy hf hi ht.1).2.2
    (G.physical_entropyMoment_le hf hi ht.1)
    (G.physical_weak_seq hf hi hT ht hs hst)

theorem GlobalCollisionLimit.physical_linear_test_seq
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc 0 T) (hst : Tendsto s atTop (𝓝 t))
    {ψ : Phase → ℝ} (hψ : Measurable ψ) (D : ℝ)
    (hD : ∀ p, |ψ p| ≤ D*(1+‖p.2‖)) :
    Tendsto (fun n => ∫ p, ψ p*physicalEvolution f G.weakLimit.kineticProfile (s n) p)
      atTop (𝓝 (∫ p, ψ p*physicalEvolution f G.weakLimit.kineticProfile t p)) := by
  let a : Phase → ℝ := fun p => ψ p/(1+‖p.2‖)
  have ham : Measurable a := hψ.div (measurable_const.add measurable_snd.norm)
  have hab p : |a p| ≤ D := by
    dsimp only [a]
    rw [abs_div,abs_of_pos (by positivity : (0:ℝ) < 1+‖p.2‖)]
    exact (div_le_iff₀ (by positivity)).mpr (hD p)
  have he (u : Phase → ℝ) : (fun p => a p*linearMoment u p) = (fun p => ψ p*u p) := by
    funext p
    dsimp only [a,linearMoment]
    field_simp
  have hh := (G.physical_linearMoment_weak_seq hf hi hT ht hs hst).2.2 a ham ⟨D,hab⟩
  simpa only [he] using hh

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # A single almost-everywhere comparison of the physical evolution and weak limit -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_eq_density_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      physicalEvolution f G.weakLimit.kineticProfile t =ᵐ[volume]
        (fun p => G.weakLimit.density (t,p)) := by
  have hh n := Measure.ae_ae_of_ae_prod
    (G.physicalEvolution_eq_density hf hi (Nat.cast_nonneg n))
  simp only [ae_restrict_iff' measurableSet_Icc] at hh
  filter_upwards [ae_all_iff.mpr hh] with t ht
  intro ht0
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact ht n ⟨ht0,hn⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalGlobalRenormalized
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Mass and momentum conservation at every nonnegative physical time -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_conserved_test
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {ψ : Phase → ℝ} (hψ : Measurable ψ) (D : ℝ)
    (hD : ∀ p, |ψ p| ≤ D*(1+‖p.2‖))
    (hc : ∀ᵐ t ∂volume, 0 ≤ t →
      (∫ p : Phase, ψ p*G.weakLimit.density (t,p)) = ∫ p, ψ p*f p)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ p, ψ p*physicalEvolution f G.weakLimit.kineticProfile t p) = ∫ p, ψ p*f p := by
  have he : ∀ᵐ r ∂volume, 0 ≤ r →
      (∫ p, ψ p*physicalEvolution f G.weakLimit.kineticProfile r p) = ∫ p, ψ p*f p := by
    filter_upwards [G.physical_eq_density_ae hf hi,hc] with r hr hc
    intro hr0
    exact (integral_congr_ae ((hr hr0).mono (fun p hp => congrArg (fun a => ψ p*a) hp))).trans (hc hr0)
  obtain ⟨s,hs,hst⟩ := exists_right_good_sequence he t
  have hsm n : s n ∈ Icc 0 (t+1) := by
    have hδ : 1/((n:ℝ)+1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨ht.trans (hs n).1.le,(hs n).2.1.le.trans (add_le_add le_rfl hδ)⟩
  have hh := G.physical_linear_test_seq hf hi (show 0 ≤ t+1 by linarith)
    (show t ∈ Icc 0 (t+1) from ⟨ht,by linarith⟩) hsm hst hψ D hD
  have heq n := (hs n).2.2 (hsm n).1
  simp only [heq] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds

theorem GlobalCollisionLimit.physical_momentum_coordinate
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (i : Fin 3) {t : ℝ} (ht : 0 ≤ t) :
    (∫ p : Phase, p.2 i*physicalEvolution f G.weakLimit.kineticProfile t p) =
      ∫ p : Phase, p.2 i*f p := by
  apply G.physical_conserved_test hf hi (ψ := fun p => p.2 i) (by fun_prop) 1 _
    (G.momentum_conservation_ae hf hi i) ht
  intro p
  have hv : |p.2 i| ≤ ‖p.2‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p.2 i
  simpa only [one_mul] using hv.trans (by linarith : ‖p.2‖ ≤ 1+‖p.2‖)

theorem GlobalCollisionLimit.physical_momentum_conservation_q80_oai
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    momentum (physicalEvolution f G.weakLimit.kineticProfile t) = momentum f := by
  apply PiLp.ext
  intro i
  let L := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i
  have h₁ := L.integral_comp_comm
    (show FiniteEntropyDatum f from ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩).integrable_momentum
  have h₂ := L.integral_comp_comm (G.physical_finiteEntropy hf hi ht).integrable_momentum
  change (momentum (physicalEvolution f G.weakLimit.kineticProfile t)) i = (momentum f) i
  simp only [L,PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul] at h₁ h₂
  unfold momentum
  rw [← h₂,← h₁]
  simpa only [mul_comm] using G.physical_momentum_coordinate hf hi i ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_momentum_conservation_q80_oai := @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_momentum_conservation_q80_oai
