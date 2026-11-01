-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_in_measure_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:10:33.975914+00:00
-- url     : https://prove2.me/submissions/e9dedb79-e068-4f0f-8b8a-eb70551a0968

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002
import Theorems.Thm_OAI_BoltzmannNonuniqueness_PeriodicApproximation_GlobalCollisionLimit_normalized_gain_strong_q80

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

protected theorem ae_mono (hg : UnifIntegrable g p μ)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ)
    (hfg : ∀ i, (‖f i ·‖ₑ) ≤ᵐ[μ] (‖g i ·‖ₑ)) :
    UnifIntegrable f p μ :=
  of_enn (fun ε hε => (hg.enn_spec ε hε).imp fun _ ⟨hδ, h⟩ => ⟨hδ, fun i s hs =>
    (eLpNorm_mono_enorm_ae ((hfg i).filter_mono ae_restrict_le)).trans (h i s hs)⟩) hf_meas

/-- Uniform integrability is preserved by restriction of the measure to a set. -/
protected theorem restrict (hf : UnifIntegrable f p μ) (s : Set α) :
    UnifIntegrable f p (μ.restrict s) :=
  ⟨hf.1.restrict s, fun i => (hf.2 i).restrict⟩

end UnifIntegrable

/-! ### `UniformIntegrable` -/

namespace UniformIntegrable

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

end BoltzmannNonuniqueness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AverageMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The product step for strongly convergent scalar velocity averages -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Compactness

theorem tendstoInMeasure_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {f g : ℕ → X → ℝ} {a b : X → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ) (hgm : ∀ n, AEStronglyMeasurable (g n) μ)
    (hf : TendstoInMeasure μ f atTop a) (hg : TendstoInMeasure μ g atTop b) :
    TendstoInMeasure μ (fun n x => f n x*g n x) atTop (fun x => a x*b x) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff (fun n => (hfm n).mul (hgm n))).mpr
  intro ns hns
  obtain ⟨i,hi,hfi⟩ := (hf.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  obtain ⟨j,hj,hgj⟩ := (hg.comp (hns.comp hi).tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨i ∘ j,hi.comp hj,?_⟩
  filter_upwards [hfi,hgj] with x hfx hgx
  exact (hfx.comp hj.tendsto_atTop).mul hgx

end BoltzmannNonuniqueness.Compactness

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instNonemptySupportedTest
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

/-! # Uniform integrability removes bounded multipliers that vanish in L1 -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness

theorem tendsto_L1_mul_uniformIntegrable
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f a : ℕ → X → ℝ} (hf : UniformIntegrable f 1 μ)
    (hfm : ∀ n, Measurable (f n)) (ham : ∀ n, Measurable (a n))
    (ha0 : Tendsto (fun n => eLpNorm (a n) 1 μ) atTop (𝓝 0))
    (C : ℝ≥0) (ha : ∀ n x, |a n x| ≤ C) :
    Tendsto (fun n => eLpNorm (fun x => a n x*f n x) 1 μ) atTop (𝓝 0) := by
  let D : ℝ≥0 := C+1
  have hD : (0 : ℝ≥0∞) < D := by simp [D]
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hε2 : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  have hε' : 0 < (ε/2)/(D:ℝ≥0∞) :=
    ENNReal.div_pos hε2.ne' ENNReal.coe_ne_top
  obtain ⟨K,hK⟩ := hf.spec (by norm_num : (1:ℝ≥0∞) ≠ 0) (by norm_num) hε'
  let u (n : ℕ) : X → ℝ := {x | ‖f n x‖₊ < K}.indicator (f n)
  have hum n : Measurable (u n) :=
    (hfm n).indicator (measurableSet_lt (hfm n).nnnorm measurable_const)
  have hub n x : |u n x| ≤ K := by
    by_cases hx : ‖f n x‖₊ < K
    · simpa [u,hx,Real.norm_eq_abs] using
        (show ‖f n x‖ ≤ (K:ℝ) by exact_mod_cast hx.le)
    · simp [u,hx]
  have hue n : eLpNorm (fun x => f n x-u n x) 1 μ ≤ (ε/2)/(D:ℝ≥0∞) := by
    have he : (fun x => f n x-u n x) = {x | K ≤ ‖f n x‖₊}.indicator (f n) := by
      funext x
      by_cases hx : ‖f n x‖₊ < K
      · simp [u,hx,not_le.mpr hx]
      · simp [u,hx,le_of_not_gt hx]
    rw [he]
    exact hK n
  have hs : Tendsto (fun n => eLpNorm (fun x => a n x*u n x) 1 μ) atTop (𝓝 0) := by
    have h := tendsto_L1_bounded_mul_zero
      (fun n => (ham n).aestronglyMeasurable) (fun n => (hum n).aestronglyMeasurable)
      ha0 K.coe_nonneg (Eventually.of_forall (fun n => ae_of_all _ (hub n)))
    simpa only [mul_comm] using h
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hs (ε/2) hε2] with n hn
  have herr : eLpNorm (fun x => a n x*(f n x-u n x)) 1 μ ≤ ε/2 := by
    have hb := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (ae_of_all μ (fun x => show ‖a n x*(f n x-u n x)‖₊ ≤ D*‖f n x-u n x‖₊ from by
        apply NNReal.coe_le_coe.mp
        change |a n x*(f n x-u n x)| ≤ (D:ℝ)*|f n x-u n x|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right ((ha n x).trans (by dsimp [D] <;> norm_num)) (abs_nonneg _)))
      (p := 1)
    calc
      _ ≤ (D:ℝ≥0∞)*eLpNorm (fun x => f n x-u n x) 1 μ := hb
      _ ≤ (D:ℝ≥0∞)*((ε/2)/(D:ℝ≥0∞)) := mul_le_mul' le_rfl (hue n)
      _ = ε/2 := ENNReal.mul_div_cancel hD.ne' ENNReal.coe_ne_top
  have he : (fun x => a n x*f n x) =
      (fun x => a n x*(f n x-u n x))+(fun x => a n x*u n x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [he]
  exact (eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)).trans ((add_le_add herr hn).trans_eq ε.add_halves)

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

theorem uniformIntegrable_tensor {μ : Measure X} {ν : Measure Y}
    [IsFiniteMeasure μ] [SFinite ν] {f : ℕ → X → ℝ} {g : Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hui : UniformIntegrable f 1 μ)
    (hgm : Measurable g) (hgi : Integrable g ν) :
    UniformIntegrable (fun (n : ℕ) (p : X × Y) => f n p.1*g p.2) 1 (μ.prod ν) := by
  have hd (j : ℕ) : 0 < ENNReal.ofReal (1/((j:ℝ)+1)) := by positivity
  choose C hC using (fun j => hui.spec (by norm_num : (1:ℝ≥0∞) ≠ 0)
    (by norm_num : (1:ℝ≥0∞) ≠ ∞) (hd j))
  let u (j n : ℕ) : X → ℝ := {x | ‖f n x‖₊ < C j}.indicator (f n)
  have hum (j n : ℕ) : Measurable (u j n) :=
    (hfm n).indicator (measurableSet_lt (hfm n).nnnorm measurable_const)
  have hub (j n : ℕ) (x : X) : |u j n x| ≤ (C j : ℝ) := by
    by_cases hx : ‖f n x‖₊ < C j
    · simpa [u,hx,Real.norm_eq_abs] using
        (show ‖f n x‖ ≤ (C j:ℝ) by exact_mod_cast hx.le)
    · simp [u,hx]
  have hue (j n : ℕ) : eLpNorm (fun x => f n x-u j n x) 1 μ ≤ ENNReal.ofReal (1/((j:ℝ)+1)) := by
    have he : (fun x => f n x-u j n x) = {x | C j ≤ ‖f n x‖₊}.indicator (f n) := by
      funext x
      by_cases hx : ‖f n x‖₊ < C j
      · simp [u,hx,not_le.mpr hx]
      · simp [u,hx,le_of_not_gt hx]
    rw [he]
    exact hC j n
  apply uniformIntegrable_of_approximation (g := fun j n p => u j n p.1*g p.2)
  · intro j
    let b : X × Y → ℝ := fun p => (C j:ℝ)*|g p.2|
    have hbi : Integrable b (μ.prod ν) := (integrable_const (C j:ℝ)).mul_prod hgi.abs
    have hbui := uniformIntegrable_const (ι := ℕ) (by norm_num : (1:ℝ≥0∞) ≤ 1)
      (by norm_num) (memLp_one_iff_integrable.mpr hbi)
    have hm n : AEStronglyMeasurable (fun p : X × Y => u j n p.1*g p.2) (μ.prod ν) :=
      ((hum j n).comp measurable_fst |>.mul (hgm.comp measurable_snd)).aestronglyMeasurable
    have he n : ∀ᵐ p : X × Y ∂μ.prod ν, ‖u j n p.1*g p.2‖ₑ ≤ ‖b p‖ₑ := by
      filter_upwards [] with p
      apply enorm_le_iff_norm_le.mpr
      rw [Real.norm_eq_abs,abs_mul,Real.norm_of_nonneg (mul_nonneg (C j).coe_nonneg (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hub j n p.1) (abs_nonneg _)
    obtain ⟨hu,K,hK⟩ := hbui
    exact ⟨hu.ae_mono hm he,K,fun n => (eLpNorm_mono_enorm_ae (he n)).trans (hK n)⟩
  · intro ε hε
    have hdlim : Tendsto (fun j : ℕ => ENNReal.ofReal (1/((j:ℝ)+1))) atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
        (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds) :
          Tendsto (fun j : ℕ => (1:ℝ)/((j:ℝ)+1)) atTop (𝓝 0))
    have hp := ENNReal.Tendsto.mul_const hdlim (Or.inr (memLp_one_iff_integrable.mpr hgi).eLpNorm_ne_top)
    simp only [zero_mul] at hp
    obtain ⟨j,hj⟩ := (hp.eventually (gt_mem_nhds hε)).exists
    refine ⟨j,fun n => ?_⟩
    have he : (fun p : X × Y => f n p.1*g p.2-u j n p.1*g p.2) =
        (fun p : X × Y => (f n p.1-u j n p.1)*g p.2) := by funext p; ring
    rw [he,eLpNorm_mul_prod_one (f := fun x => f n x-u j n x) ((hfm n).sub (hum j n)) hgm]
    exact (mul_le_mul' (hue j n) le_rfl).trans hj.le
  · exact fun n => (((hfm n).comp measurable_fst).mul (hgm.comp measurable_snd)).aestronglyMeasurable

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

theorem normalizedTensor_L1_le {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hd0 : ∀ x, 0 ≤ d x)
    (hfm : Measurable f) (hgm : Measurable g)
    (hf : ∀ z, 0 ≤ f z) (hg : ∀ z, 0 ≤ g z)
    (hfi : Integrable f (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (hfd : ∀ᵐ x ∂μ, (∫ v, f (x,v) ∂ν) ≤ d x) :
    eLpNorm (normalizedTensor d f g) 1 (μ.prod (ν.prod ν)) ≤ eLpNorm g 1 (μ.prod ν) := by
  have ht := normalizedTensor_integrable hd hd0 hfm hgm hf hg hfi hgi hfd
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm ht,
    eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hgi]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_prod _ ht.norm,integral_prod _ hgi.norm]
  apply integral_mono_ae ht.integral_norm_prod_left hgi.integral_norm_prod_left
  filter_upwards [hfd] with x hx
  have hgn := integral_nonneg (μ := ν) (f := fun v => g (x,v)) (fun v => hg (x,v))
  have hfn := integral_nonneg (μ := ν) (f := fun v => f (x,v)) (fun v => hf (x,v))
  have hn y : 0 ≤ normalizedTensor d f g (x,y) :=
    div_nonneg (mul_nonneg (hf _) (hg _)) (by linarith [hd0 x])
  simp only [Real.norm_of_nonneg (hn _),Real.norm_of_nonneg (hg _)]
  rw [normalizedTensor_fiber_integral]
  apply (div_le_iff₀ (by linarith [hd0 x] : 0 < 1+d x)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hx hgn]

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Products of velocity averages normalized by their mass density -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Compactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem tendstoInMeasure_continuous_comp {f : ℕ → X → ℝ} {g : X → ℝ}
    (hfm : ∀ n, AEStronglyMeasurable (f n) μ)
    (h : TendstoInMeasure μ f atTop g) {P : ℝ → ℝ} (hP : Continuous P) :
    TendstoInMeasure μ (fun n x => P (f n x)) atTop (fun x => P (g x)) := by
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => hP.comp_aestronglyMeasurable (hfm n))).mpr
  intro ns hns
  obtain ⟨i,hi,hfi⟩ := (h.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨i,hi,?_⟩
  filter_upwards [hfi] with x hx
  exact hP.continuousAt.tendsto.comp hx

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

theorem normalizedTensor_norm_swap {d : X → ℝ} {f g : X × Y → ℝ}
    (hd : Measurable d) (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (normalizedTensor d f g) 1 (μ.prod (ν.prod ν)) =
      eLpNorm (normalizedTensor d g f) 1 (μ.prod (ν.prod ν)) := by
  have hp := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := ν))
  calc
    _ = eLpNorm ((normalizedTensor d g f) ∘ (fun z : X × (Y × Y) => (z.1,z.2.2,z.2.1)))
        1 (μ.prod (ν.prod ν)) := by
      congr 1
      funext z
      dsimp only [normalizedTensor,Function.comp_apply]
      rw [mul_comm]
    _ = _ := eLpNorm_comp_measurePreserving
      (normalizedTensor_measurable hd hg hf).aestronglyMeasurable hp

theorem normalizedPair_integrable {f : X × Y → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) (hfi : Integrable f (μ.prod ν)) :
    Integrable (normalizedPair ν f) (μ.prod (ν.prod ν)) :=
  normalizedTensor_integrable (fiberMass_measurable hfm)
    (fun x => integral_nonneg (fun v => hf (x,v))) hfm hfm hf hf hfi hfi
    (ae_of_all _ (fun _ => le_rfl))

theorem normalizedPair_truncation_error {f u : X × Y → ℝ}
    (hfm : Measurable f) (hum : Measurable u)
    (hf : ∀ z, 0 ≤ f z) (hu : ∀ z, 0 ≤ u z) (huf : ∀ z, u z ≤ f z)
    (hfi : Integrable f (μ.prod ν)) (hui : Integrable u (μ.prod ν)) :
    eLpNorm (fun z => normalizedPair ν f z-
      normalizedTensor (fiberMass ν f) u u z) 1 (μ.prod (ν.prod ν)) ≤
      2*eLpNorm (fun z => f z-u z) 1 (μ.prod ν) := by
  have hm := fiberMass_measurable (ν := ν) hfm
  have hn x : 0 ≤ fiberMass ν f x := integral_nonneg (fun v => hf (x,v))
  have hd : ∀ᵐ x ∂μ, (∫ v, f (x,v) ∂ν) ≤ fiberMass ν f x := ae_of_all _ (fun _ => le_rfl)
  have hud : ∀ᵐ x ∂μ, (∫ v, u (x,v) ∂ν) ≤ fiberMass ν f x := by
    filter_upwards [hfi.prod_right_ae,hui.prod_right_ae] with x hfx hux
    exact integral_mono hux hfx (fun v => huf (x,v))
  have hsub z : 0 ≤ f z-u z := sub_nonneg.mpr (huf z)
  have hA := normalizedTensor_L1_le hm hn hfm (hfm.sub hum) hf hsub hfi (hfi.sub hui) hd
  have hB := normalizedTensor_L1_le hm hn hum (hfm.sub hum) hu hsub hui (hfi.sub hui) hud
  have he : (fun z => normalizedPair ν f z-normalizedTensor (fiberMass ν f) u u z) =
      normalizedTensor (fiberMass ν f) f (f-u)+normalizedTensor (fiberMass ν f) (f-u) u := by
    funext z
    dsimp only [normalizedPair,normalizedTensor,Pi.add_apply,Pi.sub_apply]
    ring
  rw [he]
  calc
    _ ≤ eLpNorm (normalizedTensor (fiberMass ν f) f (f-u)) 1 (μ.prod (ν.prod ν))+
        eLpNorm (normalizedTensor (fiberMass ν f) (f-u) u) 1 (μ.prod (ν.prod ν)) :=
      eLpNorm_add_le (hf := (normalizedTensor_measurable hm hfm (hfm.sub hum)).aestronglyMeasurable)
        (hg := (normalizedTensor_measurable hm (hfm.sub hum) hum).aestronglyMeasurable) (by norm_num)
    _ = eLpNorm (normalizedTensor (fiberMass ν f) f (f-u)) 1 (μ.prod (ν.prod ν))+
        eLpNorm (normalizedTensor (fiberMass ν f) u (f-u)) 1 (μ.prod (ν.prod ν)) := by
      rw [normalizedTensor_norm_swap hm (hfm.sub hum) hum]
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add hA hB

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionWeakMarginals
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.normalParameters_sFinite _root_.OAI.BoltzmannNonuniqueness.normalPhaseGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologyPositivePhaseTest _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.KineticTest.timeShift_toFun _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable physical gain and loss and their equal total mass -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_r3c4906_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
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

section

/-! # Weak convergence of the actual full collision rates -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem normalizedKernel_measurable : Measurable (normalizedKernel (X := X)) := by
  unfold normalizedKernel collisionKernel normalComponent
  fun_prop

omit [MeasurableSpace X] in
theorem normalizedKernel_bound (z : (X × (Velocity × Velocity)) × Sphere) :
    |normalizedKernel z| ≤ 1 := by
  unfold normalizedKernel
  have hw : 0 < 1+‖z.1.2.1‖+‖z.1.2.2‖ := by positivity
  rw [abs_of_nonneg (div_nonneg (collisionKernel_nonneg _ _ _) hw.le),div_le_one₀ hw]
  exact (collisionKernel_le_norm _ _ _).trans ((norm_sub_le _ _).trans (by linarith))

omit [MeasurableSpace X] in
theorem preRate_eq_normalized (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    preRate f z = normalizedKernel z*pairDensity f z.1 := by
  have hw : 1+‖z.1.2.1‖+‖z.1.2.2‖ ≠ 0 := ne_of_gt (by positivity)
  unfold preRate normalizedKernel pairDensity
  field_simp

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

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedCollisionRates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The first-velocity-moment weight of the normalized pair is integrable -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem pairVelocityWeight_measurable : Measurable (pairVelocityWeight (X := X)) := by
  unfold pairVelocityWeight
  fun_prop

theorem weightedNormalizedPair_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (weightedNormalizedPair f) :=
  pairVelocityWeight_measurable.mul
    (normalizedTensor_measurable (fiberMass_measurable (ν := volume) hfm) hfm hfm)

theorem normalizedTensor_integrable_swap {d : X → ℝ} {f g : X × Velocity → ℝ}
    (hd : Measurable d) (hf : Measurable f) (hg : Measurable g)
    (hi : Integrable (normalizedTensor d g f) (μ.prod (volume.prod volume))) :
    Integrable (normalizedTensor d f g) (μ.prod (volume.prod volume)) := by
  apply memLp_one_iff_integrable.mp
  refine ⟨(normalizedTensor_measurable hd hf hg).aestronglyMeasurable, ?_⟩
  rw [normalizedTensor_norm_swap hd hf hg]
  exact (memLp_one_iff_integrable.mpr hi).2

theorem weightedNormalizedPair_integrable {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) (μ.prod volume)) :
    Integrable (weightedNormalizedPair f) (μ.prod (volume.prod volume)) := by
  have hfi := integrable_of_entropyGauge hfm hf hi
  have hli := linearMoment_integrable hfm hf hi
  have hdm := fiberMass_measurable (ν := volume) hfm
  have hdn (x : X) : 0 ≤ fiberMass volume f x := integral_nonneg (fun v => hf (x,v))
  have hlm := linearMoment_measurable hfm
  have hln (p : X × Velocity) : 0 ≤ linearMoment f p := mul_nonneg (by positivity) (hf p)
  have hr := normalizedTensor_integrable hdm hdn hfm hlm hf hln hfi hli
    (ae_of_all _ (fun _ => le_rfl))
  have hl := normalizedTensor_integrable_swap hdm hlm hfm hr
  have hp := normalizedPair_integrable hfm hf hfi
  apply ((hl.add hr).sub hp).congr
  filter_upwards [] with z
  dsimp only [Pi.sub_apply,Pi.add_apply,weightedNormalizedPair,pairVelocityWeight,normalizedPair,normalizedTensor,linearMoment]
  ring

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Entropy controls the complete mass-normalized velocity pair -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

private theorem bounded_nonnegative_product_div {a b A B r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ A) (hB : b ≤ B)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hr : 0 ≤ r) :
    |a*b/(1+r)| ≤ A*B := by
  rw [abs_of_nonneg (div_nonneg (mul_nonneg ha hb) (by linarith))]
  apply (div_le_iff₀ (by linarith : 0 < 1+r)).mpr
  exact (mul_le_mul hA hB hb hA0).trans (by nlinarith [mul_nonneg (mul_nonneg hA0 hB0) hr])

theorem normalized_entropyTruncation_uniformIntegrable (R : ℝ)
    {f : ℕ → X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z) :
    UniformIntegrable (fun n => normalizedTensor (fiberMass volume (f n))
      (entropyTruncation R (f n)) (entropyTruncation R (f n))) 1
      (μ.prod (volume.prod volume)) := by
  let a : Velocity → ℝ := (Metric.closedBall (0:Velocity) R).indicator (fun _ => Real.exp R)
  have hai : Integrable a := (integrableOn_const
    (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne).integrable_indicator
    Metric.isClosed_closedBall.measurableSet
  have ha0 v : 0 ≤ a v := indicator_nonneg (fun _ _ => (Real.exp_pos R).le) v
  have hub (n : ℕ) (p : X × Velocity) : entropyTruncation R (f n) p ≤ a p.2 := by
    by_cases hp : p.2 ∈ Metric.closedBall 0 R
    · rw [show a p.2 = Real.exp R from indicator_of_mem hp _]
      exact (entropyTruncation_bounds R (hf n) p).2
    · have hv : R < ‖p.2‖ := by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hp
      rw [entropyTruncation_support R (f n) p hv,show a p.2 = 0 from indicator_of_notMem hp _]
  let b : X × (Velocity × Velocity) → ℝ := fun z => a z.2.1*a z.2.2
  have hbi : Integrable b (μ.prod (volume.prod volume)) := (hai.mul_prod hai).comp_snd μ
  have hbui := uniformIntegrable_const (ι := ℕ) (by norm_num : (1:ℝ≥0∞) ≤ 1)
    (by norm_num) (memLp_one_iff_integrable.mpr hbi)
  have hm n : Measurable (normalizedTensor (fiberMass volume (f n))
      (entropyTruncation R (f n)) (entropyTruncation R (f n))) :=
    normalizedTensor_measurable (fiberMass_measurable (hfm n))
      (entropyTruncation_measurable R (hfm n)) (entropyTruncation_measurable R (hfm n))
  have hdom (n : ℕ) (z : X × (Velocity × Velocity)) :
      ‖normalizedTensor (fiberMass volume (f n))
        (entropyTruncation R (f n)) (entropyTruncation R (f n)) z‖ ≤ b z := by
    change |entropyTruncation R (f n) (z.1,z.2.1)*entropyTruncation R (f n) (z.1,z.2.2)/
      (1+fiberMass volume (f n) z.1)| ≤ a z.2.1*a z.2.2
    exact bounded_nonnegative_product_div (entropyTruncation_bounds R (hf n) _).1
      (entropyTruncation_bounds R (hf n) _).1 (hub n _) (hub n _) (ha0 _) (ha0 _)
      (integral_nonneg (fun v => hf n (z.1,v)))
  have hmono (n : ℕ) (s : Set (X × (Velocity × Velocity))) :
      eLpNorm (normalizedTensor (fiberMass volume (f n))
        (entropyTruncation R (f n)) (entropyTruncation R (f n))) 1
        ((μ.prod (volume.prod volume)).restrict s) ≤ eLpNorm b 1 ((μ.prod (volume.prod volume)).restrict s) :=
    eLpNorm_mono_real (hdom n)
  refine ⟨OAI.UnifIntegrable.of_enn ?_ (fun n => (normalizedTensor_measurable
    (fiberMass_measurable (hfm n)) (entropyTruncation_measurable R (hfm n))
    (entropyTruncation_measurable R (hfm n))).aestronglyMeasurable),?_⟩
  · intro ε hε
    obtain ⟨δ,hδ,hδb⟩ := OAI.UnifIntegrable.enn_spec hbui.1 ε hε
    exact ⟨δ,hδ,fun n s hs => (hmono n s).trans (hδb n s hs)⟩
  · obtain ⟨K,hK⟩ := hbui.2
    refine ⟨K,fun n => ?_⟩
    simpa only [Measure.restrict_univ] using (hmono n univ).trans
      (by simpa only [Measure.restrict_univ] using hK n)

theorem normalizedPair_uniformIntegrable {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ z, entropyGauge (f n) z ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n => normalizedPair volume (f n)) 1 (μ.prod (volume.prod volume)) := by
  let u := fun (j n : ℕ) => entropyTruncation ((j:ℝ)+1) (f n)
  apply uniformIntegrable_of_approximation
    (g := fun j n => normalizedTensor (fiberMass volume (f n)) (u j n) (u j n))
  · exact fun j => normalized_entropyTruncation_uniformIntegrable ((j:ℝ)+1) hfm hf
  · intro ε hε
    obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (2*C) hε
    refine ⟨j,fun n => ?_⟩
    have hR : 1 ≤ (j:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
    have he := normalizedPair_truncation_error (hfm n)
      (entropyTruncation_measurable ((j:ℝ)+1) (hfm n)) (hf n)
      (fun p => (entropyTruncation_bounds ((j:ℝ)+1) (hf n) p).1)
      (fun p => by
        unfold entropyTruncation
        split_ifs
        · exact le_rfl
        · exact hf n p)
      (integrable_of_entropyGauge (hfm n) (hf n) (hi n))
      (entropyTruncation_integrable ((j:ℝ)+1) (hfm n) (hf n))
    calc
      _ ≤ 2*eLpNorm (fun z => f n z-u j n z) 1 (μ.prod volume) := he
      _ ≤ 2*ENNReal.ofReal (C/((j:ℝ)+1)) := mul_le_mul' le_rfl
        (entropyTruncation_L1_bound hR (hfm n) (hf n) (hi n) (hb n))
      _ = ENNReal.ofReal ((2*C)/((j:ℝ)+1)) := by
        rw [show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      _ ≤ ε := hj
  · exact fun n => (normalizedTensor_measurable (fiberMass_measurable (hfm n)) (hfm n) (hfm n)).aestronglyMeasurable

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Uniform velocity-tail control of the moment-weighted normalized pair -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem pairVelocityCut_measurable (R : ℝ) {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (pairVelocityCut R f) :=
  (weightedNormalizedPair_measurable hfm).ite
    ((measurableSet_le (measurable_snd.fst.norm) measurable_const).inter
      (measurableSet_le (measurable_snd.snd.norm) measurable_const)) measurable_const

private theorem tail_coeff_bound {R a b : ℝ} (hR : 0 ≤ R) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    (if a ≤ R ∧ b ≤ R then 0 else 1+a+b) ≤
      2*((if a ≤ R then 0 else 1+a)+(if b ≤ R then 0 else 1+b)) := by
  by_cases har : a ≤ R <;> by_cases hbr : b ≤ R <;>
    simp only [har,hbr,and_self,ite_true, if_true,ite_false, if_false,false_and,and_false,
      zero_add,add_zero] <;> (try linarith)

omit [MeasurableSpace X] in
private theorem tail_density_nonneg (R : ℝ) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ linearMoment f p-velocityLinearCut R f p := by
  dsimp only [velocityLinearCut]
  split_ifs
  · simp only [sub_self,le_refl]
  · simp only [sub_zero,linearMoment]
    exact mul_nonneg (by positivity) (hf p)

omit [MeasurableSpace X] in
theorem pairVelocityCut_pointwise_error {R : ℝ} (hR : 0 ≤ R) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : X × (Velocity × Velocity)) :
    |weightedNormalizedPair f z-pairVelocityCut R f z| ≤
      2*(normalizedTensor (fiberMass volume f)
          (fun p => linearMoment f p-velocityLinearCut R f p) f z+
        normalizedTensor (fiberMass volume f) f
          (fun p => linearMoment f p-velocityLinearCut R f p) z) := by
  have hd : 0 < 1+fiberMass volume f z.1 := by
    have hm : 0 ≤ fiberMass volume f z.1 := integral_nonneg (fun v => hf (z.1,v))
    linarith
  have hprod : 0 ≤ f (z.1,z.2.1)*f (z.1,z.2.2) := mul_nonneg (hf _) (hf _)
  have hc := mul_le_mul_of_nonneg_right (tail_coeff_bound hR (norm_nonneg z.2.1) (norm_nonneg z.2.2)) hprod
  have hdiv := div_le_div_of_nonneg_right hc hd.le
  by_cases hv : ‖z.2.1‖ ≤ R <;> by_cases hw : ‖z.2.2‖ ≤ R
  all_goals
    simp only [weightedNormalizedPair,pairVelocityCut,pairVelocityWeight,normalizedPair,
      normalizedTensor,linearMoment,velocityLinearCut,hv,hw,and_self,
      ite_true, if_true,ite_false, if_false,false_and,and_false,sub_self,sub_zero,zero_mul,mul_zero,zero_div,
      zero_add,add_zero,abs_zero] at hdiv ⊢
  · exact le_refl _
  all_goals
    rw [abs_of_nonneg (mul_nonneg (by positivity) (div_nonneg hprod hd.le))]
    first | (convert hdiv using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hdiv.trans (le_of_eq (by ring)))

theorem pairVelocityCut_L1_error {R C : ℝ} (hR : 0 < R) {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) (μ.prod volume))
    (hb : (∫ p, entropyGauge f p ∂μ.prod volume) ≤ C) :
    eLpNorm (fun z => weightedNormalizedPair f z-pairVelocityCut R f z) 1
      (μ.prod (volume.prod volume)) ≤ ENNReal.ofReal (8*C/R) := by
  let d : X × Velocity → ℝ := fun p => linearMoment f p-velocityLinearCut R f p
  have hdm : Measurable d := (linearMoment_measurable hfm).sub (velocityLinearCut_measurable R hfm)
  have hdi : Integrable d (μ.prod volume) :=
    (linearMoment_integrable hfm hf hi).sub (velocityLinearCut_integrable R hfm hf hi)
  have hfi := integrable_of_entropyGauge hfm hf hi
  have hm := fiberMass_measurable (ν := volume) hfm
  have hmn (x : X) : 0 ≤ fiberMass volume f x := integral_nonneg (fun v => hf (x,v))
  have hd0 : ∀ p, 0 ≤ d p := tail_density_nonneg R hf
  have hright := normalizedTensor_L1_le hm hmn hfm hdm hf hd0 hfi hdi (ae_of_all _ (fun _ => le_rfl))
  have hleft : eLpNorm (normalizedTensor (fiberMass volume f) d f) 1 (μ.prod (volume.prod volume)) ≤
      eLpNorm d 1 (μ.prod volume) := by
    rw [normalizedTensor_norm_swap hm hdm hfm]
    exact hright
  have hs_nonneg (z : X × (Velocity × Velocity)) :
      0 ≤ normalizedTensor (fiberMass volume f) d f z+normalizedTensor (fiberMass volume f) f d z := by
    have hden : 0 ≤ 1+fiberMass volume f z.1 := by linarith [hmn z.1]
    exact add_nonneg (div_nonneg (mul_nonneg (hd0 _) (hf _)) hden)
      (div_nonneg (mul_nonneg (hf _) (hd0 _)) hden)
  have hnorm := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := μ.prod (volume.prod volume))
    (f := weightedNormalizedPair f-pairVelocityCut R f)
    (g := fun z => normalizedTensor (fiberMass volume f) d f z+normalizedTensor (fiberMass volume f) f d z)
    (c := 2) (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,Real.norm_of_nonneg (hs_nonneg z)]
      exact pairVelocityCut_pointwise_error hR.le hf z)) 1
  calc
    _ ≤ 2*(eLpNorm (normalizedTensor (fiberMass volume f) d f) 1 (μ.prod (volume.prod volume))+
        eLpNorm (normalizedTensor (fiberMass volume f) f d) 1 (μ.prod (volume.prod volume))) := by
      exact hnorm.trans (by norm_num; exact mul_le_mul' le_rfl (eLpNorm_add_le (hf := (normalizedTensor_measurable hm hdm hfm).aestronglyMeasurable)
        (hg := (normalizedTensor_measurable hm hfm hdm).aestronglyMeasurable) (by norm_num)))
    _ ≤ 2*(eLpNorm d 1 (μ.prod volume)+eLpNorm d 1 (μ.prod volume)) :=
      mul_le_mul' le_rfl (add_le_add hleft hright)
    _ ≤ 2*(ENNReal.ofReal (2*C/R)+ENNReal.ofReal (2*C/R)) :=
      mul_le_mul' le_rfl (add_le_add (velocityLinearCut_L1_error hR hfm hf hi hb)
        (velocityLinearCut_L1_error hR hfm hf hi hb))
    _ = ENNReal.ofReal (8*C/R) := by
      have hC : 0 ≤ C := (integral_nonneg (entropyGauge_nonneg hf)).trans hb
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        show (2:ℝ≥0∞) = ENNReal.ofReal (2:ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      ring

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Actual pre- and post-collision rates normalized by the spatial mass -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

omit [MeasurableSpace X] in
theorem massNormalizedPreRate_eq (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    massNormalizedPreRate f z = normalizedKernel z*weightedNormalizedPair f z.1 := by
  rw [massNormalizedPreRate,preRate_eq_normalized]
  dsimp only [pairDensity,weightedNormalizedPair,pairVelocityWeight,normalizedPair,normalizedTensor]
  ring

omit [MeasurableSpace X] in
theorem massNormalizedPreRate_eq_fun (f : X × Velocity → ℝ) :
    massNormalizedPreRate f = fun z => normalizedKernel z*weightedNormalizedPair f z.1 :=
  funext (massNormalizedPreRate_eq f)

theorem massNormalizedPreRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (massNormalizedPreRate f) := by
  rw [massNormalizedPreRate_eq_fun]
  exact normalizedKernel_measurable.mul ((weightedNormalizedPair_measurable hfm).comp measurable_fst)

theorem massNormalizedPostRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (massNormalizedPostRate f) :=
  (massNormalizedPreRate_measurable hfm).comp scatterTriple_measurable

omit [SFinite μ] in
theorem massNormalizedPreRate_integrable {f : X × Velocity → ℝ} (_hfm : Measurable f)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (massNormalizedPreRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have h := (hi.comp_fst sphereArea).bdd_mul normalizedKernel_measurable.aestronglyMeasurable
    (ae_of_all _ normalizedKernel_bound)
  simpa only [massNormalizedPreRate_eq_fun] using h

theorem massNormalizedPostRate_integrable {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (massNormalizedPostRate f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (scatterTriple_measurePreserving μ).integrable_comp_of_integrable (massNormalizedPreRate_integrable hfm hi)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WeightedPairUniformIntegrability
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Entropy gives uniform integrability of moment-weighted normalized pairs -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
open PeriodicApproximation
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem weightedNormalizedPair_uniformIntegrable
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n => weightedNormalizedPair (f n)) 1
      (μ.prod (volume.prod volume)) := by
  have hui := normalizedPair_uniformIntegrable hfm hf hi hb
  have hcut (j : ℕ) : UniformIntegrable (fun n => pairVelocityCut ((j:ℝ)+1) (f n)) 1
      (μ.prod (volume.prod volume)) := by
    let R : ℝ := (j:ℝ)+1
    let a : X × (Velocity × Velocity) → ℝ := fun z =>
      if ‖z.2.1‖ ≤ R ∧ ‖z.2.2‖ ≤ R then pairVelocityWeight z else 0
    have ham : Measurable a := pairVelocityWeight_measurable.ite
      ((measurableSet_le (measurable_snd.fst.norm) measurable_const).inter
        (measurableSet_le (measurable_snd.snd.norm) measurable_const)) measurable_const
    have hR : 0 ≤ R := by dsimp [R] <;> positivity
    have ha (z) : |a z| ≤ 1+2*R := by
      dsimp only [a]
      split_ifs with hz
      · rw [abs_of_nonneg (show 0 ≤ pairVelocityWeight z by dsimp [pairVelocityWeight] <;> positivity)]
        dsimp only [pairVelocityWeight]
        linarith [hz.1,hz.2]
      · simp only [abs_zero]
        positivity
    have h := uniformIntegrable_of_bounded_multiplier hui ham
      ⟨1+2*R,by positivity⟩ ha
    have he : (fun n z => a z*normalizedPair volume (f n) z) =
        (fun n => pairVelocityCut ((j:ℝ)+1) (f n)) := by
      funext n z
      dsimp only [a,pairVelocityCut,weightedNormalizedPair,R]
      split_ifs <;> simp only [zero_mul]
    rwa [he] at h
  apply uniformIntegrable_of_approximation hcut
  intro ε hε
  obtain ⟨j,hj⟩ := exists_entropyTruncation_radius (8*C) hε
  exact ⟨j,fun n => (pairVelocityCut_L1_error (by positivity : 0 < (j:ℝ)+1)
    (hfm n) (hf n) (hi n) (hb n)).trans hj⟩
  exact fun n => (weightedNormalizedPair_measurable (hfm n)).aestronglyMeasurable

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_SmoothedPrePostIdentity
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.incomingBallFinite _root_.OAI.BoltzmannNonuniqueness.CollisionCompactness.DoubleGain.parameterMeasureFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.Compactness.instSecondCountableTopologySupportedTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The outgoing smoothing kernel is the actual incoming physical collision rate -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*}

theorem massNormalizedPreRate_eq_pair (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    massNormalizedPreRate f z = collisionKernel z.1.2.1 z.1.2.2 z.2*
      normalizedPair volume f z.1 := by
  unfold massNormalizedPreRate preRate normalizedPair normalizedTensor
  ring

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedPairCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Local uniform integrability of the mass-normalized physical collision rates -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem velocityPairBox_measurable (R : ℝ) : MeasurableSet (velocityPairBox (X := X) R) :=
  MeasurableSet.univ.prod
    (Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet)

theorem angularPairBox_measurable (R : ℝ) : MeasurableSet (angularPairBox (X := X) R) :=
  (velocityPairBox_measurable R).prod MeasurableSet.univ

variable {μ : Measure X} [IsFiniteMeasure μ]

theorem velocityPairBox_finite (R : ℝ) :
    (μ.prod (volume : Measure (Velocity × Velocity))) (velocityPairBox R) < ⊤ := by
  rw [Measure.volume_eq_prod]
  dsimp only [velocityPairBox]
  rw [Measure.prod_prod,Measure.prod_prod]
  have hb : volume (Metric.closedBall (0:Velocity) R) ≠ ⊤ :=
    (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (measure_ne_top μ univ) (ENNReal.mul_ne_top hb hb))

theorem weightedPair_angular_local_uniformIntegrable (R : ℝ)
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n z => weightedNormalizedPair (f n) z.1) 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (angularPairBox R)) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).restrict (velocityPairBox R)
  have : IsFiniteMeasure ν := ⟨by
    dsimp [ν]
    rw [Measure.restrict_apply_univ]
    exact velocityPairBox_finite R⟩
  have hui := weightedNormalizedPair_uniformIntegrable hfm hf hi hb
  rw [← Measure.volume_eq_prod] at hui
  have hr : UniformIntegrable (fun n => weightedNormalizedPair (f n)) 1 ν :=
    uniformIntegrable_restrict hui (velocityPairBox R)
  have hp := uniformIntegrable_tensor (μ := ν) (ν := sphereArea) (fun n => weightedNormalizedPair_measurable (hfm n)) hr
    (g := fun _ : Sphere => (1:ℝ)) measurable_const (integrable_const 1)
  dsimp only [ν] at hp
  rw [Measure.restrict_prod_eq_prod_univ] at hp
  simpa only [Measure.restrict_univ,mul_one,angularPairBox] using hp

theorem massNormalizedPreRate_local_uniformIntegrable (R : ℝ)
    {f : ℕ → X × Velocity → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C) :
    UniformIntegrable (fun n => massNormalizedPreRate (f n)) 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (angularPairBox R)) := by
  have h := uniformIntegrable_of_bounded_multiplier
    (weightedPair_angular_local_uniformIntegrable R hfm hf hi hb)
    normalizedKernel_measurable 1 normalizedKernel_bound
  simpa only [massNormalizedPreRate_eq_fun] using h

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Collision_CollisionSources
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # L1 contraction for marginalizing a collision rate -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_11 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

theorem collisionMarginal_sub_ae {h k : (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hi : Integrable h ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (ki : Integrable k ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    collisionMarginal (h-k) =ᵐ[μ.prod volume] collisionMarginal h-collisionMarginal k := by
  have hhi := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable hi
  have hki := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable ki
  filter_upwards [hhi.prod_right_ae,hki.prod_right_ae] with p hp kp
  exact integral_sub hp kp

theorem collisionMarginal_eLpNorm_le {h : (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hm : Measurable h) :
    eLpNorm (collisionMarginal h) 1 (μ.prod volume) ≤
      eLpNorm h 1 ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have ht := Compactness.eLpNorm_integral_le (μ := μ.prod volume)
    (ν := (volume : Measure Velocity).prod sphereArea) (hm.comp collisionGrouping.symm.measurable)
  apply ht.trans_eq
  exact eLpNorm_comp_measurePreserving hm.aestronglyMeasurable (collisionGrouping_measurePreserving μ).symm

theorem collisionMarginal_difference_le {h k : (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hm : Measurable h) (km : Measurable k)
    (hi : Integrable h ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (ki : Integrable k ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    eLpNorm (collisionMarginal h-collisionMarginal k) 1 (μ.prod volume) ≤
      eLpNorm (h-k) 1 ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  rw [← eLpNorm_congr_ae (collisionMarginal_sub_ae hi ki)]
  exact collisionMarginal_eLpNorm_le (hm.sub km)

end BoltzmannNonuniqueness.CollisionCompactness

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_StrongMassClip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded mass coefficients preserve strong L1 convergence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem strongL1_comp_fst {Y : Type*} [MeasurableSpace Y]
    [SFinite μ] {ν : Measure Y} [IsFiniteMeasure ν] {f : ℕ → X → ℝ}
    (hfm : ∀ n, Measurable (f n))
    (h : Tendsto (fun n => eLpNorm (f n) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun p : X × Y => f n p.1) 1 (μ.prod ν)) atTop (𝓝 0) := by
  have ht := ENNReal.Tendsto.mul_const h
    (Or.inr (memLp_one_iff_integrable.mpr (integrable_const (1:ℝ) : Integrable _ ν)).eLpNorm_ne_top)
  simp only [zero_mul] at ht
  simpa only [← eLpNorm_mul_prod_one (hfm _) measurable_const,mul_one] using ht

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

/-! # Measurability and pointwise stability of the common collision multiplier -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem rateMultiplier_measurable (N : ℝ) {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (rateMultiplier N f) := by
  unfold rateMultiplier attenuation rateSum scatterLeft scatterRight normalComponent
  fun_prop

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_AttenuationGap
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Quantitative removal of the symmetric collision attenuation -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem one_sub_attenuation_le {N S : ℝ} (hN : 0 < N) (hS : 0 ≤ S) :
    1-attenuation N S ≤ 2*S/N := by
  have hd : 0 < N+S := add_pos_of_pos_of_nonneg hN hS
  have he : 1-attenuation N S = (2*N*S+S^2)/(N+S)^2 := by
    unfold attenuation
    field_simp [ne_of_gt hd]
    ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos hd) hN).mpr
  nlinarith [mul_nonneg hS (sq_nonneg S),mul_nonneg hN.le (sq_nonneg S)]

theorem abs_one_sub_attenuation_le {N S : ℝ} (hN : 0 < N) (hS : 0 ≤ S) :
    |1-attenuation N S| ≤ 2*S/N := by
  rw [abs_of_nonneg (sub_nonneg.mpr (attenuation_le_one hN hS))]
  exact one_sub_attenuation_le hN hS

variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem rateMultiplier_gap_le {N : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    |1-rateMultiplier N f z| ≤ 2/N*
      (f (z.1.1,z.1.2.1)+f (z.1.1,z.1.2.2)+
        f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)+
        f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)) := by
  have h := abs_one_sub_attenuation_le hN
    (rateSum_nonneg (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
      (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
      (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)))
  unfold rateMultiplier
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold rateSum
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

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

end BoltzmannNonuniqueness.PeriodicApproximation

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

/-! # An L1 density bound on a fixed elastic collision window -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem windowPartner_measurable (R : ℝ) : Measurable (windowPartner R) :=
  (measurable_const.indicator Metric.isClosed_closedBall.measurableSet).comp measurable_fst

theorem windowPartner_integrable (R : ℝ) :
    Integrable (windowPartner R) ((volume : Measure Velocity).prod sphereArea) := by
  have hi : Integrable ((Metric.closedBall (0:Velocity) R).indicator (fun _ => (1:ℝ))) :=
    (integrableOn_const (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  exact hi.comp_fst sphereArea

theorem singleDensity_window_norm_le {R : ℝ} (hR : 0 ≤ R)
    {f : X × Velocity → ℝ} (hfm : Measurable f) :
    eLpNorm ((collisionWindow R).indicator (fun z => f (z.1.1,z.1.2.1))) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
    eLpNorm f 1 (μ.prod volume)*eLpNorm (windowPartner R) 1
      ((volume : Measure Velocity).prod sphereArea) := by
  let b : ((X × (Velocity × Velocity)) × Sphere) → ℝ := fun z =>
    f (z.1.1,z.1.2.1)*windowPartner R (z.1.2.2,z.2)
  have he : eLpNorm b 1 ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      eLpNorm f 1 (μ.prod volume)*eLpNorm (windowPartner R) 1
        ((volume : Measure Velocity).prod sphereArea) := by
    have hm : AEStronglyMeasurable
        (fun z : (X × Velocity) × (Velocity × Sphere) => f z.1*windowPartner R z.2)
        ((μ.prod volume).prod ((volume : Measure Velocity).prod sphereArea)) :=
      ((hfm.comp measurable_fst).mul ((windowPartner_measurable R).comp measurable_snd)).aestronglyMeasurable
    change eLpNorm ((fun z : (X × Velocity) × (Velocity × Sphere) => f z.1*windowPartner R z.2)
      ∘ collisionGrouping) 1 _ = _
    rw [eLpNorm_comp_measurePreserving hm (collisionGrouping_measurePreserving μ)]
    exact eLpNorm_mul_prod_one hfm (windowPartner_measurable R)
  rw [← he]
  apply eLpNorm_mono
  intro z
  by_cases hz : z ∈ collisionWindow R
  · have hw : z.1.2.2 ∈ Metric.closedBall (0:Velocity) R := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using (collisionWindow_bounds hR hz).2
    simp only [indicator_of_mem hz,b,windowPartner,indicator_of_mem hw,mul_one,Function.comp_apply]
    exact le_rfl
  · simp only [indicator_of_notMem hz,norm_zero]
    exact norm_nonneg _

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The same finite collision window contains all four collision legs -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem mem_collisionWindow_scatter (R : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    scatterTriple z ∈ collisionWindow R ↔ z ∈ collisionWindow R := by
  change (‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2+
    ‖scatterRight z.1.2.1 z.1.2.2 z.2‖^2 ≤ R^2) ↔ _
  rw [scatter_energy _ _ _ (mem_sphere_zero_iff_norm.mp z.2.property)]
  rfl

theorem mem_collisionWindow_particleSwap (R : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) :
    particleSwap z ∈ collisionWindow R ↔ z ∈ collisionWindow R := by
  change (‖z.1.2.2‖^2+‖z.1.2.1‖^2 ≤ R^2) ↔ _
  rw [add_comm]
  rfl

theorem windowSingleDensity_measurable (R : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (windowSingleDensity R f) := by
  apply Measurable.indicator _ (collisionWindow_measurable R)
  exact hfm.comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)

theorem windowDensitySum_eq (R : ℝ) (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    windowDensitySum R f z = (collisionWindow R).indicator (fun z =>
      rateSum (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2))
        (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
        (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))) z := by
  have hs := mem_collisionWindow_scatter R z
  have hp := mem_collisionWindow_particleSwap R z
  have hps := mem_collisionWindow_particleSwap R (scatterTriple z)
  by_cases hz : z ∈ collisionWindow R
  · have hs' := hs.mpr hz
    have hp' := hp.mpr hz
    have hps' := hps.mpr hs'
    simp only [windowDensitySum,windowSingleDensity,indicator_of_mem hz,
      indicator_of_mem hs',indicator_of_mem hp',indicator_of_mem hps']
    rfl
  · have hs' : scatterTriple z ∉ collisionWindow R := fun h => hz (hs.mp h)
    have hp' : particleSwap z ∉ collisionWindow R := fun h => hz (hp.mp h)
    have hps' : particleSwap (scatterTriple z) ∉ collisionWindow R := fun h => hs' (hps.mp h)
    simp only [windowDensitySum,windowSingleDensity,indicator_of_notMem hz,
      indicator_of_notMem hs',indicator_of_notMem hp',indicator_of_notMem hps',add_zero]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The four collision legs have one common local L1 bound -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
private theorem four_add_norm_le {Y : Type*} [MeasurableSpace Y] (ν : Measure Y)
    (a b c d : Y → ℝ) (ha : AEStronglyMeasurable a ν) (hb : AEStronglyMeasurable b ν)
    (hc : AEStronglyMeasurable c ν) (hd : AEStronglyMeasurable d ν) :
    eLpNorm (((a+b)+c)+d) 1 ν ≤
      ((eLpNorm a 1 ν+eLpNorm b 1 ν)+eLpNorm c 1 ν)+eLpNorm d 1 ν := by
  have h1 : eLpNorm (a+b) 1 ν ≤ eLpNorm a 1 ν+eLpNorm b 1 ν :=
    eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)
  have h2 : eLpNorm ((a+b)+c) 1 ν ≤ eLpNorm (a+b) 1 ν+eLpNorm c 1 ν :=
    eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)
  have h3 : eLpNorm (((a+b)+c)+d) 1 ν ≤ eLpNorm ((a+b)+c) 1 ν+eLpNorm d 1 ν :=
    eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)
  have h2' : eLpNorm ((a+b)+c) 1 ν ≤ (eLpNorm a 1 ν+eLpNorm b 1 ν)+eLpNorm c 1 ν :=
    h2.trans (add_le_add h1 le_rfl)
  exact h3.trans (add_le_add h2' le_rfl)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem windowDensitySum_norm_le {R : ℝ} (hR : 0 ≤ R)
    {f : X × Velocity → ℝ} (hfm : Measurable f) :
    eLpNorm (windowDensitySum R f) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
    4*(eLpNorm f 1 (μ.prod volume)*eLpNorm (windowPartner R) 1
      ((volume : Measure Velocity).prod sphereArea)) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let g := windowSingleDensity R f
  have hgm : Measurable g := windowSingleDensity_measurable R hfm
  have hgs : eLpNorm (g ∘ scatterTriple) 1 ν = eLpNorm g 1 ν :=
    eLpNorm_comp_measurePreserving hgm.aestronglyMeasurable (scatterTriple_measurePreserving μ)
  have hgp : eLpNorm (g ∘ particleSwap) 1 ν = eLpNorm g 1 ν :=
    eLpNorm_comp_measurePreserving hgm.aestronglyMeasurable (particleSwap_measurePreserving μ)
  have hgps : eLpNorm ((g ∘ particleSwap) ∘ scatterTriple) 1 ν = eLpNorm g 1 ν := by
    rw [eLpNorm_comp_measurePreserving (hgm.comp particleSwap.measurable).aestronglyMeasurable
      (scatterTriple_measurePreserving μ),hgp]
  have he : windowDensitySum R f = ((g+(g ∘ particleSwap))+(g ∘ scatterTriple))+
      ((g ∘ particleSwap) ∘ scatterTriple) := rfl
  change eLpNorm (windowDensitySum R f) 1 ν ≤ _
  rw [he]
  calc
    _ ≤ ((eLpNorm g 1 ν+eLpNorm (g ∘ particleSwap) 1 ν)+
        eLpNorm (g ∘ scatterTriple) 1 ν)+eLpNorm ((g ∘ particleSwap) ∘ scatterTriple) 1 ν :=
      four_add_norm_le ν g (g ∘ particleSwap) (g ∘ scatterTriple) ((g ∘ particleSwap) ∘ scatterTriple)
        hgm.aestronglyMeasurable (hgm.comp particleSwap.measurable).aestronglyMeasurable
        (hgm.comp scatterTriple_measurable).aestronglyMeasurable
        ((hgm.comp particleSwap.measurable).comp scatterTriple_measurable).aestronglyMeasurable
    _ = 4*eLpNorm g 1 ν := by rw [hgp,hgs,hgps]; ring
    _ ≤ _ := mul_le_mul' le_rfl (singleDensity_window_norm_le hR hfm)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual attenuation tends to one on every finite collision window -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem collisionAttenuation_window_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} (R : ℝ) (hR : 0 ≤ R)
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm ((collisionWindow R).indicator
      (fun z => 1-rateMultiplier (N n) (f n) z)) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) atTop (𝓝 0) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let P := eLpNorm (windowPartner R) 1 ((volume : Measure Velocity).prod sphereArea)
  have hP : P ≠ ⊤ := (memLp_one_iff_integrable.mpr (windowPartner_integrable R)).eLpNorm_ne_top
  have hb n : eLpNorm ((collisionWindow R).indicator
      (fun z => 1-rateMultiplier (N n) (f n) z)) 1 ν ≤
      ENNReal.ofReal (2/N n)*(4*((B:ℝ≥0∞)*P)) := by
    have hm : AEStronglyMeasurable ((collisionWindow R).indicator
        (fun z => 1-rateMultiplier (N n) (f n) z)) ν :=
      (measurable_const.sub (rateMultiplier_measurable (N n) (hfm n))).indicator
        (collisionWindow_measurable R) |>.aestronglyMeasurable
    have he (z : (X × (Velocity × Velocity)) × Sphere) :
        |(collisionWindow R).indicator (fun z => 1-rateMultiplier (N n) (f n) z) z| ≤
        (2/N n)*|windowDensitySum R (f n) z| := by
      rw [windowDensitySum_eq]
      by_cases hz : z ∈ collisionWindow R
      · rw [indicator_of_mem hz,indicator_of_mem hz,
          abs_of_nonneg (rateSum_nonneg (hf n _) (hf n _) (hf n _) (hf n _))]
        exact rateMultiplier_gap_le (hN n) (hf n) z
      · simp only [indicator_of_notMem hz,abs_zero,mul_zero,le_refl]
    have he' := eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (f := (collisionWindow R).indicator (fun z => 1-rateMultiplier (N n) (f n) z))
      (g := windowDensitySum R (f n)) (c := 2/N n)
      (ae_of_all ν (fun z => by simpa only [Real.norm_eq_abs] using he z)) 1
    exact he'.trans (mul_le_mul' le_rfl ((windowDensitySum_norm_le hR (hfm n)).trans
      (mul_le_mul' le_rfl (mul_le_mul' (hB n) le_rfl))))
  have hs : Tendsto (fun n => ENNReal.ofReal (2/N n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal
      (tendsto_const_nhds.div_atTop hNt : Tendsto (fun n => (2:ℝ)/N n) atTop (𝓝 0))
  have ht := ENNReal.Tendsto.mul_const hs
    (Or.inr (show 4*((B:ℝ≥0∞)*P) ≠ ⊤ from by finiteness))
  simp only [zero_mul] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) hb

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing attenuation from actual mass-normalized pre-collision rates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem collisionAttenuation_preRate_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (R : ℝ) (hR : 0 ≤ R)
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm (fun z =>
      (collisionWindow R).indicator (fun z => 1-rateMultiplier (N n) (f n) z) z *
        massNormalizedPreRate (f n) z) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) atTop (𝓝 0) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let S := angularPairBox (X := X) R
  let a (n : ℕ) : ((X × (Velocity × Velocity)) × Sphere) → ℝ :=
    (collisionWindow R).indicator (fun z => 1-rateMultiplier (N n) (f n) z)
  have ham n : Measurable (a n) :=
    (measurable_const.sub (rateMultiplier_measurable (N n) (hfm n))).indicator
      (collisionWindow_measurable R)
  have has : collisionWindow (X := X) R ⊆ S := by
    intro z hz
    have hv := collisionWindow_bounds hR hz
    exact ⟨⟨mem_univ _,by simpa only [Metric.mem_closedBall,dist_zero_right] using hv.1,
      by simpa only [Metric.mem_closedBall,dist_zero_right] using hv.2⟩,mem_univ _⟩
  have ha n z : |a n z| ≤ (1:ℝ≥0) := by
    by_cases hz : z ∈ collisionWindow R
    · change |(collisionWindow R).indicator _ z| ≤ 1
      rw [indicator_of_mem hz,abs_of_nonneg (sub_nonneg.mpr (rateMultiplier_bounds (hN n) (hf n) z).2)]
      linarith [(rateMultiplier_bounds (hN n) (hf n) z).1]
    · simp only [a,indicator_of_notMem hz,abs_zero,NNReal.coe_one,zero_le_one]
  have hzero : Tendsto (fun n => eLpNorm (a n) 1 (ν.restrict S)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (collisionAttenuation_window_L1 R hR hfm hf hN hNt B hB)
      (fun _ => zero_le) (fun n => eLpNorm_mono_measure (a n) Measure.restrict_le_self)
  have ht := tendsto_L1_mul_uniformIntegrable
    (massNormalizedPreRate_local_uniformIntegrable R hfm hf hi hb)
    (fun n => massNormalizedPreRate_measurable (hfm n)) ham hzero 1 ha
  have he n : S.indicator (fun z => a n z*massNormalizedPreRate (f n) z) =
      (fun z => a n z*massNormalizedPreRate (f n) z) := by
    funext z
    by_cases hz : z ∈ S
    · exact indicator_of_mem hz _
    · have hw : z ∉ collisionWindow R := fun hw => hz (has hw)
      simp only [indicator_of_notMem hz,a,indicator_of_notMem hw,zero_mul]
  have hmS : MeasurableSet S := angularPairBox_measurable R
  have hn n : eLpNorm (fun z => a n z*massNormalizedPreRate (f n) z) 1 (ν.restrict S) =
      eLpNorm (fun z => a n z*massNormalizedPreRate (f n) z) 1 ν := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hmS,he n]
  change Tendsto (fun n => eLpNorm (fun z => a n z*massNormalizedPreRate (f n) z) 1
    (ν.restrict S)) atTop (𝓝 0) at ht
  simp only [hn] at ht
  exact ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_NormalizedGainCompactness
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The linear normalized-pair gain is the physical gain divided by spatial mass -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness.DoubleGain
open Compactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem normalizedPair_postRate (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    pairPostRate (normalizedPair volume f) z = massNormalizedPostRate f z := by
  change pairPreRate (normalizedPair volume f) (scatterTriple z) =
    massNormalizedPreRate f (scatterTriple z)
  exact (massNormalizedPreRate_eq_pair f (scatterTriple z)).symm

theorem normalizedPair_gain (f : X × Velocity → ℝ) (p : X × Velocity) :
    pairGain (normalizedPair volume f) p = gainDensity f p/(1+fiberMass volume f p.1) := by
  unfold pairGain
  simp_rw [normalizedPair_postRate]
  change (∫ q : Velocity × Sphere,
    postRate f (collisionGrouping.symm (p,q))/(1+fiberMass volume f p.1)
      ∂(volume : Measure Velocity).prod sphereArea) = _
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  rfl

end BoltzmannNonuniqueness.CollisionCompactness.DoubleGain

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MassNormalizedCollisionLimits
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong spatial masses remove gain normalization in measure -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem tendstoInMeasure_of_strong_massNormalized
    {f r : ℕ → X → ℝ} {g s : X → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hrm : ∀ n, Measurable (r n))
    (hr0 : ∀ n x, 0 ≤ r n x) (hs0 : ∀ x, 0 ≤ s x)
    (hr : Tendsto (fun n => eLpNorm (fun x => r n x-s x) 1 μ) atTop (𝓝 0))
    (hf : Tendsto (fun n => eLpNorm (fun x =>
      f n x/(1+r n x)-g x/(1+s x)) 1 μ) atTop (𝓝 0))
    (hsm : Measurable s) (hgm : Measurable g) :
    TendstoInMeasure μ f atTop g := by
  have hri := tendstoInMeasure_of_tendsto_eLpNorm
    (hf := fun n => by exact (hrm n).aestronglyMeasurable) (hg := by exact hsm.aestronglyMeasurable) (by norm_num : (1:ℝ≥0∞) ≠ 0) hr
  have hfi := tendstoInMeasure_of_tendsto_eLpNorm
    (hf := fun n => by exact ((hfm n).div (measurable_const.add (hrm n))).aestronglyMeasurable)
    (hg := by exact (hgm.div (measurable_const.add hsm)).aestronglyMeasurable) (by norm_num : (1:ℝ≥0∞) ≠ 0) hf
  have hrc := tendstoInMeasure_continuous_comp (fun n => (hrm n).aestronglyMeasurable) hri
    (P := fun x : ℝ => 1+x) (continuous_const.add continuous_id)
  have h := tendstoInMeasure_mul
    (fun n => ((hfm n).div (measurable_const.add (hrm n))).aestronglyMeasurable)
    (fun n => (measurable_const.add (hrm n)).aestronglyMeasurable) hfi hrc
  have he n x : f n x/(1+r n x)*(1+r n x) = f n x :=
    div_mul_cancel₀ _ (by linarith [hr0 n x])
  have heg x : g x/(1+s x)*(1+s x) = g x := div_mul_cancel₀ _ (by linarith [hs0 x])
  change TendstoInMeasure μ (fun n x => f n x/(1+r n x)*(1+r n x)) atTop
    (fun x => g x/(1+s x)*(1+s x)) at h
  simpa only [he,heg] using h

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # The actual finite collision rates divided by the same spatial mass -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X]

theorem massRegularizedPreRate_measurable (N : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (massRegularizedPreRate N f) := by
  exact (regularizedPreRate_measurable N hfm).div
    (measurable_const.add ((fiberMass_measurable hfm).comp measurable_fst.fst))

theorem massRegularizedPostRate_measurable (N : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (massRegularizedPostRate N f) :=
  (massRegularizedPreRate_measurable N hfm).comp scatterTriple_measurable

omit [MeasurableSpace X] in
theorem massRegularizedPreRate_bounds {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ massRegularizedPreRate N f z ∧ massRegularizedPreRate N f z ≤ massNormalizedPreRate f z := by
  have hd : 0 ≤ 1+fiberMass volume f z.1.1 := by
    have h : 0 ≤ fiberMass volume f z.1.1 := integral_nonneg (fun v => hf (z.1.1,v))
    linarith
  exact ⟨div_nonneg (regularizedPreRate_bounds hN hf z).1 hd,
    div_le_div_of_nonneg_right (regularizedPreRate_le_physical hN hf z) hd⟩

variable {μ : Measure X} [SFinite μ]

omit [SFinite μ] in
theorem massRegularizedPreRate_integrable {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (massRegularizedPreRate N f)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  apply (massNormalizedPreRate_integrable hfm hi).mono'
    (massRegularizedPreRate_measurable N hfm).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_of_nonneg (massRegularizedPreRate_bounds hN hf z).1]
  exact (massRegularizedPreRate_bounds hN hf z).2

theorem massRegularizedPostRate_integrable {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (weightedNormalizedPair f) (μ.prod (volume : Measure (Velocity × Velocity)))) :
    Integrable (massRegularizedPostRate N f)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) :=
  (scatterTriple_measurePreserving μ).integrable_comp_of_integrable
    (massRegularizedPreRate_integrable hN hfm hf hi)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Entropy controls the mass-normalized collision rate outside velocity windows -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem massPreRate_velocity_tail {R C : ℝ} (hR : 0 < R)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyGauge f) (μ.prod volume))
    (hb : (∫ p, entropyGauge f p ∂μ.prod volume) ≤ C) :
    eLpNorm ((collisionWindow R)ᶜ.indicator (massNormalizedPreRate f)) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
      ENNReal.ofReal (16*C/R)*eLpNorm (fun _ : Sphere => (1:ℝ)) 1 sphereArea := by
  let u : X × (Velocity × Velocity) → ℝ :=
    fun z => weightedNormalizedPair f z-pairVelocityCut (R/2) f z
  have hum : Measurable u :=
    (weightedNormalizedPair_measurable hfm).sub (pairVelocityCut_measurable (R/2) hfm)
  have hdom (z : (X × (Velocity × Velocity)) × Sphere) :
      ‖((collisionWindow R)ᶜ.indicator (massNormalizedPreRate f)) z‖ ≤ ‖u z.1‖ := by
    by_cases hz : z ∈ collisionWindow R
    · rw [indicator_of_notMem (notMem_compl_iff.mpr hz),norm_zero]
      exact norm_nonneg _
    · have hbox : ¬(‖z.1.2.1‖ ≤ R/2 ∧ ‖z.1.2.2‖ ≤ R/2) := by
        intro h
        have hv : ‖z.1.2.1‖^2 ≤ (R/2)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h.1
        have hw : ‖z.1.2.2‖^2 ≤ (R/2)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h.2
        apply hz
        change ‖z.1.2.1‖^2+‖z.1.2.2‖^2 ≤ R^2
        nlinarith [sq_nonneg R]
      rw [indicator_of_mem (mem_compl hz),massNormalizedPreRate_eq]
      change ‖normalizedKernel z*weightedNormalizedPair f z.1‖ ≤
        ‖weightedNormalizedPair f z.1-pairVelocityCut (R/2) f z.1‖
      simp only [pairVelocityCut,hbox,ite_false, if_false,sub_zero,norm_mul]
      exact (mul_le_mul_of_nonneg_right (normalizedKernel_bound z) (norm_nonneg _)).trans_eq (one_mul _)
  have hm := (massNormalizedPreRate_measurable hfm).indicator (collisionWindow_measurable R).compl
  have hn := eLpNorm_mono (p := 1) (μ := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) hdom
  have hp := eLpNorm_mul_prod_one (μ := μ.prod (volume.prod volume))
    (ν := sphereArea) hum (g := fun _ : Sphere => (1:ℝ)) measurable_const
  simp only [mul_one] at hp
  rw [Measure.volume_eq_prod] at hn
  rw [hp] at hn
  apply hn.trans
  have he := pairVelocityCut_L1_error (half_pos hR) hfm hf hi hb
  have hc : 8*C/(R/2) = 16*C/R := by ring
  rw [hc] at he
  exact mul_le_mul' he le_rfl

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual finite pre-rates converge to physical pre-rates on each collision window -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem collisionWindow_mono {R N : ℝ} (hR : 0 ≤ R) (hRN : R ≤ N) :
    collisionWindow (X := X) R ⊆ collisionWindow N := by
  intro z hz
  exact hz.trans ((sq_le_sq₀ hR (hR.trans hRN)).mpr hRN)

omit [MeasurableSpace X] in
theorem massRegularizedPreRate_on_window {R N : ℝ} (hR : 0 ≤ R) (hRN : R ≤ N)
    (f : X × Velocity → ℝ) (z : (X × (Velocity × Velocity)) × Sphere)
    (hz : z ∈ collisionWindow R) :
    massRegularizedPreRate N f z = rateMultiplier N f z*massNormalizedPreRate f z := by
  unfold massRegularizedPreRate massNormalizedPreRate
  rw [regularizedPreRate_factor,windowKernel,indicator_of_mem (collisionWindow_mono hR hRN hz)]
  unfold preRate
  ring

omit [MeasurableSpace X] in
theorem massRegularizedPreRate_window_difference {R N : ℝ} (hR : 0 ≤ R) (hRN : R ≤ N)
    (f : X × Velocity → ℝ) :
    (collisionWindow R).indicator (fun z => massRegularizedPreRate N f z-massNormalizedPreRate f z) =
      fun z => -((collisionWindow R).indicator (fun z => 1-rateMultiplier N f z) z *
        massNormalizedPreRate f z) := by
  funext z
  by_cases hz : z ∈ collisionWindow R
  · rw [indicator_of_mem hz,indicator_of_mem hz,massRegularizedPreRate_on_window hR hRN f z hz]
    ring
  · simp only [indicator_of_notMem hz,zero_mul,neg_zero]

variable {μ : Measure X} [IsFiniteMeasure μ]

theorem massRegularizedPreRate_window_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (R : ℝ) (hR : 0 ≤ R)
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm ((collisionWindow R).indicator
      (fun z => massRegularizedPreRate (N n) (f n) z-massNormalizedPreRate (f n) z)) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) atTop (𝓝 0) := by
  have ht := collisionAttenuation_preRate_L1 R hR hfm hf hi hb hN hNt B hB
  have he : (fun n => eLpNorm ((collisionWindow R).indicator
      (fun z => massRegularizedPreRate (N n) (f n) z-massNormalizedPreRate (f n) z)) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) =ᶠ[atTop]
      (fun n => eLpNorm (fun z => (collisionWindow R).indicator
        (fun z => 1-rateMultiplier (N n) (f n) z) z*massNormalizedPreRate (f n) z) 1
        ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) := by
    filter_upwards [hNt.eventually (eventually_ge_atTop R)] with n hn
    rw [massRegularizedPreRate_window_difference hR hn]
    exact eLpNorm_neg _ _ _
  exact (tendsto_congr' he).mpr ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing every collision cutoff from the mass-normalized actual rates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

omit [MeasurableSpace X] [IsFiniteMeasure μ] in
private theorem massRegularizedPreRate_difference_bound {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    |massRegularizedPreRate N f z-massNormalizedPreRate f z| ≤ |massNormalizedPreRate f z| := by
  have h := massRegularizedPreRate_bounds hN hf z
  rw [abs_of_nonpos (sub_nonpos.mpr h.2),abs_of_nonneg (h.1.trans h.2)]
  linarith

theorem massRegularizedPreRate_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm (fun z => massRegularizedPreRate (N n) (f n) z-
      massNormalizedPreRate (f n) z) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) atTop (𝓝 0) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let d n := fun z => massRegularizedPreRate (N n) (f n) z-massNormalizedPreRate (f n) z
  let P := eLpNorm (fun _ : Sphere => (1:ℝ)) 1 sphereArea
  have hP : P ≠ ⊤ := (memLp_one_iff_integrable.mpr (integrable_const (1:ℝ))).eLpNorm_ne_top
  have hdm n : Measurable (d n) := (massRegularizedPreRate_measurable (N n) (hfm n)).sub
    (massNormalizedPreRate_measurable (hfm n))
  have htail (R : ℝ) (hR : 0 < R) (n : ℕ) :
      eLpNorm ((collisionWindow R)ᶜ.indicator (d n)) 1 ν ≤ ENNReal.ofReal (16*C/R)*P := by
    apply le_trans (b := eLpNorm ((collisionWindow R)ᶜ.indicator (massNormalizedPreRate (f n))) 1 ν)
    · apply eLpNorm_mono
      intro z
      by_cases hz : z ∈ collisionWindow R
      · simp only [indicator_of_notMem (notMem_compl_iff.mpr hz),norm_zero,le_refl]
      · simp only [indicator_of_mem (mem_compl hz),Real.norm_eq_abs]
        exact massRegularizedPreRate_difference_bound (hN n) (hf n) z
    · exact massPreRate_velocity_tail hR (hfm n) (hf n) (hi n) (hb n)
  have hsplit (R : ℝ) (n : ℕ) : eLpNorm (d n) 1 ν ≤
      eLpNorm ((collisionWindow R).indicator (d n)) 1 ν+
        eLpNorm ((collisionWindow R)ᶜ.indicator (d n)) 1 ν := by
    have he : d n = (collisionWindow R).indicator (d n)+(collisionWindow R)ᶜ.indicator (d n) := by
      funext z
      by_cases hz : z ∈ collisionWindow R <;> simp [hz]
    conv_lhs => rw [he]
    exact eLpNorm_add_le (hf := ((hdm n).indicator (collisionWindow_measurable R)).aestronglyMeasurable)
      (hg := ((hdm n).indicator (collisionWindow_measurable R).compl).aestronglyMeasurable) (by norm_num)
  have hδ : Tendsto (fun j : ℕ => ENNReal.ofReal (16*C/((j:ℝ)+1))*P) atTop (𝓝 0) := by
    have ht := ENNReal.tendsto_ofReal (tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds) :
      Tendsto (fun j : ℕ => 16*C/((j:ℝ)+1)) atTop (𝓝 0))
    simpa only [ENNReal.ofReal_zero,zero_mul] using ENNReal.Tendsto.mul_const ht (Or.inr hP)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have hε2 : 0 < ε/2 := ENNReal.div_pos hε.ne' (by norm_num)
  obtain ⟨j,hj⟩ := (ENNReal.tendsto_nhds_zero.mp hδ (ε/2) hε2).exists
  have hR : 0 < (j:ℝ)+1 := by positivity
  have hw := massRegularizedPreRate_window_L1 ((j:ℝ)+1) hR.le hfm hf hi hb hN hNt B hB
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hw (ε/2) hε2] with n hn
  exact (hsplit ((j:ℝ)+1) n).trans ((add_le_add hn ((htail _ hR n).trans hj)).trans_eq ε.add_halves)

theorem massRegularizedPostRate_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm (fun z => massRegularizedPostRate (N n) (f n) z-
      massNormalizedPostRate (f n) z) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) atTop (𝓝 0) := by
  have he n : eLpNorm (fun z => massRegularizedPostRate (N n) (f n) z-
      massNormalizedPostRate (f n) z) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      eLpNorm (fun z => massRegularizedPreRate (N n) (f n) z-
        massNormalizedPreRate (f n) z) 1
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
    have hc : (fun z => massRegularizedPostRate (N n) (f n) z-massNormalizedPostRate (f n) z) =
        (fun z => massRegularizedPreRate (N n) (f n) z-massNormalizedPreRate (f n) z) ∘ scatterTriple := by
      funext z
      rfl
    rw [hc]
    exact eLpNorm_comp_measurePreserving
      ((massRegularizedPreRate_measurable (N n) (hfm n)).sub
        (massNormalizedPreRate_measurable (hfm n))).aestronglyMeasurable
      (scatterTriple_measurePreserving μ)
  simpa only [he] using massRegularizedPreRate_L1 hfm hf hi hb hN hNt B hB

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Removing finite collision attenuation from the mass-normalized gain -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness CollisionCompactness.DoubleGain
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem massRegularized_gain {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ) (p : X × Velocity) :
    collisionMarginal (massRegularizedPostRate N f) p = gain N f p/(1+fiberMass volume f p.1) := by
  change (∫ q : Velocity × Sphere,
    regularizedPostRate N f (collisionGrouping.symm (p,q))/(1+fiberMass volume f p.1)
      ∂(volume : Measure Velocity).prod sphereArea) = _
  rw [integral_div,← gain_eq_full_integral hN]

theorem massNormalized_gain (f : X × Velocity → ℝ) (p : X × Velocity) :
    collisionMarginal (massNormalizedPostRate f) p = gainDensity f p/(1+fiberMass volume f p.1) := by
  change (∫ q : Velocity × Sphere,
    postRate f (collisionGrouping.symm (p,q))/(1+fiberMass volume f p.1)
      ∂(volume : Measure Velocity).prod sphereArea) = _
  rw [integral_div]
  rfl

theorem massRegularizedGain_L1
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) (hNt : Tendsto N atTop atTop)
    (B : ℝ≥0) (hB : ∀ n, eLpNorm (f n) 1 (μ.prod volume) ≤ B) :
    Tendsto (fun n => eLpNorm (fun p =>
      gain (N n) (f n) p/(1+fiberMass volume (f n) p.1)-
      gainDensity (f n) p/(1+fiberMass volume (f n) p.1)) 1 (μ.prod volume)) atTop (𝓝 0) := by
  have herr := massRegularizedPostRate_L1 hfm hf hi hb hN hNt B hB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds herr (fun _ => zero_le)
  intro n
  have hwi : Integrable (weightedNormalizedPair (f n))
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
    simpa only [Measure.volume_eq_prod] using weightedNormalizedPair_integrable (hfm n) (hf n) (hi n)
  have hm := massRegularizedPostRate_measurable (N n) (hfm n)
  have km := massNormalizedPostRate_measurable (hfm n)
  have hri := massRegularizedPostRate_integrable (hN n) (hfm n) (hf n) hwi
  have hpi := massNormalizedPostRate_integrable (hfm n) hwi
  have h := collisionMarginal_difference_le hm km hri hpi
  have he : collisionMarginal (massRegularizedPostRate (N n) (f n))-
      collisionMarginal (massNormalizedPostRate (f n)) =
      (fun p => gain (N n) (f n) p/(1+fiberMass volume (f n) p.1)-
        gainDensity (f n) p/(1+fiberMass volume (f n) p.1)) := by
    funext p
    exact congrArg₂ (fun a b : ℝ => a-b) (massRegularized_gain (hN n).le (f n) p)
      (massNormalized_gain (f n) p)
  rw [he] at h
  exact h

end BoltzmannNonuniqueness.PeriodicApproximation

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

/-! # Weak velocity averages of the same global periodic limit -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.kineticProfile_measurable {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) : Measurable G.kineticProfile :=
  G.measurable.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicFiniteGainStrong
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Strong convergence of the actual finite mass-normalized gains -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness CollisionCompactness.DoubleGain

theorem GlobalCollisionLimit.finite_gain_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    Tendsto (fun n => eLpNorm (fun p : (ℝ × Position) × Velocity =>
      gain ((G.weakLimit.indices n:ℝ)+1)
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p/
        (1+fiberMass volume (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p.1)-
      gainDensity G.weakLimit.kineticProfile p/(1+fiberMass volume G.weakLimit.kineticProfile p.1))
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let g := G.weakLimit.kineticProfile
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n p : 0 ≤ F n p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  have hEi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  let C := max ((volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f)
    (∫ p, entropyGauge g p ∂μ.prod volume)
  have hEb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤
      C := by
    apply le_trans _ (le_max_left _ _)
    exact (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  let N (n : ℕ) : ℝ := (G.weakLimit.indices n:ℝ)+1
  have hN n : 0 < N n := by dsimp [N] <;> positivity
  have hNt : Tendsto N atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp G.weakLimit.increasing.tendsto_atTop).atTop_add tendsto_const_nhds
  obtain ⟨B,hB⟩ := (approximatingSolution_compactness_hypotheses f hfm hf hi
    (volume.restrict (Icc 0 T))).1.2
  have hFB n : eLpNorm (F n) 1 (μ.prod volume) ≤ B := hB (G.weakLimit.indices n)
  have hr := massRegularizedGain_L1 hFm hFn hEi hEb hN hNt B hFB
  let ν : Measure ((ℝ × Position) × Velocity) :=
    μ.prod ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))
  have hν : ν ≤ μ.prod volume := Measure.prod_mono le_rfl Measure.restrict_le_self
  have hrl : Tendsto (fun n => eLpNorm (fun p =>
      gain (N n) (F n) p/(1+fiberMass volume (F n) p.1)-
      gainDensity (F n) p/(1+fiberMass volume (F n) p.1)) 1 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr (fun _ => zero_le)
      (fun _ => eLpNorm_mono_measure _ hν)
  have hp := G.normalized_gain_strong_q80 hf hi hT R
  have hp' : Tendsto (fun n => eLpNorm (fun p =>
      gainDensity (F n) p/(1+fiberMass volume (F n) p.1)-
      gainDensity g p/(1+fiberMass volume g p.1)) 1 ν) atTop (𝓝 0) := by
    simpa only [normalizedPair_gain] using hp
  have ht := hrl.add hp'
  simp only [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
  intro n
  have he : (fun p => gain (N n) (F n) p/(1+fiberMass volume (F n) p.1)-
      gainDensity g p/(1+fiberMass volume g p.1)) =
      (fun p => gain (N n) (F n) p/(1+fiberMass volume (F n) p.1)-
        gainDensity (F n) p/(1+fiberMass volume (F n) p.1))+
      (fun p => gainDensity (F n) p/(1+fiberMass volume (F n) p.1)-
        gainDensity g p/(1+fiberMass volume g p.1)) := by
    funext p
    simp only [Pi.add_apply]
    ring
  change eLpNorm (fun p => gain (N n) (F n) p/(1+fiberMass volume (F n) p.1)-
    gainDensity g p/(1+fiberMass volume g p.1)) 1 ν ≤ _
  rw [he]
  have hgm : Measurable g := G.weakLimit.kineticProfile_measurable
  exact eLpNorm_add_le
    (hf := ((gain_measurable (N n) (hFm n)).div (measurable_const.add ((fiberMass_measurable (hFm n)).comp measurable_fst))).sub
      ((gainDensity_measurable (hFm n)).div (measurable_const.add ((fiberMass_measurable (hFm n)).comp measurable_fst)))
      |>.aestronglyMeasurable)
    (hg := ((gainDensity_measurable (hFm n)).div (measurable_const.add ((fiberMass_measurable (hFm n)).comp measurable_fst))).sub
      ((gainDensity_measurable hgm).div (measurable_const.add ((fiberMass_measurable hgm).comp measurable_fst)))
      |>.aestronglyMeasurable) (by norm_num)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_GainMeasureLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Unnormalizing the convergent physical gain on a bounded velocity window -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {ν : Measure Velocity} [IsFiniteMeasure ν]

theorem physical_gain_tendstoInMeasure
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {N : ℕ → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n p, 0 ≤ f n p) (hg : ∀ p, 0 ≤ g p)
    (hm : Tendsto (fun n => eLpNorm
      (fun x => fiberMass volume (f n) x-fiberMass volume g x) 1 μ) atTop (𝓝 0))
    (ha : Tendsto (fun n => eLpNorm (fun p =>
      gain (N n) (f n) p/(1+fiberMass volume (f n) p.1)-
      gainDensity g p/(1+fiberMass volume g p.1)) 1 (μ.prod ν)) atTop (𝓝 0)) :
    TendstoInMeasure (μ.prod ν) (fun n => gain (N n) (f n)) atTop (gainDensity g) := by
  have hrm n : Measurable (fiberMass volume (f n)) := fiberMass_measurable (hfm n)
  have hsm : Measurable (fiberMass volume g) := fiberMass_measurable hgm
  have hr : Tendsto (fun n => eLpNorm (fun p : X × Velocity =>
      fiberMass volume (f n) p.1-fiberMass volume g p.1) 1 (μ.prod ν)) atTop (𝓝 0) :=
    strongL1_comp_fst (f := fun n x => fiberMass volume (f n) x-fiberMass volume g x)
      (fun n => (hrm n).sub hsm) hm
  have hr0 : ∀ n p, 0 ≤ fiberMass volume (f n) p := by
    intro n x
    exact integral_nonneg (fun v => hf n (x,v))
  have hs0 : ∀ x, 0 ≤ fiberMass volume g x := by
    intro x
    exact integral_nonneg (fun v => hg (x,v))
  exact tendstoInMeasure_of_strong_massNormalized (μ := μ.prod ν)
    (fun n => gain_measurable (N n) (hfm n))
    (fun n => (hrm n).comp measurable_fst) (fun n p => hr0 n p.1)
    (fun p => hs0 p.1) hr ha (by exact hsm.comp measurable_fst) (by exact gainDensity_measurable hgm)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PeriodicCharacteristicGainUnit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual finite physical gains converge locally in measure -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.gain_in_measure_q80_oai {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    TendstoInMeasure
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))
      (fun n => gain ((G.weakLimit.indices n:ℝ)+1)
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      atTop (gainDensity G.weakLimit.kineticProfile) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let ν : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let : IsFiniteMeasure ν :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  have hFm (n : ℕ) : Measurable (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn (n : ℕ) (p : (ℝ × Position) × Velocity) :
      0 ≤ (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  exact physical_gain_tendstoInMeasure (μ := μ) (ν := ν) hFm
    G.weakLimit.kineticProfile_measurable hFn (fun _ => G.weakLimit.nonnegative _)
    (G.mass_strong T hT) (G.finite_gain_strong hf hi hT R)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_in_measure_q80_oai := @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.gain_in_measure_q80_oai
