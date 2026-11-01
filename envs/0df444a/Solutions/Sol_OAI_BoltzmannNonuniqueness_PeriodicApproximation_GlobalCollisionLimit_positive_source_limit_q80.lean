-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_source_limit_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:23:04.617485+00:00
-- url     : https://prove2.me/submissions/5a970731-05e7-4964-bf03-c2449c6b8025

import Mathlib
import Definitions.Def_BoltzmannNonuniqueness
import Definitions.Def_OAIQ080A002

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

theorem uniformIntegrable_integral {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [IsFiniteMeasure ν] {f : ℕ → X × Y → ℝ}
    (hf : ∀ n, Measurable (f n)) (hui : UniformIntegrable f 1 (μ.prod ν)) :
    UniformIntegrable (fun n x => ∫ y, f n (x,y) ∂ν) 1 μ := by
  constructor
  · apply OAI.UnifIntegrable.of_enn'
    intro ε hε
    obtain ⟨δ,hδ,hsmall⟩ := OAI.UnifIntegrable.enn_spec' hui.1 ε hε
    let B : ℝ≥0∞ := ν univ+1
    have hB : B ≠ 0 := by simp [B]
    have hBtop : B ≠ ∞ := by simp [B,measure_ne_top]
    refine ⟨δ/B,ENNReal.div_pos hδ.ne' hBtop,?_⟩
    intro n s hs hμs
    have hvol : (μ.prod ν) (s ×ˢ univ) ≤ δ := by
      rw [Measure.prod_prod]
      calc
        μ s*ν univ ≤ (δ/B)*B := mul_le_mul' hμs (le_self_add)
        _ = δ := ENNReal.div_mul_cancel hB hBtop
    calc
      _ ≤ eLpNorm (f n) 1 ((μ.restrict s).prod ν) := eLpNorm_integral_le (hf n)
      _ = eLpNorm (f n) 1 ((μ.prod ν).restrict (s ×ˢ univ)) := by
        rw [← Measure.prod_restrict,Measure.restrict_univ]
      _ ≤ ε := hsmall n (s ×ˢ univ) (hs.prod MeasurableSet.univ) hvol
    exact fun n => (hui.aestronglyMeasurable n).integral_prod_right'
  · obtain ⟨C,hC⟩ := hui.2
    exact ⟨C,fun n => (eLpNorm_integral_le (hf n)).trans (hC n)⟩

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakL1Operations
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

section

/-! # Extending a weak L¹ sequence by a finite angular measure -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.Published

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem WeakL1Converges.prod_constant {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [IsFiniteMeasure ν] {f : ℕ → X → ℝ} {g : X → ℝ}
    (h : WeakL1Converges μ f g) (hf : ∀ n, Integrable (f n) μ) :
    WeakL1Converges (μ.prod ν) (fun n z => f n z.1) (fun z => g z.1) := by
  refine ⟨h.1.comp measurable_fst,h.2.1.comp_fst ν,?_⟩
  intro ψ hψ hB
  obtain ⟨C,hC⟩ := hB
  have hbound : ∀ x, |∫ y, ψ (x,y) ∂ν| ≤ max C 0*ν.real Set.univ := by
    intro x
    have hi : Integrable (fun _ : Y => max C 0) ν := integrable_const _
    have hb := norm_integral_le_of_norm_le hi (ae_of_all _ (fun y =>
      (show ‖ψ (x,y)‖ ≤ C from hC (x,y)).trans (le_max_left C 0)))
    simpa only [integral_const,smul_eq_mul,Real.norm_eq_abs,mul_comm] using hb
  have ht := h.2.2 (fun x => ∫ y, ψ (x,y) ∂ν)
    hψ.stronglyMeasurable.integral_prod_right'.measurable ⟨_,hbound⟩
  have he (u : X → ℝ) (hu : Integrable u μ) :
      (∫ z, ψ z*u z.1 ∂μ.prod ν) = ∫ x, (∫ y, ψ (x,y) ∂ν)*u x ∂μ := by
    have hi := (hu.comp_fst ν).bdd_mul hψ.aestronglyMeasurable (ae_of_all _ hC)
    rw [integral_prod _ hi]
    simp_rw [integral_mul_const]
  simpa only [he _ (hf _),he _ h.2.1] using ht

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The time primitive is weakly continuous on a finite time interval -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.Published

variable {P : Type*} [MeasurableSpace P]

theorem timeExchange_measurePreserving (μ : Measure ℝ) (ν : Measure P) [SFinite μ] [SFinite ν] :
    MeasurePreserving (timeExchange (P := P)) ((μ.prod ν).prod μ) ((μ.prod ν).prod μ) := by
  exact (measurePreserving_prodAssoc μ ν μ).symm.comp
    (((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := μ) (ν := ν))).comp
      (Measure.measurePreserving_swap (μ := μ.prod ν) (ν := μ)))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak L1 convergence extended by zero from a fixed measurable window -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published
variable {X : Type*} [MeasurableSpace X]

theorem WeakL1Converges.zeroExtension {μ : Measure X} {s : Set X}
    {f : ℕ → X → ℝ} {g : X → ℝ} (hs : MeasurableSet s)
    (h : WeakL1Converges (μ.restrict s) f g) :
    WeakL1Converges μ (fun n => s.indicator (f n)) (s.indicator g) := by
  refine ⟨h.1.indicator hs,(integrable_indicator_iff hs).mpr h.2.1,?_⟩
  intro ψ hψ hB
  have he (u : X → ℝ) : (∫ x, ψ x*s.indicator u x ∂μ) = ∫ x in s, ψ x*u x ∂μ := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ s <;> simp [hx]
  simpa only [he] using h.2.2 ψ hψ hB

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

/-! # Uniform integrability under bounded varying coefficients -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_of_varying_multiplier
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f a : ℕ → X → ℝ}
    (hf : UniformIntegrable f 1 μ) (ha : ∀ n, Measurable (a n))
    (C : ℝ≥0) (hC : ∀ n x, |a n x| ≤ C) :
    UniformIntegrable (fun n x => a n x*f n x) 1 μ := by
  have hconst := uniformIntegrable_of_bounded_multiplier hf
    (a := fun _ => (C:ℝ)) measurable_const C (fun _ => by simp)
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => a n x*f n x) μ :=
    (ha n).aestronglyMeasurable.mul (hf.aestronglyMeasurable n)
  have hb (n : ℕ) : ∀ᵐ x ∂μ, ‖a n x*f n x‖ₑ ≤ ‖(C:ℝ)*f n x‖ₑ := by
    filter_upwards [] with x
    apply ENNReal.coe_le_coe.mpr
    apply NNReal.coe_le_coe.mp
    change ‖a n x*f n x‖ ≤ ‖(C:ℝ)*f n x‖
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg C.coe_nonneg]
    exact mul_le_mul_of_nonneg_right (hC n x) (abs_nonneg _)
  obtain ⟨hu,B,hB⟩ := hconst
  exact ⟨hu.ae_mono hm hb,B,fun n => (eLpNorm_mono_enorm_ae (hb n)).trans (hB n)⟩

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

/-! # Extending uniformly integrable families by zero from a measurable region -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.Compactness

theorem uniformIntegrable_indicator_of_restrict
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : ℕ → X → ℝ}
    {s : Set X} (hs : MeasurableSet s) (hf : UniformIntegrable f 1 (μ.restrict s)) :
    UniformIntegrable (fun n => s.indicator (f n)) 1 μ := by
  constructor
  · apply OAI.UnifIntegrable.of_enn'
    intro ε hε
    obtain ⟨δ,hδ,hsmall⟩ := OAI.UnifIntegrable.enn_spec' hf.1 ε hε
    refine ⟨δ,hδ,fun n a ha hμa => ?_⟩
    calc
      _ = eLpNorm (f n) 1 ((μ.restrict s).restrict a) := by
        rw [eLpNorm_indicator_eq_eLpNorm_restrict hs,
          Measure.restrict_restrict hs,Measure.restrict_restrict ha,inter_comm]
      _ ≤ ε := hsmall n a ha ((Measure.restrict_le_self a).trans hμa)
    exact fun n => (aestronglyMeasurable_indicator_iff hs).2 (hf.aestronglyMeasurable n)
  · obtain ⟨C,hC⟩ := hf.2
    refine ⟨C,fun n => ?_⟩
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    exact hC n

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

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable physical gain and loss and their equal total mass -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_ra92858_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
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

section

/-! # Weak convergence of the physical gain and loss marginals -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_3_ra92858_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
theorem weak_grouped_rate {μ : Measure X} [SFinite μ]
    {r : ℕ → ((X × (Velocity × Velocity)) × Sphere) → ℝ}
    {s : ((X × (Velocity × Velocity)) × Sphere) → ℝ}
    (hr : ∀ n, Measurable (r n)) (hs : Measurable s)
    (h : Published.WeakL1Converges
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) r s) :
    Published.WeakL1Converges
      ((μ.prod (volume : Measure Velocity)).prod ((volume : Measure Velocity).prod sphereArea))
      (fun n z => r n (collisionGrouping.symm z)) (fun z => s (collisionGrouping.symm z)) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (collisionGrouping_measurePreserving μ)
    (fun n => (hr n).comp collisionGrouping.symm.measurable)
    (hs.comp collisionGrouping.symm.measurable)
  simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using h

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformIntegrableGainTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform integrability of marginals with fixed finite-measure velocity support -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem uniformIntegrable_integral_of_support {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] {s : Set Y} [IsFiniteMeasure (ν.restrict s)]
    (hs : MeasurableSet s) {f : ℕ → X × Y → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hui : UniformIntegrable f 1 (μ.prod ν))
    (hf : ∀ n x y, y ∉ s → f n (x,y) = 0) :
    UniformIntegrable (fun n x => ∫ y, f n (x,y) ∂ν) 1 μ := by
  have hu := uniformIntegrable_restrict hui (univ ×ˢ s)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hu
  have h := uniformIntegrable_integral hfm hu
  have he (n : ℕ) (x : X) : (∫ y in s, f n (x,y) ∂ν) = ∫ y, f n (x,y) ∂ν := by
    rw [← integral_indicator hs]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ s
    · exact indicator_of_mem hy _
    · rw [indicator_of_notMem hy,hf n x y hy]
  simpa only [he] using h

end BoltzmannNonuniqueness.Compactness

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
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.hotKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.mixedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PeriodicApproximation.fiberMeasure_finite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.eventParameterMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.markedEventMeasure_isFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
attribute [-simp] _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.phaseEquiv_snd _root_.OAI.BoltzmannNonuniqueness.timeTranslation_apply
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

/-! # Local uniform integrability of the mass-normalized physical collision rates -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_WeakL1ToWeakStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # A bounded strongly convergent coefficient times a uniformly integrable weak limit -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Published

theorem WeakL1Converges.varying_bounded_mul
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f a : ℕ → X → ℝ} {g b : X → ℝ}
    (hw : WeakL1Converges μ f g) (hu : UniformIntegrable f 1 μ)
    (hfm : ∀ n, Measurable (f n)) (ham : ∀ n, Measurable (a n)) (hbm : Measurable b)
    (C : ℝ≥0) (ha : ∀ n x, |a n x| ≤ C) (hb : ∀ x, |b x| ≤ C)
    (hs : Tendsto (fun n => eLpNorm (fun x => a n x-b x) 1 μ) atTop (𝓝 0)) :
    WeakL1Converges μ (fun n x => a n x*f n x) (fun x => b x*g x) := by
  have he := Compactness.tendsto_L1_mul_uniformIntegrable hu hfm
    (fun n => (ham n).sub hbm) hs (C+C) (fun n x => by
      exact (abs_sub (a n x) (b x)).trans (add_le_add (ha n x) (hb x)))
  apply (hw.bounded_mul hbm C hb).of_eLpNorm_sub
  · exact fun n => (memLp_one_iff_integrable.mp (hu.memLp n)).bdd_mul
      hbm.aestronglyMeasurable (ae_of_all μ hb)
  · exact fun n => (memLp_one_iff_integrable.mp (hu.memLp n)).bdd_mul
      (ham n).aestronglyMeasurable (ae_of_all μ (ha n))
  · convert he using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    congr 1
    funext x
    simp only [Pi.sub_apply]
    ring

end BoltzmannNonuniqueness.Published

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

theorem massClip_measurable (K : ℝ) {r : X → ℝ} (hr : Measurable r) :
    Measurable (fun x => massClip K (r x)) :=
  measurable_const.min (measurable_const.add hr)

theorem massClip_bounds {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r) :
    0 ≤ massClip K r ∧ massClip K r ≤ K :=
  ⟨le_min hK (by linarith),min_le_left _ _⟩

theorem massClip_lipschitz (K r s : ℝ) :
    |massClip K r-massClip K s| ≤ |r-s| := by
  simpa only [massClip,sub_self,abs_zero,add_sub_add_left_eq_sub,max_eq_right (abs_nonneg (r-s))]
    using abs_min_sub_min_le_max K (1+r) K (1+s)

theorem strong_massClip {r : ℕ → X → ℝ} {s : X → ℝ}
    (hr : ∀ n, Measurable (r n)) (hs : Measurable s) (K : ℝ)
    (h : Tendsto (fun n => eLpNorm (fun x => r n x-s x) 1 μ) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => massClip K (r n x)-massClip K (s x)) 1 μ)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
  intro n
  apply eLpNorm_mono
  intro x
  simpa only [Real.norm_eq_abs,Pi.sub_apply] using massClip_lipschitz K (r n x) (s x)

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Stability of the nonnegative loss integrating factor -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.AttenuationLipschitz

private theorem exp_neg_difference_ordered {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (-a) - Real.exp (-b) ≤ b - a := by
  have he : Real.exp (a - b) ≤ 1 := Real.exp_le_one_iff.mpr (sub_nonpos.mpr hab)
  have hne : 0 ≤ 1 - Real.exp (a - b) := sub_nonneg.mpr he
  have heq : Real.exp (-b) = Real.exp (-a) * Real.exp (a - b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = Real.exp (-a) * (1 - Real.exp (a - b)) := by rw [heq]; ring
    _ ≤ 1 - Real.exp (a - b) :=
      mul_le_of_le_one_left hne (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha))
    _ ≤ b - a := by linarith [Real.add_one_le_exp (a - b)]

theorem exp_neg_difference {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  rcases le_total a b with hab | hba
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hab))),
      abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    exact exp_neg_difference_ordered ha hab
  · rw [abs_sub_comm (Real.exp (-a)), abs_sub_comm a,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (neg_le_neg hba))),
      abs_of_nonpos (sub_nonpos.mpr hba), neg_sub]
    exact exp_neg_difference_ordered hb hba

end BoltzmannNonuniqueness.AttenuationLipschitz

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

/-! # Strong L1 continuity of the time primitive on a finite time window -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
open Compactness
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [SFinite ν]

theorem strong_timePrimitive {f : ℕ → ℝ × P → ℝ} {g : ℝ × P → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (ht : Tendsto (fun n => eLpNorm (f n-g) 1 (μ.prod ν)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (timePrimitive μ (f n)-timePrimitive μ g) 1 (μ.prod ν))
      atTop (𝓝 0) := by
  let F n (z : (ℝ × P) × ℝ) := f n (z.2,z.1.2)
  let G (z : (ℝ × P) × ℝ) := g (z.2,z.1.2)
  have hFm n : Measurable (F n) := (hfm n).comp (measurable_snd.prodMk measurable_fst.snd)
  have hGm : Measurable G := hgm.comp (measurable_snd.prodMk measurable_fst.snd)
  have hFi n : Integrable (F n) ((μ.prod ν).prod μ) :=
    (timeExchange_measurePreserving μ ν).integrable_comp_of_integrable ((hfi n).comp_fst μ)
  have hGi : Integrable G ((μ.prod ν).prod μ) :=
    (timeExchange_measurePreserving μ ν).integrable_comp_of_integrable (hgi.comp_fst μ)
  have hlift := strongL1_comp_fst (ν := μ) (fun n => (hfm n).sub hgm) ht
  have hex n : eLpNorm (F n-G) 1 ((μ.prod ν).prod μ) =
      eLpNorm (fun z : (ℝ × P) × ℝ => (f n-g) z.1) 1 ((μ.prod ν).prod μ) := by
    have hc : F n-G = (fun z : (ℝ × P) × ℝ => (f n-g) z.1) ∘ timeExchange := by
      funext z
      rfl
    rw [hc]
    exact eLpNorm_comp_measurePreserving
      (((hfm n).sub hgm).comp measurable_fst).aestronglyMeasurable
      (timeExchange_measurePreserving μ ν)
  have ht' : Tendsto (fun n => eLpNorm (F n-G) 1 ((μ.prod ν).prod μ)) atTop (𝓝 0) := by
    simpa only [hex] using hlift
  let k (z : (ℝ × P) × ℝ) : ℝ := if z.2 ≤ z.1.1 then 1 else 0
  have hkm : Measurable k := measurable_const.ite
    (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  have hkb z : |k z| ≤ 1 := by dsimp only [k]; split <;> norm_num
  have he (u : ℝ × P → ℝ) z : (∫ s, k (z,s)*u (s,z.2) ∂μ) = timePrimitive μ u z := by
    apply integral_congr_ae
    apply ae_of_all
    intro s
    dsimp only [k,timePrimitive]
    split <;> simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht' (fun _ => zero_le)
  intro n
  have h := weighted_average_difference_le (hFm n) hGm hkm (hFi n) hGi hkb
  change eLpNorm (fun z => timePrimitive μ (f n) z-timePrimitive μ g z) 1 (μ.prod ν) ≤ _
  simpa only [F,G,he,ENNReal.ofReal_one,one_mul] using h

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

theorem strong_timeDifference {u : ℕ → ℝ × P → ℝ} {v : ℝ × P → ℝ}
    (hum : ∀ n, Measurable (u n)) (hvm : Measurable v)
    (ht : Tendsto (fun n => eLpNorm (u n-v) 1 (μ.prod ν)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (timeDifference (u n)-timeDifference v) 1 ((μ.prod ν).prod μ))
      atTop (𝓝 0) := by
  have hfirst := strongL1_comp_fst (ν := μ) (fun n => (hum n).sub hvm) ht
  have hsecond : Tendsto (fun n => eLpNorm
      (fun z : (ℝ × P) × ℝ => u n (z.2,z.1.2)-v (z.2,z.1.2)) 1 ((μ.prod ν).prod μ))
      atTop (𝓝 0) := by
    have he n : eLpNorm (fun z : (ℝ × P) × ℝ => u n (z.2,z.1.2)-v (z.2,z.1.2))
        1 ((μ.prod ν).prod μ) = eLpNorm (fun z : (ℝ × P) × ℝ => (u n-v) z.1)
        1 ((μ.prod ν).prod μ) := by
      have hc : (fun z : (ℝ × P) × ℝ => u n (z.2,z.1.2)-v (z.2,z.1.2)) =
          (fun z : (ℝ × P) × ℝ => (u n-v) z.1) ∘ timeExchange := by
        funext z
        rfl
      rw [hc]
      exact eLpNorm_comp_measurePreserving (((hum n).sub hvm).comp measurable_fst).aestronglyMeasurable
        (timeExchange_measurePreserving μ ν)
    simpa only [he] using hfirst
  have hs := hfirst.add hsecond
  simp only [zero_add] at hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => zero_le)
  intro n
  change eLpNorm (timeDifference (u n)-timeDifference v) 1 ((μ.prod ν).prod μ) ≤
    eLpNorm (fun z : (ℝ × P) × ℝ => (u n-v) z.1) 1 ((μ.prod ν).prod μ)+
      eLpNorm (fun z : (ℝ × P) × ℝ => u n (z.2,z.1.2)-v (z.2,z.1.2))
        1 ((μ.prod ν).prod μ)
  have he : timeDifference (u n)-timeDifference v =
      (fun z : (ℝ × P) × ℝ => (u n-v) z.1)-
      (fun z : (ℝ × P) × ℝ => u n (z.2,z.1.2)-v (z.2,z.1.2)) := by
    funext z
    dsimp only [timeDifference,Pi.sub_apply]
    ring
  rw [he]
  exact eLpNorm_sub_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num)

omit [MeasurableSpace P] [IsFiniteMeasure μ] [SFinite ν] in
theorem twoTimeSurvival_bounds (μ : Measure ℝ) (f : ℝ × P → ℝ) (z : (ℝ × P) × ℝ) :
    0 < twoTimeSurvival μ f z ∧ twoTimeSurvival μ f z ≤ 1 :=
  ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_left 0 _))⟩

theorem twoTimeSurvival_measurable {f : ℝ × P → ℝ} (hf : Measurable f) :
    Measurable (twoTimeSurvival μ f) :=
  (measurable_const.max (timeDifference_measurable (timePrimitive_measurable μ hf))).neg.exp

theorem strong_twoTimeSurvival {f : ℕ → ℝ × P → ℝ} {g : ℝ × P → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hfi : ∀ n, Integrable (f n) (μ.prod ν)) (hgi : Integrable g (μ.prod ν))
    (ht : Tendsto (fun n => eLpNorm (f n-g) 1 (μ.prod ν)) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (twoTimeSurvival μ (f n)-twoTimeSurvival μ g)
      1 ((μ.prod ν).prod μ)) atTop (𝓝 0) := by
  have h := strong_timeDifference (fun n => timePrimitive_measurable μ (hfm n))
    (timePrimitive_measurable μ hgm) (strong_timePrimitive hfm hgm hfi hgi ht)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
  intro n
  apply eLpNorm_mono
  intro z
  have he := AttenuationLipschitz.exp_neg_difference
    (le_max_left 0 (timeDifference (timePrimitive μ (f n)) z))
    (le_max_left 0 (timeDifference (timePrimitive μ g) z))
  have hm := abs_max_sub_max_le_max 0 (timeDifference (timePrimitive μ (f n)) z)
    0 (timeDifference (timePrimitive μ g) z)
  have hmax : max (0:ℝ)
      |timeDifference (timePrimitive μ (f n)) z-timeDifference (timePrimitive μ g) z| =
      |timeDifference (timePrimitive μ (f n)) z-timeDifference (timePrimitive μ g) z| :=
    max_eq_right (abs_nonneg _)
  simpa only [Pi.sub_apply,twoTimeSurvival,Real.norm_eq_abs,sub_self,abs_zero,
    hmax] using he.trans hm

end BoltzmannNonuniqueness.Published

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

/-! # Weak positive source integrals with strongly convergent survival kernels -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.Published
open Compactness
variable {P : Type*} [MeasurableSpace P]
variable {μ : Measure ℝ} {ν : Measure P} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem WeakL1Converges.survivalVolterra
    {f : ℕ → ℝ × P → ℝ} {g : ℝ × P → ℝ}
    {a : ℕ → (ℝ × P) × ℝ → ℝ} {b : (ℝ × P) × ℝ → ℝ}
    (hw : WeakL1Converges (μ.prod ν) f g) (hui : UniformIntegrable f 1 (μ.prod ν))
    (hfm : ∀ n, Measurable (f n)) (ham : ∀ n, Measurable (a n)) (hbm : Measurable b)
    (C : ℝ≥0) (ha : ∀ n z, |a n z| ≤ C) (hb : ∀ z, |b z| ≤ C)
    (hs : Tendsto (fun n => eLpNorm (a n-b) 1 ((μ.prod ν).prod μ)) atTop (𝓝 0)) :
    WeakL1Converges (μ.prod ν) (fun n => survivalVolterra μ (a n) (f n))
      (survivalVolterra μ b g) := by
  have hfi n := memLp_one_iff_integrable.mp (hui.memLp n)
  have hprod := hw.prod_constant (ν := μ) hfi
  have hlm n : Measurable (fun z : (ℝ × P) × ℝ => f n (z.2,z.1.2)) :=
    (hfm n).comp (measurable_snd.prodMk measurable_fst.snd)
  have hlg : Measurable (fun z : (ℝ × P) × ℝ => g (z.2,z.1.2)) :=
    hw.1.comp (measurable_snd.prodMk measurable_fst.snd)
  have hl : WeakL1Converges ((μ.prod ν).prod μ)
      (fun n z => f n (z.2,z.1.2)) (fun z => g (z.2,z.1.2)) := by
    apply WeakL1Converges.of_comp_measurePreserving (timeExchange_measurePreserving μ ν) hlm hlg
    exact hprod
  have hut : UniformIntegrable (fun n (z : (ℝ × P) × ℝ) => f n z.1) 1 ((μ.prod ν).prod μ) := by
    simpa only [mul_one] using uniformIntegrable_tensor hfm hui measurable_const
      (integrable_const (1:ℝ) : Integrable (fun _ : ℝ => (1:ℝ)) μ)
  have hul : UniformIntegrable (fun n (z : (ℝ × P) × ℝ) => f n (z.2,z.1.2))
      1 ((μ.prod ν).prod μ) := by
    apply uniformIntegrable_of_comp_measurePreserving (timeExchange_measurePreserving μ ν) hlm
    exact hut
  have hv := hl.varying_bounded_mul hul hlm ham hbm C ha hb hs
  have hvi n : Integrable (fun z : (ℝ × P) × ℝ => a n z*f n (z.2,z.1.2))
      ((μ.prod ν).prod μ) :=
    (memLp_one_iff_integrable.mp (hul.memLp n)).bdd_mul (ham n).aestronglyMeasurable
      (ae_of_all _ (ha n))
  let k : (ℝ × P) × ℝ → ℝ := fun z => if z.2 ≤ z.1.1 then 1 else 0
  have hkm : Measurable k := measurable_const.ite
    (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  have hkb : ∀ z, |k z| ≤ 1 := by intro z; dsimp [k]; split <;> norm_num
  have h := hv.marginal hvi hkm 1 hkb
  have he (A : (ℝ × P) × ℝ → ℝ) (F : ℝ × P → ℝ) :
      (fun z : ℝ × P => ∫ s, k (z,s)*(A (z,s)*F (s,z.2)) ∂μ) =
        Published.survivalVolterra μ A F := by
    funext z
    apply integral_congr_ae
    filter_upwards [] with s
    dsimp only [k,Published.survivalVolterra]
    split <;> simp
  have hseq : (fun n (z : ℝ × P) => ∫ s, k (z,s)*(a n (z,s)*f n (s,z.2)) ∂μ) =
      (fun n => Published.survivalVolterra μ (a n) (f n)) := funext (fun n => he (a n) (f n))
  rw [hseq,he b g] at h
  exact h

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

theorem weak_along_regroup_local {μ : Measure ℝ} {ν : Measure Velocity}
    [SFinite μ] [SFinite ν]
    {f : ℕ → (ℝ × Position) × Velocity → ℝ} {g : (ℝ × Position) × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n))
    (hw : Published.WeakL1Converges ((μ.prod volume).prod ν) f g) :
    Published.WeakL1Converges (μ.prod ((volume : Measure Position).prod ν))
      (fun n => along (regroup (f n))) (along (regroup g)) := by
  apply Published.WeakL1Converges.of_comp_measurePreserving (backRegroup_measurePreserving μ ν)
    (fun n => (hfm n).comp (alongRegroup_measurePreserving μ ν).measurable)
    (hw.1.comp (alongRegroup_measurePreserving μ ν).measurable)
  simpa only [along,regroup,Function.comp_def,neg_flight,flight_snd] using hw

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

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_UniformIntegrableCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform integrability under the coordinate and bounded-weight changes -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal
namespace BoltzmannNonuniqueness.Published

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}

theorem eLpNorm_comp_equiv_restrict (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    {E : Type*} [NormedAddCommGroup E] (f : Y → E) (S : Set X) :
    eLpNorm (f ∘ e) 1 (μ.restrict S) = eLpNorm f 1 (ν.restrict (e '' S)) := by
  have hm : Measure.map e (μ.restrict S) = ν.restrict (e '' S) := by
    rw [← he.map_eq,e.restrict_map,preimage_image_eq _ e.injective]
  rw [← hm]
  exact e.measurableEmbedding.eLpNorm_map_measure.symm

theorem uniformIntegrable_comp_equiv (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (f : ℕ → Y → ℝ) (hf : UniformIntegrable f 1 ν) :
    UniformIntegrable (fun n => f n ∘ e) 1 μ := by
  constructor
  · apply OAI.UnifIntegrable.of_enn
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := OAI.UnifIntegrable.enn_spec hf.1 ε hε
    refine ⟨δ,hδ,fun n S hS => ?_⟩
    rw [eLpNorm_comp_equiv_restrict e he]
    apply hd n (e '' S)
    have hm := he.measure_preimage_emb e.measurableEmbedding (e '' S)
    rw [← hm,preimage_image_eq _ e.injective]
    exact hS
    exact fun n => (hf.aestronglyMeasurable n).comp_measurePreserving he
  · obtain ⟨C,hC⟩ := hf.2
    refine ⟨C,fun n => ?_⟩
    rw [eLpNorm_comp_measurePreserving (hf.aestronglyMeasurable n) he]
    exact hC n

end BoltzmannNonuniqueness.Published

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_MassNormalizedCollisionLimits
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong mass coefficients on bounded collision windows -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem collisionMassClip_measurable (K : ℝ) {f : X × Velocity → ℝ}
    (hf : Measurable f) : Measurable (collisionMassClip K f) :=
  (massClip_measurable K (fiberMass_measurable hf)).comp measurable_fst.fst

theorem collisionMassClip_strong_on_box {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hm : Tendsto (fun n => eLpNorm (fun x => fiberMass volume (f n) x-fiberMass volume g x)
      1 μ) atTop (𝓝 0)) (K R : ℝ) :
    Tendsto (fun n => eLpNorm (fun z => collisionMassClip K (f n) z-collisionMassClip K g z)
      1 (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict
        (angularPairBox R))) atTop (𝓝 0) := by
  let B : Set (Velocity × Velocity) := Metric.closedBall 0 R ×ˢ Metric.closedBall 0 R
  let ν : Measure (Velocity × Velocity) := volume.restrict B
  have : IsFiniteMeasure ν := by
    constructor
    dsimp only [ν]
    rw [Measure.restrict_apply_univ,Measure.volume_eq_prod,Measure.prod_prod]
    exact ENNReal.mul_lt_top (isCompact_closedBall (0:Velocity) R).measure_lt_top
      (isCompact_closedBall (0:Velocity) R).measure_lt_top
  let a n x := massClip K (fiberMass volume (f n) x)-massClip K (fiberMass volume g x)
  have ham n : Measurable (a n) :=
    (massClip_measurable K (fiberMass_measurable (hfm n))).sub
      (massClip_measurable K (fiberMass_measurable hgm))
  have ha := strong_massClip (fun n => fiberMass_measurable (hfm n))
    (fiberMass_measurable hgm) K hm
  have ht := strongL1_comp_fst (ν := sphereArea)
    (fun n => (ham n).comp measurable_fst) (strongL1_comp_fst (ν := ν) ham ha)
  have he : (μ.prod ν).prod sphereArea =
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict
        (angularPairBox R) := by
    dsimp only [ν,angularPairBox,velocityPairBox,B]
    rw [← Measure.restrict_prod_eq_prod_univ,← Measure.prod_restrict,Measure.restrict_univ]
  rw [he] at ht
  exact ht

omit [MeasurableSpace X] in
theorem collisionWindow_subset_angularPairBox {R : ℝ} (hR : 0 ≤ R) :
    collisionWindow (X := X) R ⊆ angularPairBox R := by
  intro z hz
  have h := collisionWindow_bounds hR hz
  exact ⟨⟨mem_univ _,by simpa only [Set.mem_prod,Metric.mem_closedBall,dist_zero_right] using h⟩,mem_univ _⟩

theorem collisionMassClip_strong_on_window {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hm : Tendsto (fun n => eLpNorm (fun x => fiberMass volume (f n) x-fiberMass volume g x)
      1 μ) atTop (𝓝 0)) (K : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (fun z => collisionMassClip K (f n) z-collisionMassClip K g z)
      1 (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict
        (collisionWindow R))) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (collisionMassClip_strong_on_box hfm hgm hm K R) (fun _ => zero_le)
  exact fun n => eLpNorm_mono_measure _
    (Measure.restrict_mono (collisionWindow_subset_angularPairBox hR) le_rfl)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_FiniteRatesWindowUI
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Uniform integrability of actual finite rates on elastic windows -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem scatterTriple_window_measurePreserving (R : ℝ) :
    MeasurePreserving (scatterTriple (X := X))
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R))
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)) := by
  have he : scatterTriple (X := X) ⁻¹' collisionWindow R = collisionWindow R := by
    ext z
    change (‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2+
      ‖scatterRight z.1.2.1 z.1.2.2 z.2‖^2 ≤ R^2) ↔ _
    rw [scatter_energy _ _ _ (mem_sphere_zero_iff_norm.mp z.2.property)]
    rfl
  have h := (scatterTriple_measurePreserving μ).restrict_preimage (collisionWindow_measurable R)
  rwa [he] at h

theorem massRegularizedPreRate_window_uniformIntegrable
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) {R : ℝ} (hR : 0 ≤ R) :
    UniformIntegrable (fun n => massRegularizedPreRate (N n) (f n)) 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)) := by
  have hu := uniformIntegrable_restrict
    (massNormalizedPreRate_local_uniformIntegrable R hfm hf hi hb) (collisionWindow R)
  rw [Measure.restrict_restrict_of_subset (collisionWindow_subset_angularPairBox hR)] at hu
  have hm n := (massRegularizedPreRate_measurable (N n) (hfm n)).aestronglyMeasurable
    (μ := (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)))
  have he n : ∀ᵐ z ∂(((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict
      (collisionWindow R)), ‖massRegularizedPreRate (N n) (f n) z‖ₑ ≤ ‖massNormalizedPreRate (f n) z‖ₑ := by
    filter_upwards [] with z
    apply enorm_le_iff_norm_le.mpr
    rw [Real.norm_of_nonneg (massRegularizedPreRate_bounds (hN n) (hf n) z).1,Real.norm_eq_abs]
    exact (massRegularizedPreRate_bounds (hN n) (hf n) z).2.trans (le_abs_self _)
  obtain ⟨hu,B,hB⟩ := hu
  exact ⟨hu.ae_mono hm he,B,fun n => (eLpNorm_mono_enorm_ae (he n)).trans (hB n)⟩

theorem massRegularizedPostRate_window_uniformIntegrable
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) {R : ℝ} (hR : 0 ≤ R) :
    UniformIntegrable (fun n => massRegularizedPostRate (N n) (f n)) 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)) := by
  let ν := ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)
  have he : MeasurePreserving (scatterTripleEquiv (X := X)) ν ν :=
    scatterTriple_window_measurePreserving R
  have hp : UniformIntegrable (fun n => massRegularizedPreRate (N n) (f n)) 1 ν :=
    massRegularizedPreRate_window_uniformIntegrable hfm hf hi hb hN hR
  have h := Published.uniformIntegrable_comp_equiv (μ := ν) (ν := ν)
    scatterTripleEquiv he (fun n => massRegularizedPreRate (N n) (f n)) hp
  exact h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClippedProductionLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Weak convergence after restoring bounded spatial-mass factors -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem weak_clipped_collision_rates
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n p, 0 ≤ f n p) (hg : ∀ p, 0 ≤ g p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n)
    (hm : Tendsto (fun n => eLpNorm (fun x => fiberMass volume (f n) x-fiberMass volume g x)
      1 μ) atTop (𝓝 0))
    (hp : Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massRegularizedPreRate (N n) (f n)) (massNormalizedPreRate g))
    (hq : Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massRegularizedPostRate (N n) (f n)) (massNormalizedPostRate g))
    (K : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    Published.WeakL1Converges
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R))
      (fun n z => collisionMassClip K (f n) z*massRegularizedPreRate (N n) (f n) z)
      (fun z => collisionMassClip K g z*massNormalizedPreRate g z) ∧
    Published.WeakL1Converges
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R))
      (fun n z => collisionMassClip K (f n) z*massRegularizedPostRate (N n) (f n) z)
      (fun z => collisionMassClip K g z*massNormalizedPostRate g z) := by
  have hclip n z : |collisionMassClip K (f n) z| ≤ K := by
    have h := massClip_bounds K.coe_nonneg (integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hf n (z.1.1,v)))
    exact (abs_of_nonneg h.1).trans_le h.2
  have hgclip z : |collisionMassClip K g z| ≤ K := by
    have h := massClip_bounds K.coe_nonneg (integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hg (z.1.1,v)))
    exact (abs_of_nonneg h.1).trans_le h.2
  have hs := collisionMassClip_strong_on_window hfm hgm hm (K:ℝ) hR
  exact ⟨(hp.restrict (collisionWindow_measurable R)).varying_bounded_mul
      (massRegularizedPreRate_window_uniformIntegrable hfm hf hi hb hN hR)
      (fun n => massRegularizedPreRate_measurable (N n) (hfm n))
      (fun n => collisionMassClip_measurable K (hfm n)) (collisionMassClip_measurable K hgm)
      K hclip hgclip hs,
    (hq.restrict (collisionWindow_measurable R)).varying_bounded_mul
      (massRegularizedPostRate_window_uniformIntegrable hfm hf hi hb hN hR)
      (fun n => massRegularizedPostRate_measurable (N n) (hfm n))
      (fun n => collisionMassClip_measurable K (hfm n)) (collisionMassClip_measurable K hgm)
      K hclip hgclip hs⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_WindowCollisionMarginal
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Weak collision marginals and uniform integrability on a fixed elastic window -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

local instance localInst_ra92858_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
theorem windowCollisionMarginal_measurable (R : ℝ)
    {r : (X × (Velocity × Velocity)) × Sphere → ℝ} (hr : Measurable r) :
    Measurable (windowCollisionMarginal R r) :=
  ((hr.indicator (collisionWindow_measurable R)).comp
    collisionGrouping.symm.measurable).stronglyMeasurable.integral_prod_right'.measurable

theorem weak_windowCollisionMarginal {R : ℝ}
    {r : ℕ → (X × (Velocity × Velocity)) × Sphere → ℝ}
    {s : (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hr : ∀ n, Measurable (r n))
    (hu : UniformIntegrable r 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)))
    (hw : Published.WeakL1Converges
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)) r s) :
    Published.WeakL1Converges (μ.prod volume)
      (fun n => windowCollisionMarginal R (r n)) (windowCollisionMarginal R s) := by
  have hs := collisionWindow_measurable (X := X) R
  have he := hw.zeroExtension hs
  have hui := uniformIntegrable_indicator_of_restrict hs hu
  have hg := weak_grouped_rate (fun n => (hr n).indicator hs) (hw.1.indicator hs) he
  have hi n := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable
    (memLp_one_iff_integrable.mp (hui.memLp n))
  unfold windowCollisionMarginal
  simpa only [one_mul] using hg.marginal hi (k := fun _ => 1) measurable_const 1
    (fun _ => by norm_num)

theorem windowCollisionMarginal_uniformIntegrable {R : ℝ} (hR : 0 ≤ R)
    {r : ℕ → (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hr : ∀ n, Measurable (r n))
    (hu : UniformIntegrable r 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R))) :
    UniformIntegrable (fun n => windowCollisionMarginal R (r n)) 1 (μ.prod volume) := by
  let V : Set (Velocity × Sphere) := Metric.closedBall (0:Velocity) R ×ˢ univ
  have hV : MeasurableSet V := Metric.isClosed_closedBall.measurableSet.prod MeasurableSet.univ
  let : IsFiniteMeasure (((volume : Measure Velocity).prod sphereArea).restrict V) := by
    have he : (((volume : Measure Velocity).prod sphereArea).restrict V) = fiberMeasure R := by
      dsimp only [V,fiberMeasure]
      rw [← Measure.prod_restrict,Measure.restrict_univ]
    rw [he]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hs := collisionWindow_measurable (X := X) R
  have hui := uniformIntegrable_indicator_of_restrict hs hu
  have hgi := Published.uniformIntegrable_comp_equiv collisionGrouping.symm
    (collisionGrouping_measurePreserving μ).symm (fun n => (collisionWindow R).indicator (r n)) hui
  apply uniformIntegrable_integral_of_support hV
    (fun n => ((hr n).indicator hs).comp collisionGrouping.symm.measurable) hgi
  intro n p q hq
  apply indicator_of_notMem
  intro hz
  have hv : q.1 ∈ Metric.closedBall (0:Velocity) R := by
    have hb := (collisionWindow_bounds hR hz).2
    change ‖q.1‖ ≤ R at hb
    simpa only [Metric.mem_closedBall,dist_zero_right] using hb
  exact hq ⟨hv,mem_univ _⟩

end BoltzmannNonuniqueness.PeriodicApproximation

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

section

/-! # Actual collision fibers and renormalized gain/loss of the global weak density -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_2 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClippedCharacteristicGain
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Actual gain limits with bounded spatial mass and a fixed elastic window -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem clippedFiniteGain_measurable (N K R : ℝ) {f : X × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (clippedFiniteGain N K R f) :=
  windowCollisionMarginal_measurable R ((collisionMassClip_measurable K hfm).mul
    (massRegularizedPostRate_measurable N hfm))

theorem GlobalCollisionLimit.clipped_gain_limit {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (K : ℝ≥0) :
    Published.WeakL1Converges
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume)
      (fun n => clippedFiniteGain ((G.weakLimit.indices n:ℝ)+1) K R
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      (clippedPhysicalGain K R G.weakLimit.kineticProfile) ∧
    UniformIntegrable
      (fun n => clippedFiniteGain ((G.weakLimit.indices n:ℝ)+1) K R
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile) 1
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) := by
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let N (n : ℕ) : ℝ := (G.weakLimit.indices n:ℝ)+1
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  have hFm n : Measurable (F n) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hFn n p : 0 ≤ F n p :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative _
  have hN n : 0 < N n := by dsimp [N] <;> positivity
  have hFi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integrable
      (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hFb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤
      (volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f :=
    (approximatingSolution f hfm (G.weakLimit.indices n)).kinetic_entropy_integral_le
      (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hclip n z : |collisionMassClip K (F n) z| ≤ K := by
    have h := massClip_bounds K.coe_nonneg
      (integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hFn n (z.1.1,v)))
    exact (abs_of_nonneg h.1).trans_le h.2
  have hu := uniformIntegrable_of_varying_multiplier
    (massRegularizedPostRate_window_uniformIntegrable hFm hFn hFi hFb hN hR)
    (fun n => collisionMassClip_measurable K (hFm n)) K hclip
  have hw := (weak_clipped_collision_rates hFm G.weakLimit.kineticProfile_measurable
    hFn (fun _ => G.weakLimit.nonnegative _) hFi hFb hN (G.mass_strong T hT)
    (G.finite_rates T hT).1 (G.finite_rates T hT).2 K hR).2
  exact ⟨weak_windowCollisionMarginal
    (fun n => (collisionMassClip_measurable K (hFm n)).mul
      (massRegularizedPostRate_measurable (N n) (hFm n))) hu hw,
    windowCollisionMarginal_uniformIntegrable hR
      (fun n => (collisionMassClip_measurable K (hFm n)).mul
        (massRegularizedPostRate_measurable (N n) (hFm n))) hu⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual clipped gain converges along the same free characteristics -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness

theorem characteristicClippedFiniteGain_measurable (N K R : ℝ)
    {f : (ℝ × Position) × Velocity → ℝ} (hf : Measurable f) :
    Measurable (characteristicClippedFiniteGain N K R f) :=
  (clippedFiniteGain_measurable N K R hf).comp
    ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

theorem GlobalCollisionLimit.characteristic_clipped_gain_limit {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (K : ℝ≥0) (L : ℝ) :
    Published.WeakL1Converges
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))))
      (fun n => characteristicClippedFiniteGain ((G.weakLimit.indices n:ℝ)+1) K R
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      (characteristicClippedPhysicalGain K R G.weakLimit.kineticProfile) ∧
    UniformIntegrable
      (fun n => characteristicClippedFiniteGain ((G.weakLimit.indices n:ℝ)+1) K R
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile) 1
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 L)))) := by
  obtain ⟨hw,hu⟩ := G.clipped_gain_limit hf hi hT hR K
  have hm n := clippedFiniteGain_measurable ((G.weakLimit.indices n:ℝ)+1) (K:ℝ) R
    (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable
  have hwl := hw.restrict (s := (univ : Set (ℝ × Position)) ×ˢ Metric.closedBall (0:Velocity) L)
    (MeasurableSet.univ.prod Metric.isClosed_closedBall.measurableSet)
  have hul := uniformIntegrable_restrict hu
    ((univ : Set (ℝ × Position)) ×ˢ Metric.closedBall (0:Velocity) L)
  rw [← Measure.prod_restrict,Measure.restrict_univ] at hwl hul
  exact ⟨TorusFlight.weak_along_regroup_local hm hwl,
    TorusFlight.uniformIntegrable_along_regroup_local hm hul⟩

end BoltzmannNonuniqueness.PeriodicApproximation

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

/-! # Local strong convergence of the actual physical loss frequencies -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.frequency_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm (fun p =>
      kineticFrequency (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile p-
      kineticFrequency G.weakLimit.kineticProfile p)
      1 (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))) atTop (𝓝 0) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let τ : Measure Velocity := volume.restrict (Metric.closedBall 0 R)
  let : IsFiniteMeasure τ := isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) R).measure_lt_top.ne
  let k : Velocity × Velocity → ℝ := fun p => min ‖p.1-p.2‖ (R+‖p.2‖)
  have hk : Measurable k := by dsimp only [k]; fun_prop
  have hb p : |k p| ≤ (R+1)*(1+‖p.2‖) := by
    rw [abs_of_nonneg (le_min (norm_nonneg _) (by positivity))]
    exact (min_le_right _ _).trans (by nlinarith [norm_nonneg p.2])
  have hs := G.linear_kernel_strong hf hi hT τ hk ⟨R+1,by positivity⟩ hb
  have hscaled := ENNReal.Tendsto.const_mul (a := ‖(2*Real.pi:ℝ)‖ₑ) hs
    (Or.inr (by rw [enorm_mul]; exact ENNReal.mul_ne_top (by simp) (by simp)))
  simp only [← eLpNorm_const_smul,Pi.smul_def,smul_eq_mul,mul_zero] at hscaled
  apply hscaled.congr'
  apply Eventually.of_forall
  intro n
  apply eLpNorm_congr_ae
  have hva : ∀ᵐ p ∂μ.prod τ, ‖p.2‖ ≤ R := by
    have hmem : ∀ᵐ v ∂τ, v ∈ Metric.closedBall (0:Velocity) R :=
      ae_restrict_mem Metric.isClosed_closedBall.measurableSet
    have h := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := τ)).ae hmem
    simpa only [Metric.mem_closedBall,dist_zero_right] using h
  filter_upwards [hva] with p hp
  have he (u : (ℝ × Position) × Velocity → ℝ) :
      (∫ v, k (p.2,v)*u (p.1,v)) = ∫ v, ‖p.2-v‖*u (p.1,v) := by
    apply integral_congr_ae
    apply ae_of_all
    intro v
    dsimp only [k]
    rw [min_eq_left ((norm_sub_le _ _).trans (add_le_add hp le_rfl))]
  simp only [he,kineticFrequency]
  ring

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

theorem GlobalCollisionLimit.characteristic_frequency_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm
      (physicalCharacteristicFrequency (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile-
        physicalCharacteristicFrequency G.weakLimit.kineticProfile)
      1 ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))))) atTop (𝓝 0) :=
  TorusFlight.strong_along_regroup
    (fun n => kineticFrequency_measurable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    (kineticFrequency_measurable G.weakLimit.kineticProfile_measurable)
    (G.frequency_strong hf hi hT hR)

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

/-! # Both endpoints of the actual physical survival factors converge -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.two_time_survival_strong {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    Tendsto (fun n => eLpNorm
      (Published.twoTimeSurvival (volume.restrict (Icc 0 T))
        (physicalCharacteristicFrequency (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)-
      Published.twoTimeSurvival (volume.restrict (Icc 0 T))
        (physicalCharacteristicFrequency G.weakLimit.kineticProfile))
      1 (((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 R)))).prod
          (volume.restrict (Icc 0 T)))) atTop (𝓝 0) := by
  obtain ⟨hFi,hgi⟩ := G.characteristic_frequency_integrable hf hi hT hR
  exact Published.strong_twoTimeSurvival
    (fun n => physicalCharacteristicFrequency_measurable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    (physicalCharacteristicFrequency_measurable G.weakLimit.kineticProfile_measurable)
    hFi hgi (G.characteristic_frequency_strong hf hi hT hR)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Approximation_PositiveContributionsIntegrable
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # The actual positive gain integrals converge with their physical survival factors -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.positive_source_limit_q80_oai {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R L : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (hL : 0 ≤ L) (K : ℝ≥0) :
    Published.WeakL1Converges
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))))
      (fun n => finitePositiveSource T ((G.weakLimit.indices n:ℝ)+1) K R
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      (physicalPositiveSource T K R G.weakLimit.kineticProfile) := by
  let : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 L)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) L).measure_lt_top.ne
  obtain ⟨hw,hu⟩ := G.characteristic_clipped_gain_limit hf hi hT hR K L
  apply hw.survivalVolterra hu
    (fun n => characteristicClippedFiniteGain_measurable ((G.weakLimit.indices n:ℝ)+1) (K:ℝ) R
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    (fun n => Published.twoTimeSurvival_measurable (physicalCharacteristicFrequency_measurable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable))
    (Published.twoTimeSurvival_measurable (physicalCharacteristicFrequency_measurable
      G.weakLimit.kineticProfile_measurable)) 1
  · intro n z
    have h := Published.twoTimeSurvival_bounds (volume.restrict (Icc 0 T))
      (physicalCharacteristicFrequency (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile) z
    exact (abs_of_pos h.1).trans_le h.2
  · intro z
    have h := Published.twoTimeSurvival_bounds (volume.restrict (Icc 0 T))
      (physicalCharacteristicFrequency G.weakLimit.kineticProfile) z
    exact (abs_of_pos h.1).trans_le h.2
  · exact G.two_time_survival_strong hf hi hT hL

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_source_limit_q80_oai := @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.positive_source_limit_q80_oai
