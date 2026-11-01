-- Prove2me | solution 1 for OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_entropy_dissipation_q80
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:19:32.002704+00:00
-- url     : https://prove2.me/submissions/23752741-a708-496e-83d2-bad0b19cccd8

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

end BoltzmannNonuniqueness.Compactness

end

end OAI
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

/-!
# Lower semicontinuity of entropy production

The extended scalar entropy production is lower semicontinuous along positive
approximations of nonnegative products. In particular its value is infinite
when exactly one limiting product vanishes. Weighted Fatou then passes this
production to a limit, without a domination hypothesis or a finite-production
assumption. The final specialization applies to positive regularizations of
four nonnegative factors.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem extendedEntropyProduction_symm (a b : ℝ) :
    extendedEntropyProduction a b = extendedEntropyProduction b a := by
  by_cases hz : a = 0 ∧ b = 0
  · simp [extendedEntropyProduction, hz.1, hz.2]
  have hz' : ¬ (b = 0 ∧ a = 0) := fun h => hz ⟨h.2, h.1⟩
  by_cases hp : 0 < a ∧ 0 < b
  · have hp' : 0 < b ∧ 0 < a := ⟨hp.2, hp.1⟩
    simp only [extendedEntropyProduction, ite_eq_right hz, ite_eq_right hz',
      ite_eq_left hp, ite_eq_left hp']
    congr 1
    rw [Real.log_div hp.1.ne' hp.2.ne', Real.log_div hp.2.ne' hp.1.ne']
    ring
  · have hp' : ¬ (0 < b ∧ 0 < a) := fun h => hp ⟨h.2, h.1⟩
    simp only [extendedEntropyProduction, ite_eq_right hz, ite_eq_right hz',
      ite_eq_right hp, ite_eq_right hp']

theorem measurable_extendedEntropyProduction {X : Type*} [MeasurableSpace X]
    {a b : X → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => extendedEntropyProduction (a x) (b x)) := by
  unfold extendedEntropyProduction
  apply Measurable.ite
    ((measurableSet_eq_fun ha measurable_const).inter
      (measurableSet_eq_fun hb measurable_const)) measurable_const
  exact Measurable.ite
    ((measurableSet_lt measurable_const ha).inter (measurableSet_lt measurable_const hb))
    ((ha.sub hb).mul ((ha.div hb).log)).ennreal_ofReal measurable_const

private theorem production_eventually_eq {ι : Type*} {l : Filter ι}
    {a b : ι → ℝ} (ha : ∀ᶠ i in l, 0 < a i) (hb : ∀ᶠ i in l, 0 < b i) :
    (fun i => extendedEntropyProduction (a i) (b i)) =ᶠ[l]
      (fun i => ENNReal.ofReal ((a i - b i) * Real.log (a i / b i))) := by
  filter_upwards [ha, hb] with i hai hbi
  simp [extendedEntropyProduction, hai, hbi, hai.ne', hbi.ne']

theorem tendsto_extendedEntropyProduction_positive {ι : Type*} {l : Filter ι}
    {a b : ι → ℝ} {A B : ℝ}
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
    (hA : 0 < A) (hB : 0 < B)
    (hap : ∀ᶠ i in l, 0 < a i) (hbp : ∀ᶠ i in l, 0 < b i) :
    Tendsto (fun i => extendedEntropyProduction (a i) (b i)) l
      (𝓝 (extendedEntropyProduction A B)) := by
  have ht := ENNReal.tendsto_ofReal ((ha.sub hb).mul
    ((ha.div hb hB.ne').log (div_pos hA hB).ne'))
  have he : extendedEntropyProduction A B =
      ENNReal.ofReal ((A - B) * Real.log (A / B)) := by
    simp [extendedEntropyProduction, hA, hB, hA.ne', hB.ne']
  rw [he]
  exact ht.congr' (production_eventually_eq hap hbp).symm

/-- A zero product against a positive product has infinite limiting production. -/
theorem tendsto_extendedEntropyProduction_zero_left {ι : Type*} {l : Filter ι}
    {a b : ι → ℝ} {B : ℝ}
    (ha : Tendsto a l (𝓝 0)) (hb : Tendsto b l (𝓝 B)) (hB : 0 < B)
    (hap : ∀ᶠ i in l, 0 < a i) (hbp : ∀ᶠ i in l, 0 < b i) :
    Tendsto (fun i => extendedEntropyProduction (a i) (b i)) l (𝓝 ∞) := by
  have hr : Tendsto (fun i => a i / b i) l (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_div, Pi.div_def] using ha.div hb hB.ne'
    · filter_upwards [hap, hbp] with i hai hbi
      exact div_pos hai hbi
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hr
  have hdiff : Tendsto (fun i => a i - b i) l (𝓝 (-B)) := by
    simpa only [zero_sub] using ha.sub hb
  have hprod := hdiff.neg_mul_atBot (neg_lt_zero.mpr hB) hlog
  have ht := ENNReal.tendsto_ofReal_atTop.comp hprod
  exact ht.congr' (production_eventually_eq hap hbp).symm

theorem tendsto_extendedEntropyProduction_zero_right {ι : Type*} {l : Filter ι}
    {a b : ι → ℝ} {A : ℝ}
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 0)) (hA : 0 < A)
    (hap : ∀ᶠ i in l, 0 < a i) (hbp : ∀ᶠ i in l, 0 < b i) :
    Tendsto (fun i => extendedEntropyProduction (a i) (b i)) l (𝓝 ∞) := by
  simpa only [extendedEntropyProduction_symm] using
    tendsto_extendedEntropyProduction_zero_left hb ha hA hbp hap

theorem extendedEntropyProduction_le_liminf {ι : Type*} {l : Filter ι} [NeBot l]
    {a b : ι → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
    (hap : ∀ᶠ i in l, 0 < a i) (hbp : ∀ᶠ i in l, 0 < b i) :
    extendedEntropyProduction A B ≤
      liminf (fun i => extendedEntropyProduction (a i) (b i)) l := by
  by_cases hAz : A = 0
  · subst A
    by_cases hBz : B = 0
    · simp only [hBz, extendedEntropyProduction, and_self, ite_true, if_true]
      exact bot_le
    · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
      rw [(tendsto_extendedEntropyProduction_zero_left ha hb hBp hap hbp).liminf_eq]
      exact le_top
  · have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
    by_cases hBz : B = 0
    · subst B
      rw [(tendsto_extendedEntropyProduction_zero_right ha hb hAp hap hbp).liminf_eq]
      exact le_top
    · have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
      rw [(tendsto_extendedEntropyProduction_positive ha hb hAp hBp hap hbp).liminf_eq]

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

/-! # Weighted Fatou for entropy production with convergent kernel multipliers -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness

theorem lintegral_varying_production_le_liminf
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter ι}
    [NeBot l] [IsCountablyGenerated l]
    {a b : ι → X → ℝ} {A B : X → ℝ} {w : ι → X → ℝ≥0∞} {W : X → ℝ≥0∞}
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i)) (hw : ∀ i, Measurable (w i))
    (hA : ∀ᵐ x ∂μ, 0 ≤ A x) (hB : ∀ᵐ x ∂μ, 0 ≤ B x)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun i => a i x) l (𝓝 (A x)) ∧
      Tendsto (fun i => b i x) l (𝓝 (B x)))
    (hwconv : ∀ᵐ x ∂μ, Tendsto (fun i => w i x) l (𝓝 (W x)))
    (hpos : ∀ᵐ x ∂μ, (∀ᶠ i in l, 0 < a i x) ∧ (∀ᶠ i in l, 0 < b i x)) :
    (∫⁻ x, W x*extendedEntropyProduction (A x) (B x) ∂μ) ≤
      liminf (fun i => ∫⁻ x, w i x*extendedEntropyProduction (a i x) (b i x) ∂μ) l := by
  calc
    _ ≤ ∫⁻ x, liminf (fun i => w i x*extendedEntropyProduction (a i x) (b i x)) l ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hA,hB,hconv,hwconv,hpos] with x hAx hBx hx hwx hpx
      have hs := extendedEntropyProduction_le_liminf hAx hBx hx.1 hx.2 hpx.1 hpx.2
      have hm := ENNReal.le_liminf_mul (u := fun i => w i x)
        (v := fun i => extendedEntropyProduction (a i x) (b i x)) (f := l)
      rw [hwx.liminf_eq] at hm
      exact (mul_le_mul_right hs (W x)).trans hm
    _ ≤ _ := lintegral_liminf_le (fun i => (hw i).mul (measurable_extendedEntropyProduction (ha i) (hb i)))

end BoltzmannNonuniqueness

end

end

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

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Integrable physical gain and loss and their equal total mass -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_r79f3d9_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
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

/-! # Full collision terms are independent of the density representative -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea_7_r79f3d9_1 : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
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

theorem massNormalizedPreRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (massNormalizedPreRate f) := by
  rw [massNormalizedPreRate_eq_fun]
  exact normalizedKernel_measurable.mul ((weightedNormalizedPair_measurable hfm).comp measurable_fst)

theorem massNormalizedPostRate_measurable {f : X × Velocity → ℝ} (hfm : Measurable f) :
    Measurable (massNormalizedPostRate f) :=
  (massNormalizedPreRate_measurable hfm).comp scatterTriple_measurable

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

section

/-! # Passing the sum of nonnegative entropy and dissipation to a subsequential limit -/

noncomputable section

open Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem ennreal_liminf_add_nat (u v : ℕ → ℝ≥0∞) :
    liminf u atTop+liminf v atTop ≤ liminf (fun n => u n+v n) atTop := by
  simp_rw [liminf_eq_iSup_iInf_of_nat]
  apply ENNReal.iSup_add_iSup_le
  intro N M
  apply le_iSup_of_le (max N M)
  apply le_iInf₂
  intro k hk
  exact add_le_add (iInf₂_le k ((le_max_left N M).trans hk))
    (iInf₂_le k ((le_max_right N M).trans hk))

end BoltzmannNonuniqueness

end

end

section

/-! # Retaining a common entropy and dissipation budget under time averaging -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem entropy_dissipation_average_limit {H : ℕ → X → ℝ≥0∞} {h : X → ℝ≥0∞}
    {D C : ℕ → ℝ≥0∞} {d c : ℝ≥0∞}
    (hHm : ∀ n, Measurable (H n))
    (hh : (∫⁻ x, h x ∂μ) ≤ liminf (fun n => ∫⁻ x, H n x ∂μ) atTop)
    (hd : d ≤ liminf D atTop) (hC : Tendsto C atTop (𝓝 c))
    (hu : ∀ᶠ n in atTop, ∀ᵐ x ∂μ, H n x+D n ≤ C n) :
    (∫⁻ x, h x ∂μ)+μ Set.univ*d ≤ μ Set.univ*c := by
  have hm := ENNReal.le_liminf_mul (u := fun _ : ℕ => μ Set.univ) (v := D) (f := atTop)
  have hd' : μ Set.univ*d ≤ liminf (fun n => μ Set.univ*D n) atTop := by
    apply (mul_le_mul' le_rfl hd).trans
    simpa only [liminf_const,Pi.mul_def] using hm
  have hu' : ∀ᶠ n in atTop, (∫⁻ x, H n x ∂μ)+μ Set.univ*D n ≤ μ Set.univ*C n := by
    filter_upwards [hu] with n hn
    have h := lintegral_mono_ae hn
    rw [lintegral_add_left (hHm n),lintegral_const,lintegral_const] at h
    simpa only [mul_comm] using h
  have hlim : Tendsto (fun n => μ Set.univ*C n) atTop (𝓝 (μ Set.univ*c)) :=
    ENNReal.Tendsto.const_mul hC (Or.inr (measure_ne_top μ Set.univ))
  apply (add_le_add hh hd').trans
  apply (ennreal_liminf_add_nat _ _).trans
  have hb := liminf_le_liminf hu'
  rwa [hlim.liminf_eq] at hb

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ProductionDualLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded linear tests for the extended entropy production -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem productionDual_linear (a b s : ℝ) :
    productionDual a b s = a*(s-Real.exp (-s)+1)+b*(-s-Real.exp s+1) := by
  dsimp [productionDual,entropyDual]
  ring

theorem productionDual_ofReal_le (a b s : ℝ) :
    ENNReal.ofReal (productionDual a b s) ≤ extendedEntropyProduction a b := by
  by_cases hz : a = 0 ∧ b = 0
  · rcases hz with ⟨rfl,rfl⟩
    simp [productionDual,entropyDual,extendedEntropyProduction]
  by_cases hp : 0 < a ∧ 0 < b
  · have h₁ := entropyDual_le hp.2 hp.1.le s
    have h₂ := entropyDual_le hp.1 hp.2.le (-s)
    have he : scalarRelativeEntropy b a+scalarRelativeEntropy a b =
        (a-b)*Real.log (a/b) := by
      rw [scalarRelativeEntropy_eq hp.2,scalarRelativeEntropy_eq hp.1,
        Real.log_div hp.1.ne' hp.2.ne',Real.log_div hp.2.ne' hp.1.ne']
      ring
    simp only [extendedEntropyProduction,ite_eq_right hz,ite_eq_left hp]
    exact ENNReal.ofReal_le_ofReal (by unfold productionDual; linarith only [h₁,h₂,he])
  · simp only [extendedEntropyProduction,ite_eq_right hz,ite_eq_right hp]
    exact le_top

theorem productionDual_log_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    productionDual a b (Real.log (a/b)) = (a-b)*Real.log (a/b) := by
  have hlog : -Real.log (a/b) = Real.log (b/a) := by
    rw [Real.log_div ha.ne' hb.ne',Real.log_div hb.ne' ha.ne']
    ring
  rw [productionDual,hlog,entropyDual_log_ratio hb ha,entropyDual_log_ratio ha hb,
    scalarRelativeEntropy_eq hb,scalarRelativeEntropy_eq ha,
    Real.log_div ha.ne' hb.ne',Real.log_div hb.ne' ha.ne']
  ring

theorem rawProductionTest_bound (n : ℕ) (a b : ℝ) :
    |rawProductionTest n a b| ≤ n := by
  unfold rawProductionTest
  split_ifs with ha hb hlog <;> simp_all

theorem boundedProductionTest_bound (n : ℕ) (a b : ℝ) :
    |boundedProductionTest n a b| ≤ n := by
  unfold boundedProductionTest
  split_ifs
  · exact rawProductionTest_bound n a b
  · simp

theorem productionDual_boundedTest_nonneg (n : ℕ) (a b : ℝ) :
    0 ≤ productionDual a b (boundedProductionTest n a b) := by
  unfold boundedProductionTest
  split_ifs with h
  · exact h
  · simp [productionDual,entropyDual]

theorem ofReal_productionDual_boundedTest (n : ℕ) (a b : ℝ) :
    ENNReal.ofReal (productionDual a b (boundedProductionTest n a b)) =
      ENNReal.ofReal (productionDual a b (rawProductionTest n a b)) := by
  unfold boundedProductionTest
  split_ifs with h
  · rfl
  · have hz : productionDual a b 0 = 0 := by simp [productionDual,entropyDual]
    rw [hz,ENNReal.ofReal_zero]
    exact (ENNReal.ofReal_eq_zero.mpr (le_of_not_ge h)).symm

theorem productionDual_coefficient_bound {s C : ℝ} (hC : |s| ≤ C) :
    |s-Real.exp (-s)+1| ≤ C+Real.exp C+1 := by
  have he : Real.exp (-s) ≤ Real.exp C :=
    Real.exp_le_exp.mpr ((neg_le_abs s).trans hC)
  calc
    _ ≤ |s-Real.exp (-s)|+|1| := abs_add_le _ _
    _ ≤ (|s|+|Real.exp (-s)|)+1 := by
      rw [abs_one]
      exact add_le_add (abs_sub _ _) le_rfl
    _ ≤ C+Real.exp C+1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact add_le_add (add_le_add hC he) le_rfl

variable {X : Type*} [MeasurableSpace X]

theorem measurable_productionDual {a b s : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) (hs : Measurable s) :
    Measurable (fun x => productionDual (a x) (b x) (s x)) :=
  (measurable_entropyDual hb ha hs).add (measurable_entropyDual ha hb hs.neg)

theorem measurable_rawProductionTest (n : ℕ) {a b : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => rawProductionTest n (a x) (b x)) := by
  have hlog := (ha.div hb).log
  exact Measurable.ite (measurableSet_eq_fun ha measurable_const) measurable_const
    (Measurable.ite (measurableSet_eq_fun hb measurable_const) measurable_const
      (Measurable.ite (measurableSet_le hlog.abs measurable_const) hlog measurable_const))

theorem measurable_boundedProductionTest (n : ℕ) {a b : X → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun x => boundedProductionTest n (a x) (b x)) := by
  have hs := measurable_rawProductionTest n ha hb
  exact Measurable.ite (measurableSet_le measurable_const (measurable_productionDual ha hb hs))
    hs measurable_const

theorem integrable_productionDual {μ : Measure X} {a b s : X → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hs : Measurable s)
    {C : ℝ} (hC : ∀ x, |s x| ≤ C) :
    Integrable (fun x => productionDual (a x) (b x) (s x)) μ := by
  have hi := (integrable_entropyDual hb ha hs hC).add
    (integrable_entropyDual ha hb hs.neg (fun x => by simpa using hC x))
  simpa only [productionDual,Pi.add_def,Pi.neg_def] using hi

end BoltzmannNonuniqueness

end

end

section

/-! # Bounded linear tests recover infinite production at one-sided zeros -/

noncomputable section

open Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness

theorem ofReal_productionDual_rawTest_tendsto {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun n => ENNReal.ofReal (productionDual a b (rawProductionTest n a b))) atTop
      (𝓝 (extendedEntropyProduction a b)) := by
  by_cases haz : a = 0
  · subst a
    by_cases hbz : b = 0
    · subst b
      simp [rawProductionTest,productionDual,entropyDual,extendedEntropyProduction]
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
      have ht : Tendsto (fun n => productionDual 0 b (rawProductionTest n 0 b)) atTop atTop := by
        apply tendsto_atTop_mono _ (Tendsto.const_mul_atTop hbp tendsto_natCast_atTop_atTop)
        intro n
        have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
          (neg_nonpos.mpr (Nat.cast_nonneg n))
        dsimp [rawProductionTest,productionDual,entropyDual]
        simp only [ite_true, if_true,zero_mul,sub_zero,zero_sub,neg_neg]
        nlinarith
      rw [show extendedEntropyProduction 0 b = ∞ by simp [extendedEntropyProduction,hbz]]
      exact ENNReal.tendsto_ofReal_atTop.comp ht
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    by_cases hbz : b = 0
    · subst b
      have ht : Tendsto (fun n => productionDual a 0 (rawProductionTest n a 0)) atTop atTop := by
        apply tendsto_atTop_mono _ (Tendsto.const_mul_atTop hap tendsto_natCast_atTop_atTop)
        intro n
        have he : Real.exp (-(n:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
          (neg_nonpos.mpr (Nat.cast_nonneg n))
        simp only [rawProductionTest,haz,↓reduceIte,productionDual,entropyDual,zero_mul,sub_zero]
        nlinarith
      rw [show extendedEntropyProduction a 0 = ∞ by simp [extendedEntropyProduction,haz]]
      exact ENNReal.tendsto_ofReal_atTop.comp ht
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (Nat.ceil |Real.log (a/b)|)] with n hn
      have hlog : |Real.log (a/b)| ≤ (n:ℝ) :=
        (Nat.le_ceil _).trans (by exact_mod_cast hn)
      simp [rawProductionTest,haz,hbz,hlog,productionDual_log_ratio hap hbp,
        extendedEntropyProduction,hap,hbp]

theorem ofReal_productionDual_boundedTest_tendsto {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto (fun n => ENNReal.ofReal (productionDual a b (boundedProductionTest n a b))) atTop
      (𝓝 (extendedEntropyProduction a b)) := by
  simpa only [ofReal_productionDual_boundedTest] using ofReal_productionDual_rawTest_tendsto ha hb

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

section

/-! # Extended entropy production is lower semicontinuous under weak L¹ convergence -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem productionDual_integral_tendsto {a b : ℕ → X → ℝ} {A B s : X → ℝ}
    (hA : WeakL1Converges μ a A) (hB : WeakL1Converges μ b B)
    (ha : ∀ n, Integrable (a n) μ) (hb : ∀ n, Integrable (b n) μ)
    (hs : Measurable s) {C : ℝ} (hC : ∀ x, |s x| ≤ C) :
    Tendsto (fun n => ∫ x, productionDual (a n x) (b n x) (s x) ∂μ) atTop
      (𝓝 (∫ x, productionDual (A x) (B x) (s x) ∂μ)) := by
  let u := fun x => s x-Real.exp (-s x)+1
  let v := fun x => -s x-Real.exp (s x)+1
  have hum : Measurable u := (hs.sub hs.neg.exp).add measurable_const
  have hvm : Measurable v := (hs.neg.sub hs.exp).add measurable_const
  have hub x : |u x| ≤ C+Real.exp C+1 := productionDual_coefficient_bound (hC x)
  have hvb x : |v x| ≤ C+Real.exp C+1 := by
    simpa only [neg_neg] using productionDual_coefficient_bound
      (show |-s x| ≤ C by simpa using hC x)
  have he (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ) :
      (∫ x, productionDual (f x) (g x) (s x) ∂μ) =
        (∫ x, u x*f x ∂μ)+(∫ x, v x*g x ∂μ) := by
    simp_rw [productionDual_linear]
    simpa only [u,v,mul_comm] using integral_add
      (hf.bdd_mul hum.aestronglyMeasurable (ae_of_all μ hub))
      (hg.bdd_mul hvm.aestronglyMeasurable (ae_of_all μ hvb))
  simp only [he _ _ (ha _) (hb _),he _ _ hA.2.1 hB.2.1]
  exact (hA.2.2 u hum ⟨_,hub⟩).add (hB.2.2 v hvm ⟨_,hvb⟩)

theorem ofReal_integral_le_lintegral {f : X → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  exact ENNReal.ofReal_le_of_le_toReal (sub_le_self _ ENNReal.toReal_nonneg)

theorem weak_production_liminf {a b : ℕ → X → ℝ} {A B : X → ℝ}
    (hA : WeakL1Converges μ a A) (hB : WeakL1Converges μ b B)
    (ha : ∀ n, Integrable (a n) μ) (hb : ∀ n, Integrable (b n) μ)
    (hAn : 0 ≤ᵐ[μ] A) (hBn : 0 ≤ᵐ[μ] B) :
    (∫⁻ x, extendedEntropyProduction (A x) (B x) ∂μ) ≤
      liminf (fun n => ∫⁻ x, extendedEntropyProduction (a n x) (b n x) ∂μ) atTop := by
  let s : ℕ → X → ℝ := fun n x => boundedProductionTest n (A x) (B x)
  let d : ℕ → X → ℝ := fun n x => productionDual (A x) (B x) (s n x)
  have hsm n : Measurable (s n) := measurable_boundedProductionTest n hA.1 hB.1
  have hsb n x : |s n x| ≤ (n:ℝ) := boundedProductionTest_bound n (A x) (B x)
  have hdi n : Integrable (d n) μ := integrable_productionDual hA.2.1 hB.2.1 (hsm n) (hsb n)
  have hdm n : Measurable (d n) := measurable_productionDual hA.1 hB.1 (hsm n)
  have hdn n : 0 ≤ᵐ[μ] d n := ae_of_all μ (fun x => productionDual_boundedTest_nonneg n _ _)
  have hlim n : ENNReal.ofReal (∫ x, d n x ∂μ) ≤
      liminf (fun k => ∫⁻ x, extendedEntropyProduction (a k x) (b k x) ∂μ) atTop := by
    have ht := ENNReal.tendsto_ofReal (productionDual_integral_tendsto hA hB ha hb (hsm n) (hsb n))
    rw [← ht.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall (fun k =>
      (ofReal_integral_le_lintegral (integrable_productionDual (ha k) (hb k) (hsm n) (hsb n))).trans
        (lintegral_mono (fun x => productionDual_ofReal_le _ _ _))))
  have hfatou : (∫⁻ x, extendedEntropyProduction (A x) (B x) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (d n x) ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (d n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hAn,hBn] with x hax hbx
        exact (ofReal_productionDual_boundedTest_tendsto hax hbx).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le (fun n => (hdm n).ennreal_ofReal)
  apply hfatou.trans
  exact liminf_le_of_frequently_le ((Eventually.of_forall (fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hdi n) (hdn n)]
    exact hlim n)).frequently)

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

omit [MeasurableSpace X] in
theorem rateMultiplier_tendsto {ι : Type*} {l : Filter ι} {N : ℝ} (hN : 0 < N)
    {F : ι → X × Velocity → ℝ} {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (hF : ∀ p, Tendsto (fun i => F i p) l (𝓝 (f p)))
    (z : (X × (Velocity × Velocity)) × Sphere) :
    Tendsto (fun i => rateMultiplier N (F i) z) l (𝓝 (rateMultiplier N f z)) := by
  have hs := (((hF (z.1.1,z.1.2.1)).add (hF (z.1.1,z.1.2.2))).add
    (hF (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))).add
    (hF (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  have hn : N+rateSum (f (z.1.1,z.1.2.1)) (f (z.1.1,z.1.2.2))
      (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
      (f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)) ≠ 0 :=
    (add_pos_of_pos_of_nonneg hN (rateSum_nonneg (hf _) (hf _) (hf _) (hf _))).ne'
  exact tendsto_const_nhds.div ((tendsto_const_nhds.add hs).pow 2) (pow_ne_zero 2 hn)

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

/-! # Retaining the nonnegative dissipation in the approximate entropy identity -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem positiveProduction_nonneg (N : ℝ) (f : X × Velocity → ℝ)
    (hf : ∀ p, 0 < f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ positiveProduction N f z := by
  simpa only [positiveProduction,mul_assoc] using
    mul_nonneg (by norm_num : (0:ℝ) ≤ 1/4) (regularized_relative_production_nonneg N f hf z)

theorem positiveProduction_identity {μ : Measure X} [IsFiniteMeasure μ]
    {N C : ℝ} (hN : 0 < N) {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hf : ∀ p, 0 < f p)
    (hlog : ∀ p, ‖p.2‖ ≤ N → |Real.log (f p/maxwellian p.2)| ≤ C) :
    Integrable (positiveProduction N f) ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ∧
    (∫ p, Real.log (f p/maxwellian p.2)*collisionOperator N f p ∂μ.prod volume) =
      -(∫ z, positiveProduction N f z ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have hm : Measurable (fun p : X × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hψ := (hfm.div hm).log
  have hpre := regularizedPreRate_test_integrable (μ := μ) hN hfm (fun p => (hf p).le) hψ hlog
  have hpost := regularizedPostRate_test_integrable (μ := μ) hN hfm (fun p => (hf p).le) hψ hlog
  obtain ⟨hjpre,hjpost⟩ := collisionJump_integrable N f (fun p => Real.log (f p/maxwellian p.2)) hpre hpost
  obtain ⟨hg,hl,hgEq,hlEq⟩ := regularized_test_marginals (μ := μ) hN hfm (fun p => (hf p).le) hψ hlog
  simp only [Pi.div_apply] at hg hl hgEq hlEq
  constructor
  · convert (hjpost.sub hjpre).const_mul (1/4:ℝ) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    simp only [positiveProduction,Pi.sub_apply]
    ring
  · simp_rw [collisionOperator,mul_sub]
    rw [integral_sub hg hl,hgEq,hlEq,
      regularized_production_identity N f (fun p => Real.log (f p/maxwellian p.2)) hpre hpost]
    simp only [positiveProduction,mul_assoc,integral_const_mul]
    ring

theorem gaussian_entropy_dissipation_bound {μ : Measure X} [IsFiniteMeasure μ]
    {N B δ : ℝ} (hN : 0 < N) (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hfb : ∀ p, f p ≤ B) :
    (∫ p, Real.log (gaussianShift δ f p/maxwellian p.2)*collisionOperator N f p ∂μ.prod volume)+
      (∫ z, positiveProduction N (gaussianShift δ f) z
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
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
  have hid := (positiveProduction_identity (μ := μ) hN hgm hgp hψ).2
  have he := entropy_error_integral (μ := μ) hN hB hδ hδ1 hfm hf hfb
  have heq : (fun p => ψ p*(collisionOperator N f p-collisionOperator N g p)) =
      (fun p => ψ p*collisionOperator N f p)-(fun p => ψ p*collisionOperator N g p) := by
    funext p
    simp only [Pi.sub_apply,mul_sub]
  change |∫ p, ψ p*(collisionOperator N f p-collisionOperator N g p) ∂μ.prod volume| ≤ _ at he
  rw [heq,integral_sub' hif hig,hid] at he
  simp only [sub_neg_eq_add] at he
  exact (le_abs_self _).trans he

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The extended dissipation of the actual symmetric regularization -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem positiveProduction_formula (N : ℝ) (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    positiveProduction N f z = (1/4:ℝ)*(windowKernel N z*rateMultiplier N f z)*
      ((f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)-
        f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))*
        Real.log ((f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))/
          (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)))) := by
  unfold positiveProduction
  rw [collisionJump_log_relative f hf,collisionJump_log_density f hf,
    regularizedPostRate_factor,regularizedPreRate_factor]
  ring

omit [MeasurableSpace X] in
theorem ofReal_positiveProduction {N : ℝ} (hN : 0 ≤ N) (f : X × Velocity → ℝ)
    (hf : ∀ p, 0 < f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    ENNReal.ofReal (positiveProduction N f z) = (4:ℝ≥0∞)⁻¹*extendedProduction N f z := by
  have hA := mul_pos (hf (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2))
    (hf (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
  have hB := mul_pos (hf (z.1.1,z.1.2.1)) (hf (z.1.1,z.1.2.2))
  have hw : 0 ≤ windowKernel N z*rateMultiplier N f z :=
    mul_nonneg (windowKernel_bounds hN z).1 (attenuation_nonneg _ _)
  rw [positiveProduction_formula N f hf]
  unfold extendedProduction
  simp only [extendedEntropyProduction,hA,hB,hA.ne',hB.ne',and_self,ite_true, if_true,ite_false, if_false]
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hw),ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 4)]
  norm_num [mul_assoc]

theorem ofReal_integral_positiveProduction {μ : Measure X} {N : ℝ} (hN : 0 ≤ N)
    (f : X × Velocity → ℝ) (hf : ∀ p, 0 < f p)
    (hi : Integrable (positiveProduction N f)
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    ENNReal.ofReal (∫ z, positiveProduction N f z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) = extendedDissipation μ N f := by
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (positiveProduction_nonneg N f hf))]
  simp_rw [ofReal_positiveProduction hN f hf]
  exact lintegral_const_mul' _ _ (by norm_num)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Gaussian removal for the extended regularized collision dissipation -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem gaussianShift_tendsto (f : X × Velocity → ℝ) (p : X × Velocity) :
    Tendsto (fun δ : ℝ => gaussianShift δ f p) (𝓝[>] 0) (𝓝 (f p)) := by
  have hc : Continuous (fun δ : ℝ => f p+δ*maxwellian p.2) :=
    continuous_const.add (continuous_id.mul_const _)
  simpa only [gaussianShift,zero_mul,add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem extendedDissipation_gaussian_le_liminf (μ : Measure X) {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    extendedDissipation μ N f ≤
      liminf (fun δ : ℝ => extendedDissipation μ N (gaussianShift δ f)) (𝓝[>] 0) := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let A := fun z : (X × (Velocity × Velocity)) × Sphere =>
    f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)
  let B := fun z : (X × (Velocity × Velocity)) × Sphere => f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)
  let a := fun (δ : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) =>
    gaussianShift δ f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
      gaussianShift δ f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2)
  let b := fun (δ : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) =>
    gaussianShift δ f (z.1.1,z.1.2.1)*gaussianShift δ f (z.1.1,z.1.2.2)
  let W := fun z : (X × (Velocity × Velocity)) × Sphere =>
    ENNReal.ofReal (windowKernel N z*rateMultiplier N f z)
  let w := fun (δ : ℝ) (z : (X × (Velocity × Velocity)) × Sphere) =>
    ENNReal.ofReal (windowKernel N z*rateMultiplier N (gaussianShift δ f) z)
  have hbm (δ : ℝ) : Measurable (b δ) :=
    ((gaussianShift_measurable δ hfm).comp (measurable_fst.fst.prodMk measurable_fst.snd.fst)).mul
      ((gaussianShift_measurable δ hfm).comp (measurable_fst.fst.prodMk measurable_fst.snd.snd))
  have ham (δ : ℝ) : Measurable (a δ) := (hbm δ).comp scatterTriple_measurable
  have hwm (δ : ℝ) : Measurable (w δ) :=
    ((windowKernel_measurable N).mul (rateMultiplier_measurable N (gaussianShift_measurable δ hfm))).ennreal_ofReal
  have hprod := lintegral_varying_production_le_liminf (μ := ν) (l := 𝓝[>] (0:ℝ))
    ham hbm hwm (A := A) (B := B) (W := W)
    (Filter.Eventually.of_forall (fun _ => mul_nonneg (hf _) (hf _)))
    (Filter.Eventually.of_forall (fun _ => mul_nonneg (hf _) (hf _)))
    (Filter.Eventually.of_forall (fun _ => ⟨(gaussianShift_tendsto f _).mul (gaussianShift_tendsto f _),
      (gaussianShift_tendsto f _).mul (gaussianShift_tendsto f _)⟩))
    (Filter.Eventually.of_forall (fun z => ENNReal.tendsto_ofReal
      ((rateMultiplier_tendsto hN hf (gaussianShift_tendsto f) z).const_mul (windowKernel N z)))) (by
      filter_upwards [] with z
      have hp (p : X × Velocity) : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < gaussianShift δ f p := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact gaussianShift_pos hδ hf p
      exact ⟨((hp _).and (hp _)).mono (fun _ h => mul_pos h.1 h.2),
        ((hp _).and (hp _)).mono (fun _ h => mul_pos h.1 h.2)⟩)
  have hi : (∫⁻ z, extendedProduction N f z ∂ν) ≤
      liminf (fun δ : ℝ => ∫⁻ z, extendedProduction N (gaussianShift δ f) z ∂ν) (𝓝[>] 0) := hprod
  have hm := ENNReal.le_liminf_mul (u := fun _ : ℝ => (4:ℝ≥0∞)⁻¹)
    (v := fun δ => ∫⁻ z, extendedProduction N (gaussianShift δ f) z ∂ν) (f := 𝓝[>] (0:ℝ))
  change (4:ℝ≥0∞)⁻¹*(∫⁻ z, extendedProduction N f z ∂ν) ≤
    liminf (fun δ : ℝ => (4:ℝ≥0∞)⁻¹*∫⁻ z, extendedProduction N (gaussianShift δ f) z ∂ν) (𝓝[>] 0)
  exact (mul_le_mul_right hi (4:ℝ≥0∞)⁻¹).trans (by
    simpa only [liminf_const,Pi.mul_def] using hm)

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

theorem BoundedCutoffSolution.kinetic_entropy_balance (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) {t δ : ℝ} (ht : t ∈ Icc 0 T)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ p, Real.log (gaussianShift δ S.kineticProfile p/maxwellian p.2)*
      collisionOperator N S.kineticProfile p
      ∂((volume.restrict (Icc 0 t)).prod (volume : Measure Position)).prod volume) =
    (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p)))-
      (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)) := by
  have he := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 t))).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun z : ℝ × Phase => Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z)
  have hi := (S.integrated_entropy_balance hN hT ht hδ hδ1).symm
  rw [← he] at hi
  have hc (p : (ℝ × Position) × Velocity) : collisionOperator N S.kineticProfile p =
      S.collision (p.1.1,(p.1.2,p.2)) := S.kinetic_collision p
  simp only [hc,kineticProfile,gaussianShift]
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  congr 1

theorem BoundedCutoffSolution.extended_dissipation_le (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    extendedDissipation ((volume.restrict (Icc 0 t)).prod (volume : Measure Position)) N S.kineticProfile ≤
      ENNReal.ofReal ((∫ p, scalarRelativeEntropy (maxwellian p.2) (f₀ p))-
        (∫ p, scalarRelativeEntropy (maxwellian p.2) (S.density (t,p)))) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 t)).prod volume
  obtain ⟨B,hSb⟩ := S.bounded
  have hB : 0 ≤ B := (S.nonnegative (0,0)).trans (hSb (0,0))
  have hf : ∀ p, 0 ≤ S.kineticProfile p := fun p => S.nonnegative _
  have h0 := S.endpoint_entropy_tendsto 0
  simp only [S.initial hT] at h0
  have hlim := ((entropy_error_tendsto μ N B).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)).sub ((S.endpoint_entropy_tendsto t).sub h0)
  have hu : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      extendedDissipation μ N (gaussianShift δ S.kineticProfile) ≤
      ENNReal.ofReal (entropyErrorCoefficient μ N*δ*(|Real.log δ|+logRegularizationConstant N B)-
        ((∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p)))-
          (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)))) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hδ
    have hp := gaussian_entropy_dissipation_bound (μ := μ) hN hB hδ.1 hδ.2.le
      S.kineticProfile_measurable hf (fun p => hSb _)
    rw [S.kinetic_entropy_balance hN hT ht hδ.1 hδ.2.le] at hp
    have hlog := fun (p : (ℝ × Position) × Velocity) (hp : ‖p.2‖ ≤ N) =>
      log_regularization_bound hN.le hB hδ.1 hδ.2.le (hf p) (hSb _) p.2 hp
    have hpi := (positiveProduction_identity (μ := μ) hN
      (gaussianShift_measurable δ S.kineticProfile_measurable) (gaussianShift_pos hδ.1 hf) hlog).1
    rw [← ofReal_integral_positiveProduction hN.le _ (gaussianShift_pos hδ.1 hf) hpi]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hupper := liminf_le_liminf hu
  rw [(ENNReal.tendsto_ofReal hlim).liminf_eq] at hupper
  have hlower := extendedDissipation_gaussian_le_liminf μ hN S.kineticProfile_measurable hf
  exact (hlower.trans hupper).trans_eq (by congr 1; ring)

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

section

/-! # Uniform integrability of both normalized sources of actual periodic solutions -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_dissipation_bound (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) {n : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (hTN : T ≤ (n:ℝ)+1) :
    extendedDissipation ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) ((n:ℝ)+1)
      (approximatingSolution f hfm n).kineticProfile ≤ ENNReal.ofReal (initialEntropyBudget f) := by
  have hd := (approximatingSolution f hfm n).extended_dissipation_le (by positivity) (by positivity) ⟨hT,hTN⟩
  apply hd.trans (ENNReal.ofReal_le_ofReal ?_)
  have hN : 1 ≤ (n:ℝ)+1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hIni := initialApproximation_relativeEntropy_le hN hfm hf hi
  change relativeEntropy (initialApproximation ((n:ℝ)+1) f) ≤ initialEntropyBudget f at hIni
  have hEnd := relativeEntropy_nonneg ((approximatingSolution f hfm n).finiteEntropy (by positivity) T)
  have he0 : (∫ p, scalarRelativeEntropy (maxwellian p.2) (initialApproximation ((n:ℝ)+1) f p)) =
      relativeEntropy (initialApproximation ((n:ℝ)+1) f) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)
  have he1 : (∫ p, scalarRelativeEntropy (maxwellian p.2) ((approximatingSolution f hfm n).density (T,p))) =
      relativeEntropy (fun p => (approximatingSolution f hfm n).density (T,p)) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)
  rw [he0,he1]
  linarith

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual finite approximations retain entropy and all earlier dissipation -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {X : Type*} [MeasurableSpace X]

theorem extendedDissipation_mono_measure {μ ν : Measure X} (h : μ ≤ ν)
    (N : ℝ) (f : X × Velocity → ℝ) : extendedDissipation μ N f ≤ extendedDissipation ν N f := by
  unfold extendedDissipation
  apply mul_le_mul' le_rfl
  exact lintegral_mono' (Measure.prod_mono (Measure.prod_mono h le_rfl) le_rfl) le_rfl

theorem BoundedCutoffSolution.earlier_joint_budget {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) (hT : 0 ≤ T)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T) :
    ENNReal.ofReal (relativeEntropy (fun p => S.density (t,p)))+
      extendedDissipation ((volume.restrict (Icc 0 r)).prod (volume : Measure Position)) N S.kineticProfile ≤
        ENNReal.ofReal (relativeEntropy f₀) := by
  have htt : t ∈ Icc 0 T := ⟨hr.trans hrt,ht⟩
  have hH := S.relativeEntropy_le hN hT htt
  have hHn := relativeEntropy_nonneg (S.finiteEntropy hN.le t)
  have hd := S.extended_dissipation_le hN hT htt
  have he (u : Density) : (∫ p, scalarRelativeEntropy (maxwellian p.2) (u p)) = relativeEntropy u := by
    apply integral_congr_ae
    exact ae_of_all _ (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)
  rw [he,he] at hd
  have hm := extendedDissipation_mono_measure
    (μ := (volume.restrict (Icc 0 r)).prod (volume : Measure Position))
    (ν := (volume.restrict (Icc 0 t)).prod (volume : Measure Position))
    (Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc le_rfl hrt) le_rfl) le_rfl)
    N S.kineticProfile
  apply (add_le_add le_rfl (hm.trans hd)).trans_eq
  rw [← ENNReal.ofReal_add hHn (sub_nonneg.mpr hH)]
  congr 1
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RelativeEntropyMarginal
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.EuclideanFlight.sourcePullback_finite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseIncrement_finite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The nonnegative entropy marginal and its finite-entropy interpretation -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem entropyMarginal_measurable {F : ℝ × Phase → ℝ} (hF : Measurable F) :
    Measurable (entropyMarginal F) :=
  (spacetimeRelativeEntropy_measurable hF).ennreal_ofReal.lintegral_prod_right'

theorem scalarRelativeEntropy_integrable {f : Density} (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    Integrable (fun p => scalarRelativeEntropy (maxwellian p.2) (f p)) := by
  apply ((hi.const_mul initialEntropyCoefficient).add integrable_maxwellian_phase).mono'
    (scalarRelativeEntropy_measurable (by unfold maxwellian; fun_prop) hfm).aestronglyMeasurable
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (scalarRelativeEntropy_nonneg (maxwellian_pos p.2) (hf p))]
  exact relativeEntropy_density_bound hf p

theorem entropyMarginal_eq {F : ℝ × Phase → ℝ} (hF : Measurable F) (hFn : ∀ z, 0 ≤ F z)
    (t : ℝ) (hi : Integrable (entropyMoment (fun p => F (t,p)))) :
    entropyMarginal F t = ENNReal.ofReal (relativeEntropy (fun p => F (t,p))) := by
  have hh := scalarRelativeEntropy_integrable (f := fun p => F (t,p))
    (hF.comp (measurable_const.prodMk measurable_id)) (fun p => hFn (t,p)) hi
  rw [entropyMarginal,← ofReal_integral_eq_lintegral_ofReal hh
    (ae_of_all _ (fun p => scalarRelativeEntropy_nonneg (maxwellian_pos p.2) (hFn (t,p))))]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun p => scalarRelativeEntropy_eq (maxwellian_pos p.2) _)

end BoltzmannNonuniqueness.PeriodicApproximation

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

section

/-! # The relative entropy integral is lower semicontinuous in weak L¹ -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem WeakL1Converges.entropy_liminf {f : ℕ → X → ℝ} {g m : X → ℝ}
    (h : WeakL1Converges μ f g) (hfi : ∀ n, Integrable (f n) μ)
    (hfn : ∀ n, 0 ≤ᵐ[μ] f n) (hgn : 0 ≤ᵐ[μ] g)
    (hmm : Measurable m) (hmi : Integrable m μ) (hmp : ∀ᵐ x ∂μ, 0 < m x) :
    (∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (g x)) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (f n x)) ∂μ) atTop := by
  let s : ℕ → X → ℝ := fun n x => boundedEntropyTest n (m x) (g x)
  let d : ℕ → X → ℝ := fun n x => entropyDual (m x) (g x) (s n x)
  have hsm n : Measurable (s n) := measurable_boundedEntropyTest n hmm h.1
  have hsb n x : |s n x| ≤ (n:ℝ) := boundedEntropyTest_bound n (m x) (g x)
  have hdi n : Integrable (d n) μ := integrable_entropyDual hmi h.2.1 (hsm n) (hsb n)
  have hdm n : Measurable (d n) := measurable_entropyDual hmm h.1 (hsm n)
  have hdn n : 0 ≤ᵐ[μ] d n := by
    filter_upwards [hmp,hgn] with x hmx hgx
    exact entropyDual_boundedEntropyTest_nonneg n hmx hgx
  have hbound n : ENNReal.ofReal (∫ x, d n x ∂μ) ≤
      liminf (fun k => ∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (f k x)) ∂μ) atTop := by
    have hcorr := (integrable_entropyDual hmi h.2.1 (hsm n) (hsb n))
    have hc : Integrable (fun x => m x*(Real.exp (s n x)-1)) μ := by
      have hi := (h.2.1.bdd_mul (hsm n).aestronglyMeasurable (ae_of_all μ (hsb n))).sub hcorr
      convert hi using 1
      all_goals try with_reducible_and_instances rfl
      funext x
      dsimp [entropyDual]
      ring
    have he (u : X → ℝ) (hui : Integrable u μ) :
        (∫ x, entropyDual (m x) (u x) (s n x) ∂μ) =
          (∫ x, s n x*u x ∂μ)-(∫ x, m x*(Real.exp (s n x)-1) ∂μ) := by
      simpa only [entropyDual,mul_comm,Pi.sub_def] using integral_sub
        (hui.bdd_mul (hsm n).aestronglyMeasurable (ae_of_all μ (hsb n))) hc
    have ht : Tendsto (fun k => ∫ x, entropyDual (m x) (f k x) (s n x) ∂μ)
        atTop (𝓝 (∫ x, d n x ∂μ)) := by
      simp only [he _ (hfi _),show (∫ x, d n x ∂μ) = _ from he g h.2.1]
      exact (h.2.2 (s n) (hsm n) ⟨n,hsb n⟩).sub_const _
    rw [← (ENNReal.tendsto_ofReal ht).liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall (fun k =>
      (ofReal_integral_le_lintegral (integrable_entropyDual hmi (hfi k) (hsm n) (hsb n))).trans
        (lintegral_mono_ae (by
          filter_upwards [hmp,hfn k] with x hmx hfx
          exact ENNReal.ofReal_le_ofReal (entropyDual_le hmx hfx _)))))
  have hfatou : (∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (g x)) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (d n x) ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (d n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hmp,hgn] with x hmx hgx
        exact (ENNReal.tendsto_ofReal (entropyDual_boundedEntropyTest_tendsto hmx hgx)).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le (fun n => (hdm n).ennreal_ofReal)
  refine hfatou.trans ?_
  exact liminf_le_of_frequently_le ((Eventually.of_forall (fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hdi n) (hdn n)]
    exact hbound n)).frequently)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak lower semicontinuity of the time-integrated physical entropy marginal -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {μ : Measure ℝ} [IsFiniteMeasure μ]

theorem entropyMarginal_liminf {F : ℕ → ℝ × Phase → ℝ} {G : ℝ × Phase → ℝ}
    (hw : Published.WeakL1Converges (μ.prod volume) F G)
    (hFm : ∀ n, Measurable (F n)) (hFi : ∀ n, Integrable (F n) (μ.prod volume))
    (hFn : ∀ n z, 0 ≤ F n z) (hGn : ∀ z, 0 ≤ G z) :
    (∫⁻ t, entropyMarginal G t ∂μ) ≤
      liminf (fun n => ∫⁻ t, entropyMarginal (F n) t ∂μ) atTop := by
  have h := hw.entropy_liminf hFi (fun n => ae_of_all _ (hFn n)) (ae_of_all _ hGn)
    (by unfold maxwellian; fun_prop) (integrable_maxwellian_phase.comp_snd μ)
    (ae_of_all _ (fun z => maxwellian_pos z.2.2))
  have he (f : ℝ × Phase → ℝ) (hfm : Measurable f) :
      (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2.2) (f z)) ∂μ.prod volume) =
        ∫⁻ t, entropyMarginal f t ∂μ :=
    lintegral_prod _ (spacetimeRelativeEntropy_measurable hfm).ennreal_ofReal.aemeasurable
  simpa only [he G hw.1,he _ (hFm _)] using h

end BoltzmannNonuniqueness.PeriodicApproximation

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ExtendedProductionScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Homogeneity of the extended entropy production, including its infinite cases -/

noncomputable section

open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem extendedEntropyProduction_scale {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    extendedEntropyProduction (c*a) (c*b) = ENNReal.ofReal c*extendedEntropyProduction a b := by
  by_cases hcz : c = 0
  · subst c
    simp [extendedEntropyProduction]
  have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hcz)
  have hcn : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hcp)
  by_cases haz : a = 0
  · subst a
    by_cases hbz : b = 0
    · subst b
      simp [extendedEntropyProduction]
    · have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
      simp [extendedEntropyProduction,hbz,(mul_pos hcp hbp).ne',hcn]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  by_cases hbz : b = 0
  · subst b
    simp [extendedEntropyProduction,haz,(mul_pos hcp hap).ne',hcn]
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
  have hcap := mul_pos hcp hap
  have hcbp := mul_pos hcp hbp
  simp only [extendedEntropyProduction,hap,hbp,hcap,hcbp,haz,hbz,hcap.ne',hcbp.ne',
    and_self,↓reduceIte]
  have hdiv : c*a/(c*b) = a/b := by field_simp
  rw [hdiv,← ENNReal.ofReal_mul hc]
  congr 1
  ring

end BoltzmannNonuniqueness

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_EntropyDissipationCoordinates
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The collision-rate dissipation is the physical entropy dissipation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

local instance instSFiniteProdVelocityElemSphereProdVolumeSphereArea : SFinite ((volume : Measure BoltzmannNonuniqueness.Velocity).prod
    BoltzmannNonuniqueness.sphereArea) := Measure.prod.instSFinite

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

theorem kernelEntropyProduction_measurable {f : X × Velocity → ℝ} (hf : Measurable f) :
    Measurable (kernelEntropyProduction f) := by
  have hpost : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      f (p.1,scatterLeft p.2.1 p.2.2.1 p.2.2.2)*
        f (p.1,scatterRight p.2.1 p.2.2.1 p.2.2.2)) := by
    unfold scatterLeft scatterRight normalComponent
    fun_prop
  have hpre : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      f (p.1,p.2.1)*f (p.1,p.2.2.1)) := by fun_prop
  have hK : Measurable (fun p : X × (Velocity × (Velocity × Sphere)) =>
      collisionKernel p.2.1 p.2.2.1 p.2.2.2) := by
    unfold collisionKernel normalComponent
    fun_prop
  exact hK.ennreal_ofReal.mul (measurable_extendedEntropyProduction hpost hpre)

theorem collisionEntropyGrouping_measurePreserving (μ : Measure X) [SFinite μ] :
    MeasurePreserving (collisionEntropyGrouping (X := X))
      ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (μ.prod ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea))) :=
  (measurePreserving_prodAssoc μ (volume : Measure Velocity)
    ((volume : Measure Velocity).prod sphereArea)).comp (collisionGrouping_measurePreserving μ)

theorem rateProduction_eq_kernel {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    extendedEntropyProduction (postRate f z) (preRate f z) =
      kernelEntropyProduction f (collisionEntropyGrouping z) := by
  rw [postRate_formula]
  change extendedEntropyProduction
    (collisionKernel z.1.2.1 z.1.2.2 z.2*f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*
      f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
    (collisionKernel z.1.2.1 z.1.2.2 z.2*f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2)) =
    ENNReal.ofReal (collisionKernel z.1.2.1 z.1.2.2 z.2)*extendedEntropyProduction
      (f (z.1.1,scatterLeft z.1.2.1 z.1.2.2 z.2)*f (z.1.1,scatterRight z.1.2.1 z.1.2.2 z.2))
      (f (z.1.1,z.1.2.1)*f (z.1.1,z.1.2.2))
  simpa only [mul_assoc] using
    extendedEntropyProduction_scale (collisionKernel_nonneg z.1.2.1 z.1.2.2 z.2)
      (mul_nonneg (hf _) (hf _)) (mul_nonneg (hf _) (hf _))

theorem rateDissipation_eq_kernel {μ : Measure X} [SFinite μ]
    {f : X × Velocity → ℝ} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) :
    rateDissipation μ f = (4:ℝ≥0∞)⁻¹ * ∫⁻ p, kernelEntropyProduction f p
      ∂μ.prod ((volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)) := by
  unfold rateDissipation
  simp_rw [rateProduction_eq_kernel hf]
  rw [(collisionEntropyGrouping_measurePreserving μ).lintegral_comp
    (kernelEntropyProduction_measurable hfm)]

theorem rateDissipation_congr {μ : Measure X} [SFinite μ] {f g : X × Velocity → ℝ}
    (hfm : Measurable f) (hgm : Measurable g) (he : f =ᵐ[μ.prod volume] g) :
    rateDissipation μ f = rateDissipation μ g := by
  unfold rateDissipation
  congr 1
  apply lintegral_congr_ae
  filter_upwards [postRate_congr hfm hgm he,preRate_congr hfm hgm he] with z hp hq
  rw [hp,hq]

end BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness

theorem kineticDensity_rateDissipation {F : Evolution}
    (hFm : Measurable (fun p : ℝ × Phase => F p.1 p.2))
    (hFn : ∀ t z, 0 ≤ F t z) (T : ℝ) :
    CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume T) (kineticDensity F) =
      ∫⁻ t in Icc (0:ℝ) T, entropyDissipation (F t) := by
  have hkin : Measurable (kineticDensity F) := hFm.comp MeasurableEquiv.prodAssoc.measurable
  rw [CollisionCompactness.rateDissipation_eq_kernel hkin (fun p => hFn _ _)]
  let ν := (volume : Measure Velocity).prod ((volume : Measure Velocity).prod sphereArea)
  let G : ℝ × (Position × (Velocity × (Velocity × Sphere))) → ℝ≥0∞ :=
    fun p => CollisionCompactness.kernelEntropyProduction (F p.1) p.2
  have hG : Measurable G := by
    have hm := CollisionCompactness.kernelEntropyProduction_measurable hkin
    change Measurable (fun p : ℝ × (Position × (Velocity × (Velocity × Sphere))) =>
      CollisionCompactness.kernelEntropyProduction (kineticDensity F) ((p.1,p.2.1),p.2.2))
    exact hm.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  have he := (measurePreserving_prodAssoc (volume.restrict (Icc (0:ℝ) T))
    (volume : Measure Position) ν).lintegral_comp hG
  change (4:ℝ≥0∞)⁻¹ * ∫⁻ p, G (MeasurableEquiv.prodAssoc p)
    ∂((volume.restrict (Icc (0:ℝ) T)).prod (volume : Measure Position)).prod ν = _
  rw [he,lintegral_prod _ hG.aemeasurable]
  rw [← lintegral_const_mul' _ _ (by norm_num : (4:ℝ≥0∞)⁻¹ ≠ ⊤)]
  rfl

end BoltzmannNonuniqueness

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Compactness_PhysicalDissipationBridge
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Physical dissipation depends only on the spacetime density class -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness

theorem physical_dissipation_eq_rate {F : Evolution}
    {g : (ℝ × Position) × Velocity → ℝ} {T : ℝ}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2)) (hFn : ∀ t p, 0 ≤ F t p)
    (hgm : Measurable g)
    (he : ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase),
      F z.1 z.2 = g ((z.1,z.2.1),z.2.2)) :
    (∫⁻ t in Icc (0:ℝ) T, entropyDissipation (F t)) =
      CollisionCompactness.rateDissipation
        ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) g := by
  have hkin : Measurable (kineticDensity F) := hFm.comp MeasurableEquiv.prodAssoc.measurable
  have hekin : kineticDensity F =ᵐ[
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume)] g :=
    (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae he
  rw [← kineticDensity_rateDissipation hFm hFn T]
  exact CollisionCompactness.rateDissipation_congr hkin hgm hekin

end BoltzmannNonuniqueness

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_ClippedProductionLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! # Bounded restoration of spatial mass preserves the dissipation bound -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem extendedProduction_eq_regularized_rates {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    extendedProduction N f z =
      extendedEntropyProduction (regularizedPostRate N f z) (regularizedPreRate N f z) := by
  rw [regularizedPostRate_factor,regularizedPreRate_factor]
  symm
  simpa only [extendedProduction,mul_assoc] using extendedEntropyProduction_scale
    (mul_nonneg (windowKernel_bounds hN.le z).1 (rateMultiplier_bounds hN hf z).1)
    (mul_nonneg (hf _) (hf _)) (mul_nonneg (hf _) (hf _))

omit [MeasurableSpace X] in
theorem collisionMassClip_ratio_bounds {K : ℝ} (hK : 0 ≤ K)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ collisionMassClip K f z/(1+fiberMass volume f z.1.1) ∧
      collisionMassClip K f z/(1+fiberMass volume f z.1.1) ≤ 1 := by
  have hr : 0 ≤ fiberMass volume f z.1.1 := integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hf (z.1.1,v))
  have hd : 0 < 1+fiberMass volume f z.1.1 := by linarith
  exact ⟨div_nonneg (massClip_bounds hK hr).1 hd.le,
    (div_le_one hd).mpr (min_le_right _ _)⟩

omit [MeasurableSpace X] in
theorem clipped_regularizedProduction_le {K N : ℝ} (hK : 0 ≤ K) (hN : 0 < N)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    extendedEntropyProduction
      (collisionMassClip K f z*massRegularizedPostRate N f z)
      (collisionMassClip K f z*massRegularizedPreRate N f z) ≤ extendedProduction N f z := by
  have hc := collisionMassClip_ratio_bounds hK hf z
  have hp : 0 ≤ regularizedPostRate N f z := (regularizedPreRate_bounds hN hf (scatterTriple z)).1
  have hq := (regularizedPreRate_bounds hN hf z).1
  have he : extendedEntropyProduction
      (collisionMassClip K f z*massRegularizedPostRate N f z)
      (collisionMassClip K f z*massRegularizedPreRate N f z) =
      ENNReal.ofReal (collisionMassClip K f z/(1+fiberMass volume f z.1.1))*
        extendedProduction N f z := by
    rw [extendedProduction_eq_regularized_rates hN hf]
    convert extendedEntropyProduction_scale hc.1 hp hq using 1
    all_goals try with_reducible_and_instances rfl
    simp only [massRegularizedPostRate,massRegularizedPreRate]
    congr 1 <;> ring
  rw [he]
  have hcle : ENNReal.ofReal (collisionMassClip K f z/(1+fiberMass volume f z.1.1)) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hc.2
  exact (mul_le_mul' hcle (le_refl (extendedProduction N f z))).trans_eq (one_mul _)

omit [MeasurableSpace X] in
theorem collisionMassClip_eventually_full {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    ∀ᶠ k : ℕ in atTop,
      collisionMassClip (k:ℝ) f z*massNormalizedPreRate f z = preRate f z ∧
      collisionMassClip (k:ℝ) f z*massNormalizedPostRate f z = postRate f z := by
  have hr : 0 ≤ fiberMass volume f z.1.1 := integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hf (z.1.1,v))
  have hd : 1+fiberMass volume f z.1.1 ≠ 0 := by linarith
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (1+fiberMass volume f z.1.1))] with k hk
  simp only [collisionMassClip,massClip,min_eq_right hk,massNormalizedPreRate,massNormalizedPostRate]
  constructor <;> field_simp

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

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

section

/-! # Lower semicontinuity of dissipation with a bounded spatial-mass restoration -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem clipped_production_liminf
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
    (∫⁻ z in collisionWindow R, extendedEntropyProduction
      (collisionMassClip K g z*massNormalizedPostRate g z)
      (collisionMassClip K g z*massNormalizedPreRate g z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
    liminf (fun n => ∫⁻ z, extendedProduction (N n) (f n) z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) atTop := by
  let ν := ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)
  have hw := weak_clipped_collision_rates hfm hgm hf hg hi hb hN hm hp hq K hR
  have hcb n z : |collisionMassClip K (f n) z| ≤ K := by
    have h := massClip_bounds K.coe_nonneg (integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hf n (z.1.1,v)))
    exact (abs_of_nonneg h.1).trans_le h.2
  have hpi n : Integrable (fun z => collisionMassClip K (f n) z*massRegularizedPreRate (N n) (f n) z) ν :=
    (memLp_one_iff_integrable.mp
      ((massRegularizedPreRate_window_uniformIntegrable hfm hf hi hb hN hR).memLp n)).bdd_mul
        (collisionMassClip_measurable K (hfm n)).aestronglyMeasurable (ae_of_all _ (hcb n))
  have hqi n : Integrable (fun z => collisionMassClip K (f n) z*massRegularizedPostRate (N n) (f n) z) ν :=
    (memLp_one_iff_integrable.mp
      ((massRegularizedPostRate_window_uniformIntegrable hfm hf hi hb hN hR).memLp n)).bdd_mul
        (collisionMassClip_measurable K (hfm n)).aestronglyMeasurable (ae_of_all _ (hcb n))
  have hgn z : 0 ≤ collisionMassClip K g z :=
    (massClip_bounds K.coe_nonneg (integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hg (z.1.1,v)))).1
  have hd (z : (X × (Velocity × Velocity)) × Sphere) : 0 ≤ 1+fiberMass volume g z.1.1 := by
    have h : 0 ≤ fiberMass volume g z.1.1 := integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hg (z.1.1,v))
    linarith
  have hl := Published.weak_production_liminf hw.2 hw.1 hqi hpi
    (ae_of_all ν (fun z => mul_nonneg (hgn z) (div_nonneg (preRate_nonneg hg (scatterTriple z)) (hd z))))
    (ae_of_all ν (fun z => mul_nonneg (hgn z) (div_nonneg (preRate_nonneg hg z) (hd z))))
  exact hl.trans (liminf_le_liminf (Eventually.of_forall (fun n =>
    (lintegral_mono (clipped_regularizedProduction_le K.coe_nonneg (hN n) (hf n))).trans
      (setLIntegral_le_lintegral _ _))))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_DissipationMassExhaustion
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the mass cap and the collision window from entropy production -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

omit [MeasurableSpace X] in
theorem eventually_mem_collisionWindow (z : (X × (Velocity × Velocity)) × Sphere) :
    ∀ᶠ n : ℕ in atTop, z ∈ collisionWindow (n:ℝ) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (‖z.1.2.1‖+‖z.1.2.2‖))] with n hn
  change ‖z.1.2.1‖^2+‖z.1.2.2‖^2 ≤ (n:ℝ)^2
  nlinarith [norm_nonneg z.1.2.1,norm_nonneg z.1.2.2,
    mul_nonneg (norm_nonneg z.1.2.1) (norm_nonneg z.1.2.2)]

theorem production_le_of_clipped_windows {g : X × Velocity → ℝ}
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p) {L : ℝ≥0∞}
    (h : ∀ (K : ℝ≥0) (R : ℝ), 0 ≤ R →
      (∫⁻ z in collisionWindow R, extendedEntropyProduction
        (collisionMassClip K g z*massNormalizedPostRate g z)
        (collisionMassClip K g z*massNormalizedPreRate g z)
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤ L) :
    (∫⁻ z, extendedEntropyProduction (postRate g z) (preRate g z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤ L := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let P := fun z : (X × (Velocity × Velocity)) × Sphere =>
    extendedEntropyProduction (postRate g z) (preRate g z)
  have hPm : Measurable P := measurable_extendedEntropyProduction
    ((preRate_measurable hgm).comp scatterTriple_measurable) (preRate_measurable hgm)
  have hw (R : ℝ) (hR : 0 ≤ R) : (∫⁻ z in collisionWindow R, P z ∂ν) ≤ L := by
    let p (k : ℕ) (z : (X × (Velocity × Velocity)) × Sphere) :=
      extendedEntropyProduction
        (collisionMassClip (k:ℝ) g z*massNormalizedPostRate g z)
        (collisionMassClip (k:ℝ) g z*massNormalizedPreRate g z)
    have hpm k : Measurable (p k) := measurable_extendedEntropyProduction
      ((collisionMassClip_measurable k hgm).mul (massNormalizedPostRate_measurable hgm))
      ((collisionMassClip_measurable k hgm).mul (massNormalizedPreRate_measurable hgm))
    have ht z : Tendsto (fun k => p k z) atTop (𝓝 (P z)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [collisionMassClip_eventually_full hg z] with k hk
      simp only [p,hk.1,hk.2,P]
    calc
      _ = ∫⁻ z in collisionWindow R, liminf (fun k => p k z) atTop ∂ν :=
        lintegral_congr (fun z => (ht z).liminf_eq.symm)
      _ ≤ liminf (fun k => ∫⁻ z in collisionWindow R, p k z ∂ν) atTop :=
        lintegral_liminf_le (fun k => hpm k)
      _ ≤ L := liminf_le_of_frequently_le
        (Eventually.of_forall (fun (k : ℕ) => h (k:ℝ≥0) R hR)).frequently
  have ht z : Tendsto (fun n : ℕ => (collisionWindow (n:ℝ)).indicator P z) atTop (𝓝 (P z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_mem_collisionWindow z] with n hn
    exact (indicator_of_mem hn P).symm
  calc
    _ = ∫⁻ z, liminf (fun n : ℕ => (collisionWindow (n:ℝ)).indicator P z) atTop ∂ν :=
      lintegral_congr (fun z => (ht z).liminf_eq.symm)
    _ ≤ liminf (fun n : ℕ => ∫⁻ z, (collisionWindow (n:ℝ)).indicator P z ∂ν) atTop :=
      lintegral_liminf_le (fun n => hPm.indicator (collisionWindow_measurable n))
    _ ≤ L := liminf_le_of_frequently_le ((Eventually.of_forall (fun (n : ℕ) => by
      rw [lintegral_indicator (collisionWindow_measurable n)]
      exact hw n (Nat.cast_nonneg n))).frequently)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end OAI
end

section
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_FullDissipationLimit
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full physical dissipation survives the finite periodic approximations -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem full_dissipation_le_liminf
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
    : rateDissipation μ g ≤ liminf (fun n => extendedDissipation μ (N n) (f n)) atTop := by
  have h := production_le_of_clipped_windows hgm hg
    (fun K R hR => clipped_production_liminf hfm hgm hf hg hi hb hN hm hp hq K hR)
  have hl := ENNReal.le_liminf_mul (u := fun _ : ℕ => (4:ℝ≥0∞)⁻¹)
    (v := fun n => ∫⁻ z, extendedProduction (N n) (f n) z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) (f := atTop)
  exact (mul_le_mul' (le_refl (4:ℝ≥0∞)⁻¹) h).trans (by
    simpa only [liminf_const,Pi.mul_def,extendedDissipation] using hl)

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

section

/-! # Full physical dissipation of the actual global periodic weak limit -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalWeakLimit.physical_dissipation_le_liminf
    {f : Density} {hfm : Measurable f} (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (_hT : 0 ≤ T)
    (hm : Tendsto (fun n => eLpNorm (fun x =>
      fiberMass volume (approximatingSolution f hfm (G.indices n)).kineticProfile x-
      fiberMass volume G.kineticProfile x) 1
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0))
    (hc :       Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPreRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPreRate G.kineticProfile) ∧
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPostRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPostRate G.kineticProfile)) :
    rateDissipation ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) G.kineticProfile ≤
      liminf (fun n => extendedDissipation
        ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) ((G.indices n:ℝ)+1)
        (approximatingSolution f hfm (G.indices n)).kineticProfile) atTop := by
  exact full_dissipation_le_liminf
    (fun n => (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)
    G.kineticProfile_measurable
    (fun n _ => (approximatingSolution f hfm (G.indices n)).nonnegative _)
    (fun _ => G.nonnegative _)
    (fun n => (approximatingSolution f hfm (G.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _))
    (fun n => (approximatingSolution f hfm (G.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _))
    (fun _ => by positivity) hm hc.1 hc.2

theorem GlobalWeakLimit.physical_dissipation_bound
    {f : Density} {hfm : Measurable f} (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T)
    (hm : Tendsto (fun n => eLpNorm (fun x =>
      fiberMass volume (approximatingSolution f hfm (G.indices n)).kineticProfile x-
      fiberMass volume G.kineticProfile x) 1
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0))
    (hc :       Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPreRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPreRate G.kineticProfile) ∧
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPostRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPostRate G.kineticProfile)) :
    rateDissipation ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) G.kineticProfile ≤
      ENNReal.ofReal (initialEntropyBudget f) := by
  have hN : Tendsto (fun n => (G.indices n:ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp G.increasing.tendsto_atTop).atTop_add tendsto_const_nhds
  apply (G.physical_dissipation_le_liminf hf hi hT hm hc).trans
  exact liminf_le_of_frequently_le ((hN.eventually (eventually_ge_atTop T)).mono (fun n hn =>
    approximatingSolution_dissipation_bound f hfm hf hi hT hn)).frequently

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # A single global collision limit retains its strong masses and physical rates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalCollisionLimit.dissipation_bound {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    rateDissipation ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) G.weakLimit.kineticProfile ≤
      ENNReal.ofReal (initialEntropyBudget f) :=
  G.weakLimit.physical_dissipation_bound hf hi hT (G.mass_strong T hT) (G.finite_rates T hT)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The sharp joint budget passes to the actual global limit on every time set -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalCollisionLimit.averaged_joint_budget {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) {S : Set ℝ}
    (hS : MeasurableSet S) (hSR : S ⊆ Icc r R) :
    (∫⁻ t in S, entropyMarginal G.weakLimit.density t)+
      volume S*rateDissipation ((volume.restrict (Icc 0 r)).prod (volume : Measure Position))
        G.weakLimit.kineticProfile ≤ volume S*ENNReal.ofReal (relativeEntropy f) := by
  let μ : Measure ℝ := volume.restrict S
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).density
  let D n := extendedDissipation ((volume.restrict (Icc 0 r)).prod (volume : Measure Position))
    ((G.weakLimit.indices n:ℝ)+1) (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let C n := ENNReal.ofReal (relativeEntropy (initialApproximation ((G.weakLimit.indices n:ℝ)+1) f))
  have hR : 0 ≤ R := hr.trans hrR
  have hS0 : S ⊆ Icc 0 R := hSR.trans (Icc_subset_Icc hr le_rfl)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    ((measure_mono hSR).trans_lt isCompact_Icc.measure_lt_top).ne
  have hw := (G.weakLimit.weak_on_window hR).restrict_base hS
  rw [Measure.restrict_restrict hS,inter_eq_left.mpr hS0] at hw
  have hFm n : Measurable (F n) := (approximatingSolution f hfm (G.weakLimit.indices n)).measurable
  have hFi n : Integrable (F n) (μ.prod volume) :=
    density_integrable_of_spacetimeEntropy (hFm n)
      (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative
      (approximatingSolution_spacetimeEntropy_integrable f hfm hf hi _ μ)
  have hh := entropyMarginal_liminf hw hFm hFi
    (fun n => (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative) G.weakLimit.nonnegative
  have hd := G.weakLimit.physical_dissipation_le_liminf hf hi hr
    (G.mass_strong r hr) (G.finite_rates r hr)
  have hC : Tendsto C atTop (𝓝 (ENNReal.ofReal (relativeEntropy f))) :=
    ENNReal.tendsto_ofReal ((initialApproximation_relativeEntropy_tendsto hfm hf hi).comp
      G.weakLimit.increasing.tendsto_atTop)
  have hN : Tendsto (fun n => (G.weakLimit.indices n:ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp G.weakLimit.increasing.tendsto_atTop).atTop_add tendsto_const_nhds
  have hu : ∀ᶠ n in atTop, ∀ᵐ t ∂μ, entropyMarginal (F n) t+D n ≤ C n := by
    filter_upwards [hN.eventually (eventually_ge_atTop R)] with n hn
    filter_upwards [ae_restrict_mem hS] with t ht
    have hnt : t ≤ (G.weakLimit.indices n:ℝ)+1 := (hSR ht).2.trans hn
    rw [entropyMarginal_eq (hFm n)
      (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative t
      ((approximatingSolution f hfm (G.weakLimit.indices n)).finiteEntropy (by positivity) t).2.2]
    exact (approximatingSolution f hfm (G.weakLimit.indices n)).earlier_joint_budget
      (by positivity) (by positivity) hr (hSR ht).1 hnt
  have h := entropy_dissipation_average_limit
    (μ := μ) (fun n => entropyMarginal_measurable (hFm n)) hh hd hC hu
  simpa only [μ,Measure.restrict_apply_univ] using h

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
-- module Solutions.OAIQ080_BZ.Boltzmann_Branching_RateDissipationMonotone
attribute [-instance] _root_.OAI.BoltzmannNonuniqueness.ChartKernel.offAxis_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.characteristicGainKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence.HotLimitExtraction.retainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.copyColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.mainCoreKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCopyDatum.selectedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.dilatedColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.JetCoreSheet.kineticColdKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.awayOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.PositiveIteration.nearOriginKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.beamNormalRetainedKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.dampedCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.densityScaledCharacteristicKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalBeamKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalCollision_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalPhysicalEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.localizedNormalWindowEvent_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.physicalEventMeasure_sFinite _root_.OAI.BoltzmannNonuniqueness.ReferenceGeometry.scaledBeamNormalKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseEndpointKernel_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.phaseSeed_sFinite _root_.OAI.BoltzmannNonuniqueness.WeakTime.residenceKernel_sFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Monotonicity of the nonnegative dissipation in the base measure -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

theorem rateDissipation_mono_measure {μ ν : Measure X} (h : μ ≤ ν)
    (f : X × Velocity → ℝ) : rateDissipation μ f ≤ rateDissipation ν f := by
  unfold rateDissipation
  gcongr

end BoltzmannNonuniqueness.CollisionCompactness

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

section

/-! # A joint bound on every right interval gives an almost-everywhere pointwise bound -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness

theorem ae_bound_of_right_integral_bound {H D : ℝ → ℝ} {B C : ℝ} (hB : 0 ≤ B)
    (hH : IntervalIntegrable H volume 0 B)
    (hbudget : ∀ t s : ℝ, 0 ≤ t → t < s → s ≤ B →
      (∫ r in t..s, H r)+(s-t)*D t ≤ (s-t)*C) :
    ∀ᵐ t ∂volume, t ∈ Ico 0 B → H t+D t ≤ C := by
  filter_upwards [hH.ae_hasDerivAt_integral] with t ht htB
  have htt : t ∈ uIcc 0 B := by simpa only [uIcc_of_le hB] using ⟨htB.1,htB.2.le⟩
  have hd := ht htt t htt
  have hl := hd.tendsto_slope_zero_right.add_const (D t)
  apply le_of_tendsto hl
  filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr htB.2)] with h hh
  have hb := hbudget t (t+h) htB.1 (by linarith [hh.1]) (by linarith [hh.2])
  simp only [intervalIntegral.integral_same,sub_zero,smul_eq_mul]
  change h⁻¹*(∫ r in t..(t+h), H r)+D t ≤ C
  calc
    _ = ((∫ r in t..(t+h), H r)+h*D t)/h := by field_simp [ne_of_gt hh.1]
    _ ≤ C := (div_le_iff₀ hh.1).mpr (by nlinarith only [hb])

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

section

/-! # A fixed nonnegative dissipation budget survives entropy trace limits -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness

theorem scalarEntropy_joint_trace_bound {U : ℝ × Phase → ℝ} (hUm : Measurable U)
    {s : ℕ → ℝ} {t : ℝ} {C d : ℝ≥0∞}
    (hc : ∀ᵐ p ∂(volume : Measure Phase), Tendsto (fun n => U (s n,p)) atTop (𝓝 (U (t,p))))
    (hb : ∀ n, (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (s n,p))))+d ≤ C) :
    (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (t,p))))+d ≤ C := by
  let H n := ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (s n,p)))
  have hmm : Measurable (fun p : Phase => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hum n : Measurable (fun p : Phase => U (s n,p)) :=
    hUm.comp (measurable_const.prodMk measurable_id)
  have hgm n : Measurable (fun p : Phase => scalarRelativeEntropy (maxwellian p.2) (U (s n,p))) :=
    (((hum n).mul (hum n).log).sub ((hum n).mul (measurable_const.add hmm.log))).add hmm
  have hlim : (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2) (U (t,p)))) ≤
      liminf H atTop := by
    calc
      _ = ∫⁻ p : Phase, liminf (fun n => ENNReal.ofReal
          (scalarRelativeEntropy (maxwellian p.2) (U (s n,p)))) atTop := by
        apply lintegral_congr_ae
        filter_upwards [hc] with p hp
        exact (ENNReal.tendsto_ofReal (((BoltzmannNonuniqueness.scalarRelativeEntropy_continuous
          (maxwellian p.2)).tendsto _).comp hp)).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le (fun n => (hgm n).ennreal_ofReal)
  have hadd : liminf H atTop+d ≤ liminf (fun n => H n+d) atTop := by
    simpa only [liminf_const] using ennreal_liminf_add_nat H (fun _ => d)
  exact (add_le_add hlim le_rfl).trans (hadd.trans
    (liminf_le_of_frequently_le (Eventually.of_forall hb).frequently))

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

/-! # A real-valued joint entropy budget on each finite right interval -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalWeakLimit.entropy_path_integrable {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun t => relativeEntropy (fun p => G.density (t,p))) (volume.restrict (Icc 0 T)) := by
  convert (G.entropy_on_window hf hi hT).1.integral_prod_left using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  apply integral_congr_ae
  exact ae_of_all _ (fun p => (scalarRelativeEntropy_eq (maxwellian_pos p.2) _).symm)

theorem GlobalWeakLimit.entropyMarginal_ae_eq {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    entropyMarginal G.density =ᵐ[volume] fun t => ENNReal.ofReal (relativeEntropy (fun p => G.density (t,p))) := by
  filter_upwards [G.finiteEntropy_ae_volume hf hi] with t ht
  exact entropyMarginal_eq G.measurable G.nonnegative t ht.1.2.2

theorem GlobalCollisionLimit.real_joint_interval_budget {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    (∫ t in r..R, relativeEntropy (fun p => G.weakLimit.density (t,p)))+
      (R-r)*(rateDissipation ((volume.restrict (Icc 0 r)).prod (volume : Measure Position))
        G.weakLimit.kineticProfile).toReal ≤ (R-r)*relativeEntropy f := by
  let H t := relativeEntropy (fun p => G.weakLimit.density (t,p))
  let d := rateDissipation ((volume.restrict (Icc 0 r)).prod (volume : Measure Position)) G.weakLimit.kineticProfile
  have hR : 0 ≤ R := hr.trans hrR
  have hI : Integrable H (volume.restrict (Icc r R)) :=
    (G.weakLimit.entropy_path_integrable hf hi hR).mono_measure
      (Measure.restrict_mono (Icc_subset_Icc hr le_rfl) le_rfl)
  have hn : 0 ≤ᵐ[volume.restrict (Icc r R)] H := by
    filter_upwards [ae_restrict_of_ae (G.weakLimit.finiteEntropy_ae_volume hf hi)] with t ht
    exact relativeEntropy_nonneg ht.1
  have hval : (∫⁻ t in Icc r R, entropyMarginal G.weakLimit.density t) =
      ENNReal.ofReal (∫ t in r..R, H t) := by
    rw [lintegral_congr_ae (ae_restrict_of_ae (G.weakLimit.entropyMarginal_ae_eq hf hi)),
      ← ofReal_integral_eq_lintegral_ofReal hI hn,
      integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hrR]
  have hd : d ≠ ⊤ := ne_of_lt ((G.dissipation_bound hf hi hr).trans_lt ENNReal.ofReal_lt_top)
  have hb := G.averaged_joint_budget hf hi hr hrR measurableSet_Icc (Subset.rfl : Icc r R ⊆ Icc r R)
  rw [hval,Real.volume_Icc] at hb
  change ENNReal.ofReal (∫ t in r..R, H t)+ENNReal.ofReal (R-r)*d ≤
    ENNReal.ofReal (R-r)*ENNReal.ofReal (relativeEntropy f) at hb
  rw [← ENNReal.ofReal_toReal hd] at hb
  have hdiff : 0 ≤ R-r := sub_nonneg.mpr hrR
  have hInt : 0 ≤ ∫ t in r..R, H t := by
    rw [intervalIntegral.integral_of_le hrR,← integral_Icc_eq_integral_Ioc]
    exact integral_nonneg_of_ae hn
  have h0 := relativeEntropy_nonneg (show FiniteEntropyDatum f from ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩)
  rw [← ENNReal.ofReal_mul hdiff,← ENNReal.ofReal_mul hdiff,
    ← ENNReal.ofReal_add hInt (mul_nonneg hdiff ENNReal.toReal_nonneg)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hdiff h0)).mp hb

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The sharp joint entropy and physical dissipation bound for the same global limit -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalCollisionLimit.sharp_joint_entropy_dissipation
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      ENNReal.ofReal (relativeEntropy (fun p => G.weakLimit.density (t,p)))+
        rateDissipation ((volume.restrict (Icc 0 t)).prod (volume : Measure Position))
          G.weakLimit.kineticProfile ≤ ENNReal.ofReal (relativeEntropy f) := by
  let H t := relativeEntropy (fun p => G.weakLimit.density (t,p))
  let D t := rateDissipation ((volume.restrict (Icc 0 t)).prod (volume : Measure Position)) G.weakLimit.kineticProfile
  have hlocal (n : ℕ) : ∀ᵐ t ∂volume, t ∈ Ico 0 (n:ℝ) → H t+(D t).toReal ≤ relativeEntropy f := by
    apply ae_bound_of_right_integral_bound (Nat.cast_nonneg n)
      ((intervalIntegrable_iff_integrableOn_Icc_of_le (Nat.cast_nonneg n)).mpr
        (G.weakLimit.entropy_path_integrable hf hi (Nat.cast_nonneg n)))
    intro t s ht hts _hs
    exact G.real_joint_interval_budget hf hi ht hts.le
  have hall : ∀ᵐ t ∂volume, ∀ n : ℕ, t ∈ Ico 0 (n:ℝ) → H t+(D t).toReal ≤ relativeEntropy f :=
    ae_all_iff.mpr hlocal
  filter_upwards [hall,G.weakLimit.finiteEntropy_ae_volume hf hi] with t ht hdata
  intro ht0
  obtain ⟨n,hn⟩ := exists_nat_gt t
  have hreal := ht n ⟨ht0,hn⟩
  have hd : D t ≠ ⊤ := ne_of_lt ((G.dissipation_bound hf hi ht0).trans_lt ENNReal.ofReal_lt_top)
  have hH : 0 ≤ H t := relativeEntropy_nonneg hdata.1
  change ENNReal.ofReal (H t)+D t ≤ _
  rw [← ENNReal.ofReal_toReal hd,← ENNReal.ofReal_add hH ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_le_ofReal hreal

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

/-! # The joint entropy and full earlier dissipation bound at every characteristic time -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalCollisionLimit.linear_joint_entropy_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
        (physicalLinearProfile f G.weakLimit.kineticProfile (t,p))))+
      rateDissipation ((volume.restrict (Icc 0 t)).prod (volume : Measure Position))
        G.weakLimit.kineticProfile ≤ ENNReal.ofReal (relativeEntropy f) := by
  have hh n := Measure.ae_ae_of_ae_prod (G.linear_profile_eq_density_q80 hf hi (Nat.cast_nonneg n))
  simp only [ae_restrict_iff' measurableSet_Icc] at hh
  filter_upwards [ae_all_iff.mpr hh,G.sharp_joint_entropy_dissipation hf hi,
    G.weakLimit.finiteEntropy_ae_volume hf hi] with t he hbound hdata
  intro ht0
  obtain ⟨n,hn⟩ := exists_nat_ge t
  have hslice := he n ⟨ht0,hn⟩
  have hH : (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
      (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)))) =
      ENNReal.ofReal (relativeEntropy (fun p => G.weakLimit.density (t,p))) := by
    calc
      _ = ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
          (G.weakLimit.density (t,TorusFlight.flight t p))) :=
        lintegral_congr_ae (hslice.mono (fun p hp => by rw [hp]))
      _ = ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
          (G.weakLimit.density (t,p))) :=
        TorusFlight.scalar_entropy_lintegral_comp
          (G.weakLimit.measurable.comp (measurable_const.prodMk measurable_id)) t
      _ = _ := (relativeEntropy_eq_lintegral hdata.1).symm
  rw [hH]
  exact hbound ht0

theorem GlobalCollisionLimit.linear_joint_entropy
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
      (physicalLinearProfile f G.weakLimit.kineticProfile (t,p))))+
      rateDissipation ((volume.restrict (Icc 0 t)).prod (volume : Measure Position))
        G.weakLimit.kineticProfile ≤ ENNReal.ofReal (relativeEntropy f) := by
  obtain ⟨s,hs,hst⟩ := exists_right_good_sequence (G.linear_joint_entropy_ae hf hi) t
  have hsm n : s n ∈ Icc 0 (t+1) := by
    have hδ : 1/((n:ℝ)+1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨ht.trans (hs n).1.le,(hs n).2.1.le.trans (add_le_add le_rfl hδ)⟩
  apply scalarEntropy_joint_trace_bound
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable)
    (G.linear_profile_slice_tendsto hf hi (show 0 ≤ t+1 by linarith)
      (show t ∈ Icc 0 (t+1) from ⟨ht,by linarith⟩) hsm hst)
  intro n
  have hD := rateDissipation_mono_measure
    (Measure.prod_mono (Measure.restrict_mono_set (volume : Measure ℝ)
      (show Icc (0:ℝ) t ⊆ Icc 0 (s n) from Icc_subset_Icc_right (hs n).1.le))
      (le_refl (volume : Measure Position))) G.weakLimit.kineticProfile
  apply le_trans (add_le_add le_rfl hD)
  exact (hs n).2.2 (hsm n).1

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

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Every-time joint entropy inequality for the actual physical evolution -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_entropy_dissipation_q80_oai
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (relativeEntropy (physicalEvolution f G.weakLimit.kineticProfile t))+
      (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (physicalEvolution f G.weakLimit.kineticProfile s)) ≤
      ENNReal.ofReal (relativeEntropy f) := by
  let E := physicalEvolution f G.weakLimit.kineticProfile
  have hEm : Measurable (fun z : ℝ × Phase => E z.1 z.2) :=
    physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable
  have hD := physical_dissipation_eq_rate hEm
    (fun _ _ => physicalEvolution_nonneg _ _ _ _)
    G.weakLimit.kineticProfile_measurable (G.physicalEvolution_eq_density hf hi ht)
  rw [hD,relativeEntropy_eq_lintegral (G.physical_finiteEntropy hf hi ht)]
  have he : E t = (fun p => physicalLinearProfile f G.weakLimit.kineticProfile
      (t,TorusFlight.flight (-t) p)) :=
    funext (physicalEvolution_eq (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht)
  dsimp only [E] at he
  have hUm : Measurable (fun p : Phase => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) :=
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      ((measurable_const (a := t)).prodMk measurable_id)
  rw [he,TorusFlight.scalar_entropy_lintegral_comp hUm (-t)]
  exact G.linear_joint_entropy hf hi ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
end

theorem solution : type_of% @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_entropy_dissipation_q80_oai := @OAI.BoltzmannNonuniqueness.PeriodicApproximation.GlobalCollisionLimit.physical_entropy_dissipation_q80_oai
